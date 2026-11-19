import FV.Opt.MidValCond
import FV.Opt.Proof.SimWinU
import FV.Opt.Proof.SemFacts
import FV.Opt.Proof.UnreachableU

/-!
# `g` simulates `condPrep g hints` (#1119 family 3, route D)

`condPrep g hints` (`FV/Opt/MidValCond.lean`) is `g` with, at the end of some blocks whose
terminator is `brif c t e` (`c` below `g.freshValue`), fresh statements `ss` rebuilding a wrapper
chain around `c` (`z = iconst ty 0; x = icmp ne c, z`, `x = uextend c`, …) and the terminator
`brif r t e` on the last of them. Every wrapper keeps the condition's truth (`Wrap.ok`): whenever
the statements evaluate, `r` is non-zero exactly when `c` is (`prepChain_ok`). So `g` simulates
the copy: the copy's original statements are `g`'s, its inserted ones are stuttering steps of
`g` (they write only values from `g.freshValue` on, which `g` never reads: `refsOk`), and both
take the same successor at the `brif`.

* `RunS`, `ChainInv`, `ChainOK`: running pure statements on registers alone (`cfr`), and the
  truth of the last value against `c`'s;
* `prepChain_ok`: the inserted statements of a chain of `Wrap.ok` wrappers;
* `CR`: the frame relation (`g`'s frame in a block of `g`, the copy's in the copied block, the
  same registers below `g.freshValue`, the copy's remaining inserted statements);
* **`condPrep_simU : refsOk g = true → FunSimU (condPrep g hints) g`**.
-/

namespace Opt.MidVal

open Clif Opt

/-! ## Pure statements on registers -/

/-- The instructions of the inserted statements. -/
def chainInst : Inst → Bool
  | .iconst .. | .icmp .. | .extend .. => true
  | _ => false

theorem evalInst_chain_trap {fr : Frame} {m : Mem} {i : Inst} (hi : chainInst i = true)
    (c : TrapCode) : evalInst fr m i ≠ .trap c := by
  cases i <;> simp only [chainInst, Bool.false_eq_true] at hi
  case iconst => simp [evalInst]
  case icmp cc ty x y =>
    simp only [evalInst, Frame.getAs, Frame.get]
    intro h
    cases h1 : fr.regs x <;> simp [h1, Res.ofOption, Res.bind] at h
    rename_i a
    cases h2 : a.as? ty <;> simp [h2, Res.ofOption, Res.bind] at h
    cases h3 : fr.regs y <;> simp [h3, Res.ofOption, Res.bind] at h
    rename_i b
    cases h4 : b.as? ty <;> simp [h4, Res.ofOption, Res.bind, pure] at h
  case extend op ty x =>
    simp only [evalInst, Frame.get]
    intro h
    cases h1 : fr.regs x <;> simp [h1, Res.ofOption, Res.bind] at h
    rename_i a
    by_cases hw : a.ty.width < ty.width <;> cases op <;>
      simp [hw, Res.check, Res.bind, pure] at h

/-- A wrapper instruction reads no memory and leaves it unchanged. -/
theorem evalInst_chain_mem {fr : Frame} {m m' : Mem} {i : Inst} {vals : List Val}
    (hi : chainInst i = true) (h : evalInst fr m i = .ok (vals, m')) :
    m' = m ∧ ∀ m2, evalInst fr m2 i = .ok (vals, m2) := by
  cases i <;> simp only [chainInst, Bool.false_eq_true] at hi
  case iconst ty imm =>
    simp only [evalInst, Res.pure_eq_ok, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => by simp⟩
  case icmp cc ty x y =>
    simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h ⊢
    obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => ⟨a, ha, b, hb, by simp⟩⟩
  case extend op ty x =>
    cases op <;> simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h ⊢ <;>
      obtain ⟨a, ha, u, hu, rfl, rfl⟩ := h <;> exact ⟨rfl, fun _ => ⟨a, ha, u, hu, by simp⟩⟩

/-- Running wrapper statements from the registers `r` in a frame like `T` (its function and
slots; they read no memory). -/
inductive RunS (T : Frame) : Regs → List Stmt → Regs → Prop
  | nil (r : Regs) : RunS T r [] r
  | cons {r r1 r2 : Regs} {st : Stmt} {ss : List Stmt} {vals : List Val} :
      (∀ m, evalInst { T with regs := r } m st.inst = .ok (vals, m)) →
      r.setMany st.results vals = some r1 → RunS T r1 ss r2 → RunS T r (st :: ss) r2

theorem RunS.append {T : Frame} {r r2 : Regs} {ss ss' : List Stmt}
    (h : RunS T r (ss ++ ss') r2) : ∃ r1, RunS T r ss r1 ∧ RunS T r1 ss' r2 := by
  induction ss generalizing r with
  | nil => exact ⟨r, .nil r, h⟩
  | cons st ss ih =>
    cases h with
    | cons he hs hr =>
      obtain ⟨r1, h1, h2⟩ := ih hr
      exact ⟨r1, .cons he hs h1, h2⟩

/-- `RunS` depends on the template only through its globals, externs and slots. -/
theorem RunS.congr {T T' : Frame} (hg : T'.func.globals = T.func.globals)
    (hx : T'.func.externs = T.func.externs) (hs : T'.slots = T.slots) {r r2 : Regs}
    {ss : List Stmt} (h : RunS T r ss r2) : RunS T' r ss r2 := by
  induction h with
  | nil r => exact .nil r
  | @cons r r1 r2 st ss vals he hs' _ ih =>
    refine .cons (fun m => ?_) hs' ih
    exact (evalInst_congr (fr := { T with regs := r }) (fr' := { T' with regs := r }) hg hx hs
      (fun _ _ => rfl)).trans (he m)

/-- Whenever `ss` runs from `r` and its last value `x` is defined, the condition `c` is defined
in `r` with the same truth. -/
def ChainInv (T : Frame) (r : Regs) (ss : List Stmt) (x c : ValueId) : Prop :=
  ∀ rEnd xv, RunS T r ss rEnd → rEnd x = some xv →
    ∃ cv, r c = some cv ∧ Sem.truthy xv.bits = Sem.truthy cv.bits

/-- `ChainInv` in every frame and register file. -/
def ChainOK (ss : List Stmt) (x c : ValueId) : Prop := ∀ T r, ChainInv T r ss x c

/-! ## Truth of the wrappers -/

theorem truthy_bool8 (b : Bool) : Sem.truthy (Sem.bool8 b) = b := by
  cases b <;> decide

theorem zeroExtend_eq_zero {w : Nat} (v : Nat) (hv : w ≤ v) (x : BitVec w) :
    x.zeroExtend v = 0 ↔ x = 0 := by
  constructor
  · intro hz
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat hz
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_zero] at this
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hv))] at this
    simpa using this
  · intro h; subst h; apply BitVec.eq_of_toNat_eq; simp

theorem signExtend_eq_zero {w : Nat} (v : Nat) (hv : w ≤ v) (x : BitVec w) :
    x.signExtend v = 0 ↔ x = 0 := by
  constructor
  · intro hz
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun y => y.getLsbD i) hz
    simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_zero] at this
    simpa [hi, show i < v by omega] using this
  · intro h; subst h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_signExtend]

theorem truthy_zeroExtend {w : Nat} (v : Nat) (hv : w ≤ v) (x : BitVec w) :
    Sem.truthy (x.zeroExtend v) = Sem.truthy x := by
  simp only [Sem.truthy]
  by_cases h : x = 0
  · simp [h, (zeroExtend_eq_zero v hv x).2 h]
  · have h' : x.zeroExtend v ≠ 0 := fun hz => h ((zeroExtend_eq_zero v hv x).1 hz)
    rw [bne_iff_ne.2 h', bne_iff_ne.2 h]

theorem truthy_signExtend {w : Nat} (v : Nat) (hv : w ≤ v) (x : BitVec w) :
    Sem.truthy (x.signExtend v) = Sem.truthy x := by
  simp only [Sem.truthy]
  by_cases h : x = 0
  · subst h; rw [(signExtend_eq_zero v hv 0).2 rfl]; rfl
  · have h' : x.signExtend v ≠ 0 := fun hz => h ((signExtend_eq_zero v hv x).1 hz)
    rw [bne_iff_ne.2 h', bne_iff_ne.2 h]

theorem ult_zero_left {w : Nat} (a : BitVec w) : (0#w).ult a = Sem.truthy a := by
  have e : (0#w).ult a = decide (0 < a.toNat) := by simp [BitVec.ult]
  rw [e, Sem.truthy]
  by_cases h : a = 0
  · subst h; simp
  · have h0 : a.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))
    rw [bne_iff_ne.2 h]
    simpa using Nat.pos_of_ne_zero h0

/-- The truth of a `Wrap.ok` comparison of `a` with `0`. -/
theorem truthy_icmp_zero {cc : IntCC} {ty : Ty} {zl : Bool} (hok : (Wrap.icmp cc ty zl).ok = true)
    (a : BitVec ty.width) :
    Sem.truthy (Sem.icmp cc (if zl then 0 else a) (if zl then a else 0)) = Sem.truthy a := by
  simp only [Sem.icmp, truthy_bool8]
  cases cc <;> cases zl <;> simp only [Wrap.ok, Bool.false_eq_true] at hok <;>
    simp only [Sem.intcc, ite_true, ite_false, Bool.false_eq_true] <;>
    first
      | exact ult_zero_left a
      | simp [Sem.truthy, bne_comm]

/-- Composition: a chain around `t` after statements taking `y` to `t`. -/
theorem ChainOK.comp {s ss : List Stmt} {x t y : ValueId} (h1 : ChainOK s t y)
    (h2 : ChainOK ss x t) : ChainOK (s ++ ss) x y := by
  intro T r rEnd xv hrun hx
  obtain ⟨r1, hs, hss⟩ := hrun.append
  obtain ⟨tv, ht, htr⟩ := h2 T r1 rEnd xv hss hx
  obtain ⟨yv, hy, hyr⟩ := h1 T r r1 tv hs ht
  exact ⟨yv, hy, htr.trans hyr⟩

theorem ChainOK.nil (y : ValueId) : ChainOK [] y y := by
  intro T r rEnd xv hrun hx
  cases hrun
  exact ⟨xv, hx, rfl⟩

/-- One wrapper keeps the truth. -/
theorem wrap_ok {w : Wrap} (hok : w.ok = true) {y n : ValueId} (hy : y < n) :
    ChainOK (w.stmts y n).1 (w.stmts y n).2.1 y := by
  intro T r rEnd xv hrun hx
  cases w with
  | ext op ty =>
    simp only [Wrap.stmts] at hrun hx
    obtain _ | ⟨he, hs, hr⟩ := hrun
    cases hr
    replace he := he Mem.empty
    cases hry : r y with
    | none =>
      cases op <;> simp [evalInst, Frame.get, hry, Res.ofOption, Res.bind] at he
    | some yv =>
      by_cases hw : yv.ty.width < ty.width
      · cases op <;>
        · simp [evalInst, Frame.get, hry, Res.ofOption, Res.bind, Res.check, hw, pure] at he
          subst he
          simp only [Regs.setMany, Option.some.injEq] at hs
          subst hs
          simp only [Regs.set_same, Option.some.injEq] at hx
          subst hx
          refine ⟨yv, rfl, ?_⟩
          first
            | exact truthy_zeroExtend _ (Nat.le_of_lt hw) yv.bits
            | exact truthy_signExtend _ (Nat.le_of_lt hw) yv.bits
      · cases op <;> simp [evalInst, Frame.get, hry, Res.ofOption, Res.bind, Res.check, hw] at he
  | icmp cc ty zl =>
    simp only [Wrap.stmts] at hrun hx
    obtain _ | ⟨he1, hs1, hr1⟩ := hrun
    obtain _ | ⟨he2, hs2, hr2⟩ := hr1
    cases hr2
    replace he1 := he1 Mem.empty
    replace he2 := he2 Mem.empty
    simp only [evalInst, Res.pure_eq_ok, Prod.mk.injEq, and_true] at he1
    subst he1
    simp only [Regs.setMany, Option.some.injEq] at hs1
    subst hs1
    have hyn : y ≠ n := Nat.ne_of_lt hy
    cases hry : r y with
    | none =>
      cases zl <;> simp [evalInst, Frame.getAs, Frame.get, hry, Regs.set_other _ _ hyn,
        Res.ofOption, Res.bind] at he2
    | some yv =>
      obtain ⟨yty, ybits⟩ := yv
      by_cases hty : yty = ty
      · subst hty
        cases zl <;>
        · simp [evalInst, Frame.getAs, Frame.get, hry, Regs.set_other _ _ hyn, Res.ofOption,
            Res.bind, Val.as?, pure] at he2
          subst he2
          simp only [Regs.setMany, Option.some.injEq] at hs2
          subst hs2
          simp only [Regs.set_same, Option.some.injEq] at hx
          subst hx
          refine ⟨_, rfl, ?_⟩
          exact (truthy_icmp_zero hok ybits : _)
      · cases zl <;> simp [evalInst, Frame.getAs, Frame.get, hry, Regs.set_other _ _ hyn,
          Res.ofOption, Res.bind, Val.as?, hty] at he2

/-- The inserted statements of a chain of truth-keeping wrappers keep the truth. -/
theorem prepChain_ok : ∀ (ws : List Wrap) (y n : ValueId), y < n → ws.all Wrap.ok = true →
    ChainOK (prepChain y n ws).1 (prepChain y n ws).2.1 y
  | [], y, _, _, _ => ChainOK.nil y
  | w :: ws, y, n, hy, hok => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have h1 := wrap_ok hok.1 hy
    have hlt : (w.stmts y n).2.1 < (w.stmts y n).2.2 := by
      cases w <;> simp [Wrap.stmts]
    have hn : n ≤ (w.stmts y n).2.2 := by cases w <;> simp [Wrap.stmts] <;> omega
    have h2 := prepChain_ok ws _ _ hlt hok.2
    have := h1.comp h2
    simpa [prepChain] using this

/-- The inserted statements: wrapper instructions with results from `n` on, up to the next
fresh value. -/
theorem prepChain_res : ∀ (ws : List Wrap) (y n : ValueId),
    (∀ st ∈ (prepChain y n ws).1, chainInst st.inst = true ∧ ∀ v ∈ st.results,
      n ≤ v ∧ v < (prepChain y n ws).2.2) ∧ n ≤ (prepChain y n ws).2.2
  | [], y, n => by simp [prepChain]
  | w :: ws, y, n => by
    obtain ⟨h1, h2⟩ := prepChain_res ws (w.stmts y n).2.1 (w.stmts y n).2.2
    have hs : ∀ st ∈ (w.stmts y n).1, chainInst st.inst = true ∧
        ∀ v ∈ st.results, n ≤ v ∧ v < (w.stmts y n).2.2 := by
      cases w with
      | ext => simp [Wrap.stmts, chainInst]
      | icmp cc ty zl => cases zl <;> simp [Wrap.stmts, chainInst]
    have hn : n ≤ (w.stmts y n).2.2 := by cases w <;> simp [Wrap.stmts] <;> omega
    have e1 : (prepChain y n (w :: ws)).1 =
        (w.stmts y n).1 ++ (prepChain (w.stmts y n).2.1 (w.stmts y n).2.2 ws).1 := by
      simp [prepChain]
    have e3 : (prepChain y n (w :: ws)).2.2 =
        (prepChain (w.stmts y n).2.1 (w.stmts y n).2.2 ws).2.2 := by
      simp [prepChain]
    rw [e1, e3]
    refine ⟨fun st hst => ?_, Nat.le_trans hn h2⟩
    rcases List.mem_append.1 hst with h | h
    · obtain ⟨hc, hv⟩ := hs st h
      exact ⟨hc, fun v hv' => ⟨(hv v hv').1, Nat.lt_of_lt_of_le (hv v hv').2 h2⟩⟩
    · obtain ⟨hc, hv⟩ := h1 st h
      exact ⟨hc, fun v hv' => ⟨Nat.le_trans hn (hv v hv').1, (hv v hv').2⟩⟩

/-! ## The blocks of the copy -/

/-- Block `b'` of the copy is block `b` of `g` with inserted statements `ss` (results from
`base` on) and either the same terminator (`ss = []`) or the `brif` on the chain's last value. -/
def PrepRel (base : Nat) (b b' : Block) : Prop :=
  b'.id = b.id ∧ b'.params = b.params ∧ ∃ ss, b'.body = b.body ++ ss ∧
    (∀ st ∈ ss, chainInst st.inst = true ∧ ∀ v ∈ st.results, base ≤ v) ∧
    ((ss = [] ∧ b'.term = b.term) ∨
      ∃ c t e x, b.term = .brif c t e ∧ b'.term = .brif x t e ∧ c < base ∧ ChainOK ss x c)

theorem PrepRel.refl (base : Nat) (b : Block) : PrepRel base b b :=
  ⟨rfl, rfl, [], by simp, by simp, .inl ⟨rfl, rfl⟩⟩

theorem prepBlock_rel (hints : List (BlockId × List Wrap)) {base n : Nat} (hn : base ≤ n)
    (b : Block) : PrepRel base b (prepBlock hints base n b).1 ∧ n ≤ (prepBlock hints base n b).2 := by
  unfold prepBlock
  split
  · rename_i c th el ws hterm _
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨hc, -⟩, hall⟩ := hcond
      obtain ⟨hres, hn'⟩ := prepChain_res ws c n
      have hok := prepChain_ok ws c n (Nat.lt_of_lt_of_le hc hn) hall
      generalize prepChain c n ws = p at hres hn' hok
      obtain ⟨ss, x, n'⟩ := p
      refine ⟨⟨rfl, rfl, ss, rfl, fun st hst => ⟨(hres st hst).1, fun v hv =>
        Nat.le_trans hn ((hres st hst).2 v hv).1⟩, .inr ⟨c, th, el, x, hterm, rfl, hc, hok⟩⟩, hn'⟩
    · exact ⟨PrepRel.refl base b, Nat.le_refl _⟩
  · exact ⟨PrepRel.refl base b, Nat.le_refl _⟩

theorem prepBlocks_rel (hints : List (BlockId × List Wrap)) (base : Nat) :
    ∀ (bs : List Block) (n : Nat), base ≤ n →
      (∀ b' ∈ prepBlocks hints base bs n, ∃ b ∈ bs, PrepRel base b b') ∧
      (∀ id b', (prepBlocks hints base bs n).find? (·.id == id) = some b' →
        ∃ b, bs.find? (·.id == id) = some b ∧ PrepRel base b b') ∧
      (∀ b', (prepBlocks hints base bs n).head? = some b' →
        ∃ b, bs.head? = some b ∧ PrepRel base b b')
  | [], _, _ => by simp [prepBlocks]
  | b :: bs, n, hn => by
    obtain ⟨hr, hn'⟩ := prepBlock_rel hints hn b
    obtain ⟨ih1, ih2, -⟩ := prepBlocks_rel hints base bs _ (Nat.le_trans hn hn')
    have e : prepBlocks hints base (b :: bs) n =
        (prepBlock hints base n b).1 :: prepBlocks hints base bs (prepBlock hints base n b).2 := by
      simp [prepBlocks]
    rw [e]
    refine ⟨fun b' hb' => ?_, fun id b' hf => ?_, fun b' hb' => ?_⟩
    · rcases List.mem_cons.1 hb' with rfl | h
      · exact ⟨b, List.mem_cons_self .., hr⟩
      · obtain ⟨b0, hb0, hr0⟩ := ih1 b' h
        exact ⟨b0, List.mem_cons_of_mem _ hb0, hr0⟩
    · simp only [List.find?_cons] at hf ⊢
      rw [hr.1] at hf
      cases hid : (b.id == id) with
      | true =>
        simp only [hid, Option.some.injEq] at hf
        subst hf
        exact ⟨b, rfl, hr⟩
      | false =>
        simp only [hid] at hf
        exact ih2 id b' hf
    · simp only [List.head?_cons, Option.some.injEq] at hb'
      subst hb'
      exact ⟨b, rfl, hr⟩

section
variable (g : Function) (hints : List (BlockId × List Wrap))

theorem condPrep_rel :
    (∀ b' ∈ (condPrep g hints).blocks, ∃ b ∈ g.blocks, PrepRel g.freshValue b b') ∧
    (∀ id b', (condPrep g hints).block? id = some b' →
      ∃ b, g.block? id = some b ∧ PrepRel g.freshValue b b') ∧
    (∀ b', (condPrep g hints).entry? = some b' → ∃ b, g.entry? = some b ∧ PrepRel g.freshValue b b') :=
  prepBlocks_rel hints g.freshValue g.blocks g.freshValue (Nat.le_refl _)

end

/-! ## The frame relation -/

section
variable {g : Function} {hints : List (BlockId × List Wrap)}

@[simp] theorem condPrep_globals : (condPrep g hints).globals = g.globals := rfl
@[simp] theorem condPrep_externs : (condPrep g hints).externs = g.externs := rfl
@[simp] theorem condPrep_sig : (condPrep g hints).sig = g.sig := rfl
@[simp] theorem condPrep_sigDecls : (condPrep g hints).sigDecls = g.sigDecls := rfl
@[simp] theorem condPrep_slots : (condPrep g hints).slots = g.slots := rfl
@[simp] theorem condPrep_name : (condPrep g hints).name = g.name := rfl

theorem refsOk_spec (h : refsOk g = true) {b : Block} (hb : b ∈ g.blocks) :
    (∀ st ∈ b.body, ∀ v ∈ operands st.inst, v < g.freshValue) ∧
      ∀ v ∈ termOperands b.term, v < g.freshValue := by
  simp only [refsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨fun st hst v hv => (h b hb).1 st hst v hv, fun v hv => (h b hb).2 v hv⟩

variable (g hints) in
/-- The frame relation (module doc): `X` runs the copy, `Y` runs `g`, at the same point of a
block `b` of `g`; `X` has the inserted statements `ss` still to run; registers below
`g.freshValue` agree; at a rebuilt `brif` the chain's truth is kept (`ChainOK` before `g`'s
statements are done, `ChainInv` in `X`'s current registers after). -/
def CR (X Y : Frame) : Prop :=
  X.func = condPrep g hints ∧ Y.func = g ∧ Y.slots = X.slots ∧
    Agree (· < g.freshValue) X.regs Y.regs ∧
    ∃ b ∈ g.blocks, Y.body <:+ b.body ∧ Y.term = b.term ∧ ∃ ss, X.body = Y.body ++ ss ∧
      (∀ st ∈ ss, chainInst st.inst = true ∧ ∀ v ∈ st.results, g.freshValue ≤ v) ∧
      ((ss = [] ∧ X.term = Y.term) ∨ ∃ c t e x, Y.term = .brif c t e ∧ X.term = .brif x t e ∧
        c < g.freshValue ∧ (Y.body ≠ [] → ChainOK ss x c) ∧ (Y.body = [] → ChainInv X X.regs ss x c))

/-- Entering a block: the copy's block and `g`'s, with arguments read alike. -/
theorem CR.enter {X Y : Frame} (hfx : X.func = condPrep g hints) (hfy : Y.func = g)
    (hsl : Y.slots = X.slots) (hag : Agree (· < g.freshValue) X.regs Y.regs) {bc bc' : BlockCall}
    (hblk : bc'.block = bc.block)
    (hga : ∀ args, X.getMany bc.args = .ok args → Y.getMany bc'.args = .ok args) {X1 : Frame}
    (h : enterBlock X bc = .ok X1) : ∃ Y1, enterBlock Y bc' = .ok Y1 ∧ CR g hints X1 Y1 := by
  obtain ⟨b', args, regs, hb', hga0, hty, hset, rfl⟩ := enterBlock_ok h
  rw [hfx] at hb'
  obtain ⟨b, hb, hid, hpar, ss, hbody, hss, hterm⟩ := (condPrep_rel g hints).2.1 _ _ hb'
  rw [hpar] at hty hset
  obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
  refine ⟨_, enterBlock_of (by rw [hfy, hblk]; exact hb) (hga args hga0) hty hset', ?_⟩
  refine ⟨hfx, hfy, hsl, hag', b, block?_mem hb, List.suffix_refl _, rfl, ss, hbody, hss, ?_⟩
  rcases hterm with ⟨rfl, ht⟩ | ⟨c, t, e, x, hbt, hbt', hc, hok⟩
  · exact .inl ⟨rfl, ht⟩
  · exact .inr ⟨c, t, e, x, hbt, hbt', hc, fun _ => hok, fun _ => hok _ _⟩

/-- Entering a block with the same block call, its arguments below `g.freshValue`. -/
theorem CR.enter_same {X Y : Frame} (hfx : X.func = condPrep g hints) (hfy : Y.func = g)
    (hsl : Y.slots = X.slots) (hag : Agree (· < g.freshValue) X.regs Y.regs) {bc : BlockCall}
    (hbc : ∀ v ∈ bc.args, v < g.freshValue) {X1 : Frame} (h : enterBlock X bc = .ok X1) :
    ∃ Y1, enterBlock Y bc = .ok Y1 ∧ CR g hints X1 Y1 :=
  CR.enter hfx hfy hsl hag rfl (fun args h => by
    rw [getMany_congr (fr := X) (fr' := Y) (fun v hv => hag v (hbc v hv))]; exact h) h

/-- The rest of the relation after a statement of `g` both run. -/
theorem CR.after {X Y : Frame} (h : CR g hints X Y) {st : Stmt} {restY : List Stmt}
    (hy : Y.body = st :: restY) {r1 r1' : Regs} (hag1 : Agree (· < g.freshValue) r1 r1') :
    ∃ ss, X.body = st :: (restY ++ ss) ∧
      CR g hints { X with regs := r1, body := restY ++ ss } { Y with regs := r1', body := restY } := by
  obtain ⟨hfx, hfy, hsl, -, b, hb, hsuf, hterm, ss, hxb, hss, hrel⟩ := h
  refine ⟨ss, by rw [hxb, hy]; rfl, hfx, hfy, hsl, hag1, b, hb,
    (List.suffix_cons st restY).trans (hy ▸ hsuf), hterm, ss, rfl, hss, ?_⟩
  rcases hrel with ⟨h1, h2⟩ | ⟨c, t, e, x, h1, h2, hc, hok, -⟩
  · exact .inl ⟨h1, h2⟩
  · have hok' := hok (by rw [hy]; simp)
    exact .inr ⟨c, t, e, x, h1, h2, hc, fun _ => hok', fun _ => hok' _ _⟩

/-- Both frames run the same statement of `g`. -/
theorem CR.stepA (hR : refsOk g = true) {X Y : Frame} {m : Mem} (h : CR g hints X Y)
    {st : Stmt} {restY : List Stmt} (hy : Y.body = st :: restY) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, lstep Y m = .next Y1 m1 ∧ CR g hints X1 Y1) ∧
    (∀ ext vals rs rest, lstep X m = .call ext vals rs rest → ∃ rest',
      lstep Y m = .call ext vals rs rest' ∧
      Cont (CR g hints) { X with body := rest } rs { Y with body := rest' } rs
        (AbiParam.tys ext.sig.returns)) ∧
    (∀ c, lstep X m = .trap c → lstep Y m = .trap c) := by
  have h0 := h
  obtain ⟨hfx, hfy, hsl, hag, b, hb, hsuf, -, ss, hxb, -, -⟩ := h
  have hops : ∀ v ∈ operands st.inst, v < g.freshValue :=
    (refsOk_spec hR hb).1 st (hsuf.subset (by rw [hy]; simp))
  have hxb' : X.body = st :: (restY ++ ss) := by rw [hxb, hy]; rfl
  by_cases hc : ∃ fn args, st.inst = .call fn args
  · obtain ⟨fn, args, hi⟩ := hc
    have hca : callArgs Y fn args = callArgs X fn args := by
      simp only [callArgs, Function.extern?, hfx, hfy, condPrep_externs]
      rw [getMany_congr (fr := X) (fr' := Y) (fun v hv => hag v (hops v (by simpa [hi, operands] using hv)))]
    rw [lstep_call hxb' hi, lstep_call hy hi, hca]
    refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest h => ?_, fun c h => ?_⟩
    · cases hcx : callArgs X fn args <;> simp [hcx, LRes.ofRes] at h
    · cases hcx : callArgs X fn args with
      | ok p =>
        obtain ⟨ext', vals'⟩ := p
        simp only [hcx, LRes.ofRes, LRes.call.injEq] at h ⊢
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨restY, ⟨rfl, rfl, rfl, rfl⟩, fun vs regs _ hs => ?_⟩
        obtain ⟨regs', hs', hag'⟩ := setMany_agree hag hs
        obtain ⟨ss', hxb'', hR'⟩ := CR.after h0 hy hag'
        rw [hxb'] at hxb''
        simp only [List.cons.injEq, List.append_cancel_left_eq, true_and] at hxb''
        subst hxb''
        exact ⟨regs', hs', hR'⟩
      | trap c => simp [hcx, LRes.ofRes] at h
      | stuck msg => simp [hcx, LRes.ofRes] at h
    · cases hcx : callArgs X fn args <;> simp [hcx, LRes.ofRes] at h ⊢
      exact h
  · have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
    have hev : evalInst Y m st.inst = evalInst X m st.inst :=
      evalInst_congr (by rw [hfx, hfy]; rfl) (by rw [hfx, hfy]; rfl) hsl
        (fun x hx => hag x (hops x hx))
    rw [lstep_inst hxb' hnc, lstep_inst hy hnc, hev]
    refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest h => ?_, fun c h => ?_⟩
    · cases he : evalInst X m st.inst with
      | ok p =>
        obtain ⟨vals, m'⟩ := p
        rw [he] at h
        simp only [LRes.ofRes] at h ⊢
        cases hs : X.regs.setMany st.results vals with
        | none => simp only [hs] at h; cases h
        | some r1 =>
          simp only [hs] at h
          cases h
          obtain ⟨r1', hs', hag'⟩ := setMany_agree hag hs
          obtain ⟨ss', hxb'', hR'⟩ := CR.after h0 hy hag'
          rw [hxb'] at hxb''
          simp only [List.cons.injEq, List.append_cancel_left_eq, true_and] at hxb''
          subst hxb''
          simp only [hs']
          exact ⟨_, rfl, hR'⟩
      | trap c => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
    · cases he : evalInst X m st.inst with
      | ok p =>
        obtain ⟨vals, m'⟩ := p
        rw [he] at h; simp only [LRes.ofRes] at h
        split at h <;> cases h
      | trap c => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
    · cases he : evalInst X m st.inst with
      | ok p =>
        obtain ⟨vals, m'⟩ := p
        rw [he] at h; simp only [LRes.ofRes] at h
        split at h <;> cases h
      | trap c' => rw [he] at h; simp only [LRes.ofRes] at h ⊢; exact h
      | stuck msg => rw [he] at h; cases h

/-- `X` runs an inserted statement; `g`'s frame waits at its `brif`. -/
theorem CR.stepB {X Y : Frame} {m : Mem} (h : CR g hints X Y) (hy : Y.body = [])
    {st : Stmt} {ss : List Stmt} (hx : X.body = st :: ss) :
    (∀ X1 m1, lstep X m = .next X1 m1 → m1 = m ∧ CR g hints X1 Y) ∧
    (∀ ext vals rs rest, lstep X m ≠ .call ext vals rs rest) ∧ (∀ c, lstep X m ≠ .trap c) := by
  obtain ⟨hfx, hfy, hsl, hag, b, hb, hsuf, hterm, ss0, hxb, hss, hrel⟩ := h
  rw [hy, List.nil_append] at hxb
  rw [hxb] at hx
  subst hx
  obtain ⟨hci, hres⟩ := hss st (by simp)
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => by
    rw [h] at hci; simp [chainInst] at hci
  rw [lstep_inst hxb hnc]
  refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest h => ?_, fun c h => ?_⟩
  · cases he : evalInst X m st.inst with
    | ok p =>
      obtain ⟨vals, m'⟩ := p
      rw [he] at h
      simp only [LRes.ofRes] at h
      cases hs : X.regs.setMany st.results vals with
      | none => simp only [hs] at h; cases h
      | some r1 =>
        simp only [hs, LRes.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hm, hall⟩ := evalInst_chain_mem hci he
        have hlo : ∀ v < g.freshValue, r1 v = X.regs v := fun v hv =>
          ((setMany_spec hs).2 v).1 fun hm => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hv (hres v hm))
        refine ⟨hm, hfx, hfy, hsl, fun v hv => by show Y.regs v = r1 v; rw [hlo v hv]; exact hag v hv, b, hb, hsuf,
          hterm, ss, by rw [hy]; rfl, fun st' hst' => hss st' (by simp [hst']), ?_⟩
        rcases hrel with ⟨h1, -⟩ | ⟨c, t, e, x, h1, h2, hc, -, hinv⟩
        · cases h1
        · refine .inr ⟨c, t, e, x, h1, h2, hc, fun h => absurd hy h, fun _ => ?_⟩
          intro rEnd xv hrun hxv
          have hrun0 : RunS { X with regs := r1, body := ss } r1 ss rEnd := hrun
          have hrun' : RunS X r1 ss rEnd :=
            RunS.congr (T := { X with regs := r1, body := ss }) (T' := X) rfl rfl rfl hrun0
          obtain ⟨cv, hcv, htr⟩ := hinv hy rEnd xv (.cons (fun m2 => hall m2) hs hrun') hxv
          exact ⟨cv, by show r1 c = some cv; rw [hlo c hc]; exact hcv, htr⟩
    | trap c => rw [he] at h; cases h
    | stuck msg => rw [he] at h; cases h
  · cases he : evalInst X m st.inst with
    | ok p =>
      obtain ⟨vals, m'⟩ := p
      rw [he] at h; simp only [LRes.ofRes] at h
      split at h <;> cases h
    | trap c => rw [he] at h; cases h
    | stuck msg => rw [he] at h; cases h
  · cases he : evalInst X m st.inst with
    | ok p =>
      obtain ⟨vals, m'⟩ := p
      rw [he] at h; simp only [LRes.ofRes] at h
      split at h <;> cases h
    | trap c' => exact evalInst_chain_trap hci c' he
    | stuck msg => rw [he] at h; cases h

theorem ofRes_enter_next {X : Frame} {bc : BlockCall} {m : Mem} {X1 : Frame} {m1 : Mem}
    (h : LRes.ofRes (enterBlock X bc) (fun fr => LRes.next fr m) = .next X1 m1) :
    enterBlock X bc = .ok X1 ∧ m1 = m := by
  cases he : enterBlock X bc with
  | ok Z => rw [he] at h; simp only [LRes.ofRes, LRes.next.injEq] at h; exact ⟨by rw [h.1], h.2.symm⟩
  | trap c => rw [he] at h; cases h
  | stuck msg => rw [he] at h; cases h

theorem ofRes_enter_ne {X : Frame} {bc : BlockCall} {m : Mem} {r : LRes}
    (hn : ∀ X1 m1, r ≠ .next X1 m1) (hs : ∀ msg, r ≠ .stuck msg) :
    LRes.ofRes (enterBlock X bc) (fun fr => LRes.next fr m) ≠ r := by
  intro h
  cases he : enterBlock X bc with
  | ok Z => rw [he] at h; exact hn Z m h.symm
  | trap c => exact enterBlock_not_trap _ _ _ he
  | stuck msg => rw [he] at h; exact hs msg h.symm

theorem ofRes_get_ne {X : Frame} {c : ValueId} {k : Val → LRes} {r : LRes}
    (hk : ∀ cv, k cv ≠ r) (hs : ∀ msg, r ≠ .stuck msg) : LRes.ofRes (X.get c) k ≠ r := by
  intro h
  cases hc : X.regs c with
  | none => simp [Frame.get, hc, Res.ofOption, LRes.ofRes] at h; exact hs _ h.symm
  | some cv => simp only [Frame.get, hc, Res.ofOption, LRes.ofRes] at h; exact hk cv h

/-- Both frames at their terminators. -/
theorem CR.stepC (hR : refsOk g = true) {X Y : Frame} {m : Mem} (h : CR g hints X Y)
    (hy : Y.body = []) (hx : X.body = []) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, lstep Y m = .next Y1 m1 ∧ CR g hints X1 Y1) ∧
    (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep X m = r →
      lstep Y m = r) := by
  obtain ⟨hfx, hfy, hsl, hag, b, hb, hsuf, hterm, ss, hxb, hss, hrel⟩ := h
  have hops : ∀ v ∈ termOperands Y.term, v < g.freshValue := by
    rw [hterm]; exact (refsOk_spec hR hb).2
  have hss0 : ss = [] := by rw [hx, hy] at hxb; exact hxb.symm
  subst hss0
  have henter : ∀ bc : BlockCall, (∀ v ∈ bc.args, v < g.freshValue) → ∀ X1 m1,
      LRes.ofRes (enterBlock X bc) (fun fr => LRes.next fr m) = .next X1 m1 →
      ∃ Y1, LRes.ofRes (enterBlock Y bc) (fun fr => LRes.next fr m) = .next Y1 m1 ∧
        CR g hints X1 Y1 := by
    intro bc hbc X1 m1 he
    obtain ⟨he1, hm⟩ := ofRes_enter_next he
    subst hm
    obtain ⟨Y1, he', hr⟩ := CR.enter_same hfx hfy hsl hag hbc he1
    exact ⟨Y1, by rw [he']; rfl, hr⟩
  have hget : ∀ v ∈ termOperands Y.term, Y.get v = X.get v := fun v hv => by
    simp only [Frame.get, hag v (hops v hv)]
  rw [lstep_term hx, lstep_term hy]
  rcases hrel with ⟨-, htx⟩ | ⟨c, t, e, x, hty, htx, hc, -, hinv⟩
  · rw [htx]
    cases hT : Y.term with
    | jump d =>
      rw [hT] at hops
      refine ⟨fun X1 m1 h => henter d hops X1 m1 h, fun r hn hs h => ?_⟩
      exact absurd h (ofRes_enter_ne hn hs)
    | brif c t e =>
      rw [hT] at hops hget
      simp only
      rw [hget c (by simp [termOperands])]
      have hargs : ∀ cv : Val, ∀ v ∈ (if Sem.truthy cv.bits then t else e).args,
          v < g.freshValue := fun cv v hv => hops v (by
        simp only [termOperands, List.mem_cons, List.mem_append]
        split at hv <;> simp [hv])
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hcv : X.get c with
        | ok cv => rw [hcv] at h; exact henter _ (hargs cv) X1 m1 h
        | trap _ => rw [hcv] at h; cases h
        | stuck _ => rw [hcv] at h; cases h
      · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)
    | brTable xi d tbl =>
      rw [hT] at hops hget
      simp only
      rw [hget xi (by simp [termOperands])]
      have hargs : ∀ xv : Val, ∀ v ∈ (tbl[xv.toNat]?.getD d).args, v < g.freshValue :=
        fun xv v hv => hops v (by
          simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
          cases hq : tbl[xv.toNat]? with
          | none => rw [hq] at hv; exact .inl (.inr hv)
          | some q => rw [hq] at hv; exact .inr ⟨q, List.mem_of_getElem? hq, hv⟩)
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hxv : X.get xi with
        | ok xv => rw [hxv] at h; exact henter _ (hargs xv) X1 m1 h
        | trap _ => rw [hxv] at h; cases h
        | stuck _ => rw [hxv] at h; cases h
      · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)
    | ret xs =>
      rw [hT] at hops
      have hgm : Y.getMany xs = X.getMany xs :=
        getMany_congr (fun v hv => hag v (hops v hv))
      simp only [hgm]
      refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
      cases hg : X.getMany xs <;> rw [hg] at h <;> cases h
    | returnCall fn args =>
      rw [hT] at hops
      have hta : tailArgs Y fn args = tailArgs X fn args := by
        simp only [tailArgs, Function.extern?, hfx, hfy, condPrep_externs, condPrep_sig]
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args) (fun v hv => hag v (hops v hv))]
      simp only [hta]
      refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
      cases hg : tailArgs X fn args <;> rw [hg] at h <;> cases h
    | trap tc =>
      dsimp only
      exact ⟨fun X1 m1 h => (by cases h), fun r _ _ h => h⟩
    | tryCall fn args et =>
      dsimp only
      exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩
    | tryCallIndirect c args et =>
      dsimp only
      exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩
  · rw [htx, hty]
    rw [hty] at hops
    simp only
    have hargs : ∀ b : Bool, ∀ v ∈ (if b then t else e).args, v < g.freshValue :=
      fun b v hv => hops v (by
        simp only [termOperands, List.mem_cons, List.mem_append]
        split at hv <;> simp [hv])
    refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
    · cases hxv : X.get x with
      | ok xv =>
        rw [hxv] at h
        simp only [LRes.ofRes] at h
        have hxr : X.regs x = some xv := by
          cases hr : X.regs x with
          | none => simp [Frame.get, hr, Res.ofOption] at hxv
          | some v => simp only [Frame.get, hr, Res.ofOption, Res.ok.injEq] at hxv; rw [hxv]
        obtain ⟨cv, hcv, htr⟩ := hinv hy X.regs xv (.nil _) hxr
        have hyc : Y.get c = .ok cv := by
          simp only [Frame.get, hag c hc, hcv, Res.ofOption]
        rw [hyc]
        simp only [LRes.ofRes]
        rw [← htr]
        exact henter _ (hargs _) X1 m1 h
      | trap _ => rw [hxv] at h; cases h
      | stuck _ => rw [hxv] at h; cases h
    · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)

/-! ## Fresh values -/

theorem freshValue_le_of_bound {f : Function} {N : Nat}
    (h : ∀ b ∈ f.blocks, (∀ p ∈ b.params, p.1 < N) ∧ ∀ st ∈ b.body, ∀ r ∈ st.results, r < N) :
    f.freshValue ≤ N := by
  unfold Function.freshValue
  generalize f.blocks = bs at h
  have hp : ∀ (ps : List (ValueId × Ty)) m, (∀ p ∈ ps, p.1 < N) → m ≤ N →
      ps.foldl (fun m p => max m (p.1 + 1)) m ≤ N := by
    intro ps
    induction ps with
    | nil => intro m _ hm; exact hm
    | cons p ps ihp =>
      intro m hps hm
      exact ihp _ (fun q hq => hps q (by simp [hq])) (Nat.max_le.2 ⟨hm, hps p (by simp)⟩)
  have hr : ∀ (rs : List ValueId) m, (∀ r ∈ rs, r < N) → m ≤ N →
      rs.foldl (fun m r => max m (r + 1)) m ≤ N := by
    intro rs
    induction rs with
    | nil => intro m _ hm; exact hm
    | cons r rs ihr =>
      intro m hrs hm
      exact ihr _ (fun q hq => hrs q (by simp [hq])) (Nat.max_le.2 ⟨hm, hrs r (by simp)⟩)
  have hs : ∀ (sts : List Stmt) m, (∀ st ∈ sts, ∀ r ∈ st.results, r < N) → m ≤ N →
      sts.foldl (fun m st => st.results.foldl (fun m r => max m (r + 1)) m) m ≤ N := by
    intro sts
    induction sts with
    | nil => intro m _ hm; exact hm
    | cons st sts ihs =>
      intro m hsts hm
      exact ihs _ (fun q hq => hsts q (by simp [hq])) (hr _ _ (hsts st (by simp)) hm)
  have key : ∀ (l : List Block), (∀ b ∈ l, (∀ p ∈ b.params, p.1 < N) ∧
      ∀ st ∈ b.body, ∀ r ∈ st.results, r < N) → ∀ m, m ≤ N →
      l.foldl (fun m (b : Block) =>
        let m := b.params.foldl (fun m p => max m (p.1 + 1)) m
        b.body.foldl (fun m st => st.results.foldl (fun m r => max m (r + 1)) m) m) m ≤ N := by
    intro l hl
    induction l with
    | nil => intro m hm; exact hm
    | cons b l ih =>
      intro m hm
      simp only [List.foldl_cons]
      apply ih (fun b' hb' => hl b' (by simp [hb']))
      exact hs _ _ (hl b (by simp)).2 (hp _ _ (hl b (by simp)).1 hm)
  exact key bs h 0 (Nat.zero_le _)

theorem prepBlocks_mem (hints : List (BlockId × List Wrap)) (base : Nat) :
    ∀ (bs : List Block) (n : Nat), ∀ b ∈ bs, ∃ b' ∈ prepBlocks hints base bs n,
      b'.params = b.params ∧ ∃ ss, b'.body = b.body ++ ss
  | [], _, b, hb => by cases hb
  | b0 :: bs, n, b, hb => by
    have e : prepBlocks hints base (b0 :: bs) n =
        (prepBlock hints base n b0).1 :: prepBlocks hints base bs (prepBlock hints base n b0).2 := by
      simp [prepBlocks]
    rw [e]
    rcases List.mem_cons.1 hb with rfl | h
    · have hshape : (prepBlock hints base n b).1.params = b.params ∧
          ∃ ss, (prepBlock hints base n b).1.body = b.body ++ ss := by
        unfold prepBlock
        split
        · split
          · generalize prepChain _ n _ = p
            obtain ⟨ss, x, n'⟩ := p
            exact ⟨rfl, ss, rfl⟩
          · exact ⟨rfl, [], by simp⟩
        · exact ⟨rfl, [], by simp⟩
      exact ⟨_, List.mem_cons_self .., hshape⟩
    · obtain ⟨b', hb', h'⟩ := prepBlocks_mem hints base bs _ b h
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem condPrep_freshValue (g : Function) (hints : List (BlockId × List Wrap)) :
    g.freshValue ≤ (condPrep g hints).freshValue := by
  apply freshValue_le_of_bound
  intro b hb
  obtain ⟨b', hb', hpar, ss, hbody⟩ := prepBlocks_mem hints g.freshValue g.blocks g.freshValue b hb
  have := lt_freshValue (f := condPrep g hints) hb'
  rw [hpar, hbody] at this
  exact ⟨this.1, fun st hst r hr => this.2 st (List.mem_append_left _ hst) r hr⟩

/-! ## The simulation -/

/-- The window values of `X` and `Y` are above `g.freshValue`: binding them keeps the
registers below it. -/
theorem agree_tryRets {X Y : Frame} (hfx : X.func = condPrep g hints) (hfy : Y.func = g)
    (hag : Agree (· < g.freshValue) X.regs Y.regs) {n : Nat} {vs : List Val} {regs regs' : Regs}
    (hs : X.regs.setMany (tryRets n X.func.freshValue) vs = some regs)
    (hs' : Y.regs.setMany (tryRets n Y.func.freshValue) vs = some regs') :
    Agree (· < g.freshValue) regs regs' := by
  have hle := condPrep_freshValue g hints
  intro v hv
  have h1 : v ∉ tryRets n X.func.freshValue := by
    intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : X.func.freshValue + j = v := he
    rw [hfx] at he'; exact no_window he' hv hle
  have h2 : v ∉ tryRets n Y.func.freshValue := by
    intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : Y.func.freshValue + j = v := he
    rw [hfy] at he'; exact no_window he' hv (Nat.le_refl _)
  rw [((setMany_spec hs').2 v).1 h2, ((setMany_spec hs).2 v).1 h1]
  exact hag v hv

/-- **The frame relation is a pass simulation with windows and handler edges.** -/
theorem CR.isSimWU (hR : refsOk g = true) (syms : String → Option Nat) :
    IsSimWU syms (CR g hints) := by
  -- the position of a related pair
  have hpos : ∀ X Y, CR g hints X Y → (∃ st restY, Y.body = st :: restY) ∨
      (Y.body = [] ∧ ∃ st ss, X.body = st :: ss) ∨ (Y.body = [] ∧ X.body = []) := by
    intro X Y _
    cases hY : Y.body with
    | cons st restY => exact .inl ⟨st, restY, rfl⟩
    | nil =>
      cases hX : X.body with
      | cons st ss => exact .inr (.inl ⟨rfl, st, ss, rfl⟩)
      | nil => exact .inr (.inr ⟨rfl, rfl⟩)
  have hxne : ∀ X Y, CR g hints X Y → ∀ st restY, Y.body = st :: restY → X.body ≠ [] := by
    rintro X Y ⟨-, -, -, -, -, -, -, -, ss, hxb, -⟩ st restY hy hx
    rw [hx, hy] at hxb; cases hxb
  -- `try_call` successors
  have hpost : ∀ (X Y : Frame) (n : Nat) (bc bc' : BlockCall) (et : ExnTable),
      (∀ v ∈ et.normal.vals, v < g.freshValue) → CR g hints X Y → Win X Y →
      tryNormal et X.func.freshValue = .ok bc → tryNormal et Y.func.freshValue = .ok bc' →
      ∀ rtys, TCont (CR g hints) X (tryRets n X.func.freshValue) bc Y
        (tryRets n Y.func.freshValue) bc' rtys := by
    rintro X Y n bc bc' et hops' ⟨hfx, hfy, hsl, hag, -⟩ hw hbc hbc' rtys vs regs _ hset
    obtain ⟨regs', hset'⟩ := setMany_len (r := Y.regs) (xs := tryRets n Y.func.freshValue)
      (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
        List.length_range] at this ⊢; exact this)
    have hW := setMany_tryRets hset
    have hW' := setMany_tryRets hset'
    have hagr := agree_tryRets hfx hfy hag hset hset'
    refine ⟨regs', hset', fun X1 he => ?_⟩
    obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair id (et := et) (et' := et)
      (by rw [TryDest.mapVals_id]) (b2 := Y.func.freshValue) hbc
    rw [hbc'] at hbc2; cases hbc2
    refine CR.enter (X := { X with regs }) (Y := { Y with regs := regs' }) hfx hfy hsl hagr hblk
      (fun args hga => getMany_pw2 (A := { X with regs }) (hpw.imp fun x y h => ?_) hga) he
    simp only
    rcases h with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
    · rw [hx, hy]; exact hagr v (hops' v hv)
    · rw [hx, hy, hW i, hW' i]
      split
      · rfl
      · exact (hw i).symm
  -- handler successors
  have hhand : ∀ (X Y : Frame) (et : ExnTable),
      (∀ d ∈ et.handlers, ∀ v ∈ d.vals, v < g.freshValue) → CR g hints X Y → Win X Y →
      HCont (CR g hints) X et Y et := by
    rintro X Y et hops' ⟨hfx, hfy, hsl, hag, -⟩ hw e
    refine ⟨fun hn => catchIn_eq_none.2 (catchIn_eq_none.1 hn), fun X1 hc => ?_⟩
    obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    obtain ⟨bc', hbc', hblk, hpw⟩ := tryHandler_pair id (b2 := Y.func.freshValue) hbc
    rw [TryDest.mapVals_id] at hbc'
    obtain ⟨regs', hset'⟩ := setMany_len (r := Y.regs)
      (xs := (List.range e.payload.length).map (Y.func.freshValue + ·)) (vs := e.payload)
      (by simp)
    have hW := setMany_tryRets (n := e.payload.length) (W := X.func.freshValue) hset
    have hW' := setMany_tryRets (n := e.payload.length) (W := Y.func.freshValue) hset'
    have hagr := agree_tryRets (n := e.payload.length) hfx hfy hag hset hset'
    have hd' : d ∈ et.handlers := catch?_mem hd
    refine ⟨_, catchIn_of hd hbc' hset', rfl, rfl, bc, bc', rfl, rfl, fun X2 he => ?_⟩
    have he0 : enterBlock { X with regs } bc = .ok X2 := by
      rw [← enterBlock_bt { X with regs } [] (.jump bc)]; exact he
    obtain ⟨Y2, he', hr⟩ := CR.enter (X := { X with regs }) (Y := { Y with regs := regs' }) hfx hfy
      hsl hagr hblk (fun args hga => getMany_pw2 (A := { X with regs })
        (hpw.imp fun x y h => by
          simp only
          rcases h with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
          · rw [hx, hy]; exact hagr v (hops' d hd' v hv)
          · rw [hx, hy, hW i, hW' i]
            split
            · rfl
            · exact (hw i).symm) hga) he0
    exact ⟨Y2, (enterBlock_bt { Y with regs := regs' } [] (.jump bc') bc').trans he', hr⟩
  -- a `try_call` frame: both at the same terminator
  have htry : ∀ X Y, CR g hints X Y → X.body = [] → (∀ c t e, X.term ≠ .brif c t e) →
      Y.body = [] ∧ Y.term = X.term ∧ ∀ v ∈ termOperands X.term, v < g.freshValue := by
    rintro X Y ⟨-, -, -, -, b, hb, -, hterm, ss, hxb, -, hrel⟩ hx hnb
    have hy : Y.body = [] := by
      rw [hx] at hxb; exact (List.append_eq_nil_iff.1 hxb.symm).1
    rcases hrel with ⟨-, htx⟩ | ⟨c, t, e, x, -, htx, -⟩
    · refine ⟨hy, htx.symm, ?_⟩
      rw [htx, hterm]; exact (refsOk_spec hR hb).2
    · exact absurd htx (hnb x t e)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro X Y ⟨hfx, hfy, hsl, -⟩; exact ⟨hsl, by rw [hfy, hfx]; rfl⟩
  · rintro X Y m X1 m1 hr hm hl
    rcases hpos X Y hr with ⟨st, restY, hy⟩ | ⟨hy, st, ss, hx⟩ | ⟨hy, hx⟩
    · obtain ⟨Y1, h1, h2⟩ := (CR.stepA hR hr hy (m := m)).1 X1 m1 hl
      exact ⟨Y1, .single h1, h2⟩
    · obtain ⟨rfl, h2⟩ := (CR.stepB hr hy hx (m := m)).1 X1 m1 hl
      exact ⟨Y, .refl _ _, h2⟩
    · obtain ⟨Y1, h1, h2⟩ := (CR.stepC hR hr hy hx (m := m)).1 X1 m1 hl
      exact ⟨Y1, .single h1, h2⟩
  · rintro X Y m ext vals rs rest hr hm hl
    rcases hpos X Y hr with ⟨st, restY, hy⟩ | ⟨hy, st, ss, hx⟩ | ⟨hy, hx⟩
    · obtain ⟨rest', h1, h2⟩ := (CR.stepA hR hr hy (m := m)).2.1 ext vals rs rest hl
      exact ⟨Y, rs, rest', .refl _ _, h1, h2⟩
    · exact absurd hl ((CR.stepB hr hy hx (m := m)).2.1 ext vals rs rest)
    · obtain ⟨st, fn, args, hbd, -⟩ := lstep_call_inv hl
      rw [hx] at hbd; cases hbd
  · rintro X Y m vals hr hm hl
    rcases hpos X Y hr with ⟨st, restY, hy⟩ | ⟨hy, st, ss, hx⟩ | ⟨hy, hx⟩
    · exact absurd (lstep_ret_inv hl) (hxne X Y hr st restY hy)
    · rw [lstep_ret_inv hl] at hx; cases hx
    · exact ⟨Y, .refl _ _, (CR.stepC hR hr hy hx (m := m)).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · rintro X Y m ext vals hr hm hl
    rcases hpos X Y hr with ⟨st, restY, hy⟩ | ⟨hy, st, ss, hx⟩ | ⟨hy, hx⟩
    · exact absurd (lstep_tail_inv hl) (hxne X Y hr st restY hy)
    · rw [lstep_tail_inv hl] at hx; cases hx
    · exact ⟨Y, .refl _ _, (CR.stepC hR hr hy hx (m := m)).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · rintro X Y m c hr hm hl
    rcases hpos X Y hr with ⟨st, restY, hy⟩ | ⟨hy, st, ss, hx⟩ | ⟨hy, hx⟩
    · exact ⟨Y, m, .refl _ _, (CR.stepA hR hr hy (m := m)).2.2 c hl⟩
    · exact absurd hl ((CR.stepB hr hy hx (m := m)).2.2 c)
    · exact ⟨Y, m, .refl _ _, (CR.stepC hR hr hy hx (m := m)).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · -- `call_indirect`
    rintro X Y m st rest sig callee args d a vals hr - - - hm hbd hi hca
    have hr0 := hr
    obtain ⟨hfx, hfy, hsl, hag, b, hb, hsuf, -, ss, hxb, hss, -⟩ := hr
    cases hY : Y.body with
    | nil =>
      rw [hY, List.nil_append, hbd] at hxb
      have := (hss st (by rw [← hxb]; simp)).1
      rw [hi] at this; simp [chainInst] at this
    | cons st' restY =>
      rw [hY, hbd] at hxb
      simp only [List.cons_append, List.cons.injEq] at hxb
      obtain ⟨rfl, rfl⟩ := hxb
      have hopsS := (refsOk_spec hR hb).1 st (hsuf.subset (by rw [hY]; simp))
      rw [hi] at hopsS
      refine ⟨Y, st, restY, sig, callee, args, .refl _ _, hY, hi, ?_, ?_⟩
      · rw [← hca]
        unfold ciArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hopsS v (by simp [operands, hv])))]
        simp only [Frame.get, hag callee (hopsS callee (by simp [operands])), hfx, hfy,
          condPrep_sigDecls]
      · intro vs regs _ hset
        obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
        obtain ⟨ss', hxb', hR'⟩ := CR.after hr0 hY hag'
        rw [hbd] at hxb'
        simp only [List.cons.injEq, true_and] at hxb'
        rw [hxb']
        exact ⟨regs', hset', hR'⟩
  · -- `try_call`, `try_call_indirect`
    refine ⟨?_, ?_⟩
    · rintro X Y m fn args et n base bc ext vals hr - - hw hm hbd ht htc hca
      obtain ⟨hy, hty, hopsT⟩ := htry X Y hr hbd (fun c t e h => by rw [ht] at h; cases h)
      have hr0 := hr
      obtain ⟨hfx, hfy, hsl, hag, -⟩ := hr
      rw [ht] at hopsT hty
      obtain ⟨rfl, hbc⟩ := tcArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := Y.func.freshValue) hbc
      have htc' : tcArgs Y fn et = .ok (n, Y.func.freshValue, bc') := by
        obtain ⟨e0, s0, he0, hs0, hc0, -, -, hn0⟩ := tcArgs_ok.1 htc
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', hn0⟩
        · rw [← he0]; simp only [Function.extern?, hfy, hfx, condPrep_externs]
        · rw [← hs0, hfy, hfx, condPrep_sigDecls]
      have hca' : callArgs Y fn args = .ok (ext, vals) := by
        rw [← hca]
        unfold callArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Function.extern?, hfy, hfx, condPrep_externs]
      refine ⟨Y, fn, args, et, _, bc', .refl _ _, hy, hty, htc', hca', ?_, ?_⟩
      · exact hpost X Y n bc bc' et (fun v hv => hopsT v (normal_vals_sub v hv)) hr0 hw hbc hbc' _
      · exact hhand X Y et (fun d hd v hv => hopsT v (by simp [termOperands, handler_vals hd hv]))
          hr0 hw
    · rintro X Y m callee args et n base bc d a vals hr - - hw hm hbd ht htc hca
      obtain ⟨hy, hty, hopsT⟩ := htry X Y hr hbd (fun c t e h => by rw [ht] at h; cases h)
      have hr0 := hr
      obtain ⟨hfx, hfy, hsl, hag, -⟩ := hr
      rw [ht] at hopsT hty
      obtain ⟨rfl, hbc⟩ := ticArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := Y.func.freshValue) hbc
      have htc' : ticArgs Y et = .ok (n, Y.func.freshValue, bc') := by
        obtain ⟨s0, hs0, -, -, hn0⟩ := ticArgs_ok.1 htc
        exact ticArgs_ok.2 ⟨s0, by rw [← hs0, hfy, hfx, condPrep_sigDecls], rfl, hbc', hn0⟩
      have hca' : ciArgs Y et.sig callee args = .ok (d, a, vals) := by
        rw [← hca]
        unfold ciArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Frame.get, hag callee (hopsT callee (by simp [termOperands])), hfy, hfx,
          condPrep_sigDecls]
      refine ⟨Y, callee, args, et, _, bc', .refl _ _, hy, hty, htc', hca', ?_, ?_⟩
      · exact hpost X Y n bc bc' et (fun v hv => hopsT v (normal_vals_sub' v hv)) hr0 hw hbc hbc' _
      · exact hhand X Y et (fun d hd v hv => hopsT v (by simp [termOperands, handler_vals hd hv]))
          hr0 hw

/-- **`g` simulates the copy with the rebuilt branch conditions** (module doc), whenever `g`
reads only values below its fresh value. -/
theorem condPrep_simU (hR : refsOk g = true) : FunSimU (condPrep g hints) g := by
  refine FunSimU.ofWU rfl rfl rfl rfl fun syms => ⟨CR g hints, CR.isSimWU hR syms, fun b hb => ?_⟩
  obtain ⟨b0, hb0, hid, hpar, ss, hbody, hss, hterm⟩ := (condPrep_rel g hints).2.2 b hb
  refine ⟨b0, hb0, hpar.symm, fun args regs slots _ _ _ => ?_⟩
  refine ⟨rfl, rfl, rfl, fun _ _ => rfl, b0, List.mem_of_mem_head? hb0, List.suffix_refl _, rfl,
    ss, hbody, hss, ?_⟩
  rcases hterm with ⟨rfl, ht⟩ | ⟨c, t, e, x, hbt, hbt', hc, hok⟩
  · exact .inl ⟨rfl, ht⟩
  · exact .inr ⟨c, t, e, x, hbt, hbt', hc, fun _ => hok, fun _ => hok _ _⟩

end
end Opt.MidVal
