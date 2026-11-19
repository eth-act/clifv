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

end
end Opt.MidVal
