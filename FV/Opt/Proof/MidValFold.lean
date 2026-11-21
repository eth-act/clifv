import FV.Opt.Proof.MidValCondSim
import FV.Opt.Proof.ConstPhiSimU
import FV.Opt.Proof.MidValNormConst
import FV.Opt.Proof.SimpDen

/-!
# Branch folding is simulated by its input (#1119, `rewrite:blocks`)

`Opt.MidVal.foldBr f bs` (`FV/Opt/MidValFold.lean`) turns the `brif`/`br_table` of the blocks
`bs` whose condition has a constant in `K = kLook f.freshValue (kTable f)` into the `jump` the
constant selects, when `kOk f K` accepts the constants. Here: **`foldBr_simU : FunSimU f
(foldBr f bs)`** and **`foldPre_simU : FunSimU f (foldPre f bs)`** (with `ConstPhi.run_simU`).

The frame relation `FR`: the two frames run the same point of a block `b` of `f` with the same
registers and slots, the folded frame with `foldBlock K bs b`'s terminator; and in `f`'s frame
every register whose value has a constant holds that constant or nothing (`KInv`). `KInv`
holds at the entry (only parameters are set, none has a constant) and is kept by every step:
a register is written only by its definitions (a statement's results, a block's parameters,
a `try_call`'s results and exception payload at `f.freshValue` and above, where `K` has no
constant), and a definition of a value with a constant `v` is a pure statement that defines only
it and evaluates to `v` once its operands hold their constants (`constEval_sound`: a pure
instruction with operands reads only them, `evalInst_isPure_frame`, not memory,
`evalInst_pureK_mem`; an instruction that evaluates reads all its operands, `evalInst_ops`).
At a folded `brif`/`br_table` the source reads the condition, which then holds the constant, so
it enters the block the `jump` enters.
-/

namespace Opt.MidVal

open Clif

/-! ## The constants -/

/-- Every register whose value has a constant in `K` holds that constant or nothing. -/
def KInv (K : ValueId → Option Val) (r : Regs) : Prop :=
  ∀ x v a, K x = some v → r x = some a → a = v

theorem kInv_empty (K : ValueId → Option Val) : KInv K Regs.empty := by
  intro x v a _ ha
  cases ha

theorem kInv_set {K : ValueId → Option Val} {r r' : Regs} {xs : List ValueId} {vs : List Val}
    (hI : KInv K r) (hn : ∀ x ∈ xs, K x = none) (hs : r.setMany xs vs = some r') : KInv K r' := by
  intro x v a hx ha
  have hxn : x ∉ xs := fun hm => by rw [hn x hm] at hx; cases hx
  rw [((setMany_spec hs).2 x).1 hxn] at ha
  exact hI x v a hx ha

theorem kOk_spec {f : Function} {K : ValueId → Option Val} (h : kOk f K = true) {b : Block}
    (hb : b ∈ f.blocks) :
    (∀ p ∈ b.params, K p.1 = none) ∧ ∀ st ∈ b.body, ∀ r ∈ st.results, ∀ v, K r = some v →
      st.results = [r] ∧ constEval K st.inst = some v := by
  simp only [kOk, List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hp, hs⟩ := h b hb
  refine ⟨hp, fun st hst r hr v hv => ?_⟩
  have := hs st hst r hr
  simp only [hv, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this

/-- A value with a constant is defined by an `iconst` or a pure instruction. -/
theorem constEval_pure {K : ValueId → Option Val} {i : Inst} {v : Val}
    (h : constEval K i = some v) : isPure i = true := by
  unfold constEval at h
  split at h
  · rfl
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact hc.1.1.1
    · cases h

/-- **The constant is the value**: an instruction with a constant, evaluated in a frame whose
operands hold their constants or nothing, gives exactly that constant. -/
theorem constEval_sound {K : ValueId → Option Val} {fr : Frame} {m m1 : Mem} {i : Inst}
    {v : Val} {vals : List Val} (hI : KInv K fr.regs) (hc : constEval K i = some v)
    (he : evalInst fr m i = .ok (vals, m1)) : vals = [v] := by
  unfold constEval at hc
  split at hc
  · rename_i ty imm
    simp only [Option.some.injEq] at hc
    subst hc
    simp only [evalInst, pure, Res.ok.injEq, Prod.mk.injEq] at he
    exact he.1.symm
  · split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true, Option.isSome_iff_exists] at hcond
      obtain ⟨⟨⟨hp, hpart⟩, hne⟩, hall⟩ := hcond
      split at hc
      · rename_i v' m' hk
        simp only [Option.some.injEq] at hc
        subst hc
        have hops := evalInst_ops (fr := fr) (mem := m) (i := i) (fun s h => by rw [he] at h; cases h)
        have hr : ∀ x ∈ operands i, (kFrame K).regs x = fr.regs x := by
          intro x hx
          obtain ⟨a, ha⟩ := hops x hx
          obtain ⟨w, hw⟩ := hall x hx
          rw [ha, show (kFrame K).regs x = K x from rfl, hw, hI x w a hw ha]
        have h1 : evalInst (kFrame K) m i = evalInst fr m i := evalInst_isPure_frame hp hne hr
        have h2 := evalInst_pureK_mem (fr := kFrame K) (m := Mem.empty) (m' := m)
          (by simp [pureK, hp]) hpart
        rw [h1, he, hk] at h2
        have h4 : (Res.ok (vals, m1) : Res (List Val × Mem)) = .ok ([v'], m) := by
          rw [h2]; rfl
        simp only [Res.ok.injEq, Prod.mk.injEq] at h4
        exact h4.1
      · cases hc
    · cases hc

/-- A statement of `f` keeps `KInv`. -/
theorem kInv_stmt {f : Function} {K : ValueId → Option Val} (hk : kOk f K = true) {b : Block}
    (hb : b ∈ f.blocks) {st : Stmt} (hst : st ∈ b.body) {fr : Frame} {m m1 : Mem}
    {vals : List Val} {r' : Regs} (hI : KInv K fr.regs) (he : evalInst fr m st.inst = .ok (vals, m1))
    (hs : fr.regs.setMany st.results vals = some r') : KInv K r' := by
  intro x v a hx ha
  by_cases hxr : x ∈ st.results
  · obtain ⟨hres, hce⟩ := (kOk_spec hk hb).2 st hst x hxr v hx
    have hv := constEval_sound hI hce he
    rw [hres, hv] at hs
    simp only [Regs.setMany, Option.some.injEq] at hs
    subst hs
    simp only [Regs.set_same, Option.some.injEq] at ha
    exact ha.symm
  · rw [((setMany_spec hs).2 x).1 hxr] at ha
    exact hI x v a hx ha

/-- A statement whose instruction has no constant (a call) defines no value with a constant. -/
theorem kOk_none {f : Function} {K : ValueId → Option Val} (hk : kOk f K = true) {b : Block}
    (hb : b ∈ f.blocks) {st : Stmt} (hst : st ∈ b.body) (hp : isPure st.inst = false) :
    ∀ x ∈ st.results, K x = none := by
  intro x hx
  cases hK : K x with
  | none => rfl
  | some v =>
    have := constEval_pure ((kOk_spec hk hb).2 st hst x hx v hK).2
    rw [hp] at this; cases this

/-! ## The folded function -/

section
variable {f : Function} {K : ValueId → Option Val} {bs : List BlockId}

@[simp] theorem foldFn_globals : (foldFn f K bs).globals = f.globals := rfl
@[simp] theorem foldFn_externs : (foldFn f K bs).externs = f.externs := rfl
@[simp] theorem foldFn_sig : (foldFn f K bs).sig = f.sig := rfl
@[simp] theorem foldFn_sigDecls : (foldFn f K bs).sigDecls = f.sigDecls := rfl
@[simp] theorem foldFn_slots : (foldFn f K bs).slots = f.slots := rfl
@[simp] theorem foldFn_name : (foldFn f K bs).name = f.name := rfl

theorem foldFn_freshValue : (foldFn f K bs).freshValue = f.freshValue := by
  simp only [Function.freshValue, foldFn, List.foldl_map]
  rfl

theorem foldFn_block? (id : BlockId) :
    (foldFn f K bs).block? id = (f.block? id).map (foldBlock K bs) := by
  simp only [Function.block?, foldFn, List.find?_map]
  rfl

theorem foldFn_entry? : (foldFn f K bs).entry? = f.entry?.map (foldBlock K bs) := by
  simp only [Function.entry?, foldFn, List.head?_map]

/-- The folded terminator: unchanged, or a `brif`/`br_table` on a value with a constant turned
into the `jump` it selects. -/
theorem foldBlock_term (b : Block) :
    (foldBlock K bs b).term = b.term ∨
    (∃ c t e v, b.term = .brif c t e ∧ K c = some v ∧
      (foldBlock K bs b).term = .jump (if Sem.truthy v.bits then t else e)) ∨
    (∃ x d tbl v, b.term = .brTable x d tbl ∧ K x = some v ∧
      (foldBlock K bs b).term = .jump (tbl[v.toNat]?.getD d)) := by
  simp only [foldBlock]
  split
  · cases ht : b.term with
    | brif c t e =>
      cases hc : K c with
      | none => left; simp [foldT, hc]
      | some v => right; left; exact ⟨c, t, e, v, rfl, hc, by simp [foldT, hc]⟩
    | brTable x d tbl =>
      cases hc : K x with
      | none => left; simp [foldT, hc]
      | some v => right; right; exact ⟨x, d, tbl, v, rfl, hc, by simp [foldT, hc]⟩
    | _ => left; rfl
  · left; rfl

/-! ## The folded frame reads what the source frame reads -/

theorem getMany_fold (X : Frame) (g : Function) (T : Terminator) (xs : List ValueId) :
    Frame.getMany { X with func := g, term := T } xs = X.getMany xs :=
  getMany_congr (fun _ _ => rfl)

theorem get_fold (X : Frame) (g : Function) (T : Terminator) (x : ValueId) :
    Frame.get { X with func := g, term := T } x = X.get x := rfl

theorem callArgs_fold {X : Frame} (hX : X.func = f) (T : Terminator) (fn : FnRef)
    (args : List ValueId) :
    callArgs { X with func := foldFn f K bs, term := T } fn args = callArgs X fn args := by
  unfold callArgs
  rw [getMany_fold]
  simp only [Function.extern?, hX, foldFn_externs]

theorem tailArgs_fold {X : Frame} (hX : X.func = f) (T : Terminator) (fn : FnRef)
    (args : List ValueId) :
    tailArgs { X with func := foldFn f K bs, term := T } fn args = tailArgs X fn args := by
  unfold tailArgs
  rw [getMany_fold]
  simp only [Function.extern?, hX, foldFn_externs, foldFn_sig]

theorem ciArgs_fold {X : Frame} (hX : X.func = f) (T : Terminator) (sig : Nat)
    (callee : ValueId) (args : List ValueId) :
    ciArgs { X with func := foldFn f K bs, term := T } sig callee args =
      ciArgs X sig callee args := by
  unfold ciArgs
  rw [getMany_fold]
  simp only [Frame.get, hX, foldFn_sigDecls]

theorem tcArgs_fold {X : Frame} (hX : X.func = f) (T : Terminator) (fn : FnRef) (et : ExnTable) :
    tcArgs { X with func := foldFn f K bs, term := T } fn et = tcArgs X fn et := by
  unfold tcArgs
  simp only [Function.extern?, hX, foldFn_externs, foldFn_sigDecls, foldFn_freshValue]

theorem ticArgs_fold {X : Frame} (hX : X.func = f) (T : Terminator) (et : ExnTable) :
    ticArgs { X with func := foldFn f K bs, term := T } et = ticArgs X et := by
  unfold ticArgs
  simp only [hX, foldFn_sigDecls, foldFn_freshValue]

/-! ## The frame relation -/

variable (f K bs) in
/-- The frame relation (module doc). -/
def FR (X Y : Frame) : Prop :=
  X.func = f ∧ KInv K X.regs ∧ ∃ b ∈ f.blocks, X.body <:+ b.body ∧ X.term = b.term ∧
    Y = { X with func := foldFn f K bs, term := (foldBlock K bs b).term }

/-- Entering a block: the folded block, with the same registers. -/
theorem FR.enter (hk : kOk f K = true) {A A1 : Frame} {bc : BlockCall} (hA : A.func = f)
    (hI : KInv K A.regs) (he : enterBlock A bc = .ok A1) (T : Terminator) :
    ∃ A1', enterBlock { A with func := foldFn f K bs, term := T } bc = .ok A1' ∧
      FR f K bs A1 A1' := by
  obtain ⟨B, args, regs, hB, hga, hty, hset, rfl⟩ := enterBlock_ok he
  rw [hA] at hB
  have hB' : (foldFn f K bs).block? bc.block = some (foldBlock K bs B) := by
    rw [foldFn_block?, hB]; rfl
  have hBm : B ∈ f.blocks := List.mem_of_find?_eq_some hB
  have hga' : Frame.getMany { A with func := foldFn f K bs, term := T } bc.args = .ok args := by
    rw [getMany_fold]; exact hga
  refine ⟨_, enterBlock_of (fr := { A with func := foldFn f K bs, term := T }) hB' hga' hty hset,
    hA, kInv_set hI (fun x hx => ?_) hset, B, hBm, List.suffix_refl _, rfl, rfl⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact (kOk_spec hk hBm).1 p hp

/-- A statement step of both frames. -/
theorem FR.stepA (hk : kOk f K = true) {X Y : Frame} {m : Mem} (h : FR f K bs X Y) {st : Stmt}
    {rest : List Stmt} (hx : X.body = st :: rest) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, lstep Y m = .next Y1 m1 ∧ FR f K bs X1 Y1) ∧
    (∀ ext vals rs rest', lstep X m = .call ext vals rs rest' →
      lstep Y m = .call ext vals rs rest' ∧
      Cont (FR f K bs) { X with body := rest' } rs { Y with body := rest' } rs
        (AbiParam.tys ext.sig.returns)) ∧
    (∀ c, lstep X m = .trap c → lstep Y m = .trap c) := by
  obtain ⟨hXf, hI, b, hb, hsuf, hterm, rfl⟩ := h
  have hst : st ∈ b.body := hsuf.subset (by rw [hx]; simp)
  have hsuf' : rest <:+ b.body := (List.suffix_cons st rest).trans (hx ▸ hsuf)
  have hy : ({ X with func := foldFn f K bs, term := (foldBlock K bs b).term } : Frame).body =
      st :: rest := hx
  by_cases hc : ∃ fn args, st.inst = .call fn args
  · obtain ⟨fn, args, hi⟩ := hc
    rw [lstep_call hx hi, lstep_call hy hi, callArgs_fold hXf]
    refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest' h => ?_, fun c h => h⟩
    · cases hcx : callArgs X fn args <;> simp [hcx, LRes.ofRes] at h
    · refine ⟨h, ?_⟩
      cases hcx : callArgs X fn args with
      | ok p =>
        obtain ⟨ext', vals'⟩ := p
        simp only [hcx, LRes.ofRes, LRes.call.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        intro vs regs _ hs
        refine ⟨regs, hs, hXf, kInv_set hI (kOk_none hk hb hst (by rw [hi]; rfl)) hs, b, hb,
          hsuf', hterm, rfl⟩
      | trap c => simp [hcx, LRes.ofRes] at h
      | stuck msg => simp [hcx, LRes.ofRes] at h
  · have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
    have hev : evalInst { X with func := foldFn f K bs, term := (foldBlock K bs b).term } m st.inst =
        evalInst X m st.inst :=
      evalInst_congr (by simp only [hXf, foldFn_globals]) (by simp only [hXf, foldFn_externs]) rfl
        (fun _ _ => rfl)
    rw [lstep_inst hx hnc, lstep_inst hy hnc, hev]
    refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest' h => ?_, fun c h => ?_⟩
    · cases he : evalInst X m st.inst with
      | ok p =>
        obtain ⟨vals, m'⟩ := p
        rw [he] at h
        simp only [LRes.ofRes] at h ⊢
        cases hs : X.regs.setMany st.results vals with
        | none => simp only [hs] at h; cases h
        | some r1 =>
          simp only [hs, LRes.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, rfl, hXf, kInv_stmt hk hb hst hI he hs, b, hb, hsuf', hterm, rfl⟩
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

/-- Both frames at their terminators. -/
theorem FR.stepC (hk : kOk f K = true) {X Y : Frame} {m : Mem} (h : FR f K bs X Y)
    (hx : X.body = []) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, lstep Y m = .next Y1 m1 ∧ FR f K bs X1 Y1) ∧
    (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep X m = r →
      lstep Y m = r) := by
  obtain ⟨hXf, hI, b, hb, hsuf, hterm, rfl⟩ := h
  have hy : ({ X with func := foldFn f K bs, term := (foldBlock K bs b).term } : Frame).body = [] :=
    hx
  have henter : ∀ (T : Terminator) (bc : BlockCall) X1 m1,
      LRes.ofRes (enterBlock X bc) (fun fr => LRes.next fr m) = .next X1 m1 →
      ∃ Y1, LRes.ofRes (enterBlock { X with func := foldFn f K bs, term := T } bc)
        (fun fr => LRes.next fr m) = .next Y1 m1 ∧ FR f K bs X1 Y1 := by
    intro T bc X1 m1 he
    obtain ⟨he1, hm⟩ := ofRes_enter_next he
    subst hm
    obtain ⟨Y1, he', hr⟩ := FR.enter hk hXf hI he1 T
    exact ⟨Y1, by rw [he']; rfl, hr⟩
  have hval : ∀ c v cv, K c = some v → X.get c = .ok cv → cv = v := by
    intro c v cv hc hg
    cases hr : X.regs c with
    | none => simp [Frame.get, hr, Res.ofOption] at hg
    | some a =>
      simp only [Frame.get, hr, Res.ofOption, Res.ok.injEq] at hg
      subst hg
      exact hI c v a hc hr
  rw [lstep_term hx, lstep_term hy]
  dsimp only
  rcases foldBlock_term (K := K) (bs := bs) b with ht | ⟨c, t, e, v, hbt, hc, ht⟩ |
    ⟨xi, d, tbl, v, hbt, hc, ht⟩
  · -- the same terminator
    rw [ht, ← hterm]
    cases hT : X.term with
    | jump d =>
      refine ⟨fun X1 m1 h => henter _ d X1 m1 h, fun r hn hs h => ?_⟩
      exact absurd h (ofRes_enter_ne hn hs)
    | brif c t e =>
      simp only [get_fold]
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hcv : X.get c with
        | ok cv => rw [hcv] at h; exact henter _ _ X1 m1 h
        | trap _ => rw [hcv] at h; cases h
        | stuck _ => rw [hcv] at h; cases h
      · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)
    | brTable xi d tbl =>
      simp only [get_fold]
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hxv : X.get xi with
        | ok xv => rw [hxv] at h; exact henter _ _ X1 m1 h
        | trap _ => rw [hxv] at h; cases h
        | stuck _ => rw [hxv] at h; cases h
      · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)
    | ret xs =>
      simp only [getMany_fold]
      refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
      cases hg : X.getMany xs <;> rw [hg] at h <;> cases h
    | returnCall fn args =>
      simp only [tailArgs_fold hXf]
      refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
      cases hg : tailArgs X fn args <;> rw [hg] at h <;> cases h
    | trap tc =>
      exact ⟨fun X1 m1 h => (by cases h), fun r _ _ h => h⟩
    | tryCall fn args et =>
      exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩
    | tryCallIndirect c args et =>
      exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩
  · -- a folded `brif`
    rw [ht, hterm.trans hbt]
    simp only
    refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
    · cases hcv : X.get c with
      | ok cv =>
        rw [hcv] at h
        simp only [LRes.ofRes] at h
        rw [hval c v cv hc hcv] at h
        exact henter _ _ X1 m1 h
      | trap _ => rw [hcv] at h; cases h
      | stuck _ => rw [hcv] at h; cases h
    · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)
  · -- a folded `br_table`
    rw [ht, hterm.trans hbt]
    simp only
    refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
    · cases hxv : X.get xi with
      | ok xv =>
        rw [hxv] at h
        simp only [LRes.ofRes] at h
        rw [hval xi v xv hc hxv] at h
        exact henter _ _ X1 m1 h
      | trap _ => rw [hxv] at h; cases h
      | stuck _ => rw [hxv] at h; cases h
    · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)

/-- The values `try_call` binds (results, exception payload) have no constant. -/
theorem kNone_window (hK : ∀ x v, K x = some v → x < f.freshValue) {j : Nat} :
    K (f.freshValue + j) = none := by
  cases h : K (f.freshValue + j) with
  | none => rfl
  | some v => exact absurd (hK _ v h) (Nat.not_lt.2 (Nat.le_add_right _ _))

/-- The folded frame's terminator at a `try_call`: the source's. -/
theorem FR.term_try {X Y : Frame} (h : FR f K bs X Y)
    (hnt : ∀ c t e, X.term ≠ .brif c t e) (hnb : ∀ x d tbl, X.term ≠ .brTable x d tbl) :
    Y = { X with func := foldFn f K bs } := by
  obtain ⟨-, -, b, -, -, hterm, rfl⟩ := h
  rcases foldBlock_term (K := K) (bs := bs) b with ht | ⟨c, t, e, v, hbt, -, -⟩ |
    ⟨xi, d, tbl, v, hbt, -, -⟩
  · rw [ht, ← hterm]
  · exact absurd (hterm.trans hbt) (hnt c t e)
  · exact absurd (hterm.trans hbt) (hnb xi d tbl)

/-- **The frame relation is a simulation with handler edges.** -/
theorem FR.isSimU (hk : kOk f K = true) (hK : ∀ x v, K x = some v → x < f.freshValue)
    (syms : String → Option Nat) : IsSimU syms (FR f K bs) := by
  -- after a `try_call`'s results or payload are bound, entering a block
  have hwin : ∀ (X : Frame) (n : Nat) (regs : Regs) (vs : List Val), X.func = f → KInv K X.regs →
      X.regs.setMany ((List.range n).map (f.freshValue + ·)) vs = some regs → KInv K regs := by
    intro X n regs vs _ hI hs
    refine kInv_set hI (fun x hx => ?_) hs
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact kNone_window hK
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro X Y ⟨hXf, -, b, -, -, -, rfl⟩
    exact ⟨rfl, by simp only [hXf, foldFn_sig]⟩
  · rintro X Y m X1 m1 hr hm hl
    cases hx : X.body with
    | cons st rest =>
      obtain ⟨Y1, h1, h2⟩ := (FR.stepA hk hr hx (m := m)).1 X1 m1 hl
      exact ⟨Y1, .single h1, h2⟩
    | nil =>
      obtain ⟨Y1, h1, h2⟩ := (FR.stepC hk hr hx (m := m)).1 X1 m1 hl
      exact ⟨Y1, .single h1, h2⟩
  · rintro X Y m ext vals rs rest hr hm hl
    obtain ⟨st, fn, args, hbd, -⟩ := lstep_call_inv hl
    obtain ⟨h1, h2⟩ := (FR.stepA hk hr hbd (m := m)).2.1 ext vals rs rest hl
    exact ⟨Y, rs, rest, .refl _ _, h1, h2⟩
  · rintro X Y m vals hr hm hl
    exact ⟨Y, .refl _ _, (FR.stepC hk hr (lstep_ret_inv hl) (m := m)).2 _ (fun _ _ h => by cases h)
      (fun _ h => by cases h) hl⟩
  · rintro X Y m ext vals hr hm hl
    exact ⟨Y, .refl _ _, (FR.stepC hk hr (lstep_tail_inv hl) (m := m)).2 _
      (fun _ _ h => by cases h) (fun _ h => by cases h) hl⟩
  · rintro X Y m c hr hm hl
    cases hx : X.body with
    | cons st rest => exact ⟨Y, m, .refl _ _, (FR.stepA hk hr hx (m := m)).2.2 c hl⟩
    | nil =>
      exact ⟨Y, m, .refl _ _, (FR.stepC hk hr hx (m := m)).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · -- `call_indirect`
    rintro X Y m st rest sig callee args d a vals hr hm hbd hi hca
    obtain ⟨hXf, hI, b, hb, hsuf, hterm, rfl⟩ := hr
    have hst : st ∈ b.body := hsuf.subset (by rw [hbd]; simp)
    refine ⟨_, st, rest, sig, callee, args, .refl _ _, hbd, hi, ?_, ?_⟩
    · rw [← hca]
      exact ciArgs_fold hXf _ sig callee args
    · intro vs regs _ hset
      refine ⟨regs, hset, hXf, kInv_set hI (kOk_none hk hb hst (by rw [hi]; rfl)) hset, b, hb,
        (List.suffix_cons st rest).trans (hbd ▸ hsuf), hterm, rfl⟩
  · -- `try_call`, `try_call_indirect`
    -- the normal-return successor
    have hpost : ∀ (X : Frame) (n : Nat) (bc : BlockCall) (rtys : List Ty), FR f K bs X
        { X with func := foldFn f K bs } →
        TCont (FR f K bs) X (tryRets n X.func.freshValue) bc { X with func := foldFn f K bs }
          (tryRets n X.func.freshValue) bc rtys := by
      rintro X n bc rtys ⟨hXf, hI, -⟩ vs regs _ hset
      refine ⟨regs, hset, fun X1 he => ?_⟩
      have hI' : KInv K regs := hwin X n regs vs hXf hI (by rw [← hXf]; exact hset)
      exact FR.enter hk (A := { X with regs }) hXf hI' he X.term
    -- the handlers
    have hhand : ∀ (X : Frame) (et : ExnTable), FR f K bs X { X with func := foldFn f K bs } →
        HCont (FR f K bs) X et { X with func := foldFn f K bs } et := by
      rintro X et ⟨hXf, hI, -⟩ e
      refine ⟨fun hn => catchIn_eq_none.2 (catchIn_eq_none.1 hn), fun X1 hc => ?_⟩
      obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
      have hfv : ({ X with func := foldFn f K bs } : Frame).func.freshValue = X.func.freshValue := by
        simp only [hXf, foldFn_freshValue]
      have hbc' : tryHandler d ({ X with func := foldFn f K bs } : Frame).func.freshValue = .ok bc := by
        rw [hfv]; exact hbc
      have hset' : ({ X with func := foldFn f K bs } : Frame).regs.setMany
          ((List.range e.payload.length).map
            (({ X with func := foldFn f K bs } : Frame).func.freshValue + ·)) e.payload = some regs := by
        rw [hfv]; exact hset
      refine ⟨_, catchIn_of hd hbc' hset', rfl, rfl, bc, bc, rfl, rfl, fun X2 he => ?_⟩
      have he0 : enterBlock { X with regs } bc = .ok X2 := by
        rw [← enterBlock_bt { X with regs } [] (.jump bc)]; exact he
      have hI' : KInv K regs := hwin X _ regs _ hXf hI (by rw [← hXf]; exact hset)
      obtain ⟨Y2, he', hr⟩ := FR.enter hk (A := { X with regs }) hXf hI' he0 X.term
      exact ⟨Y2, (enterBlock_bt { X with func := foldFn f K bs, regs := regs } [] (.jump bc) bc).trans
        he', hr⟩
    refine ⟨?_, ?_⟩
    · rintro X Y m fn args et n base bc ext vals hr hm hbd ht htc hca
      have hY := FR.term_try hr (fun c t e h => by rw [ht] at h; cases h)
        (fun x d tbl h => by rw [ht] at h; cases h)
      subst hY
      have hXf : X.func = f := hr.1
      obtain ⟨rfl, -⟩ := tcArgs_base htc
      refine ⟨_, fn, args, et, X.func.freshValue, bc, .refl _ _, hbd, ht,
        by rw [tcArgs_fold hXf]; exact htc, by rw [callArgs_fold hXf]; exact hca,
        hpost X n bc _ hr, hhand X et hr⟩
    · rintro X Y m callee args et n base bc d a vals hr hm hbd ht htc hca
      have hY := FR.term_try hr (fun c t e h => by rw [ht] at h; cases h)
        (fun x d tbl h => by rw [ht] at h; cases h)
      subst hY
      have hXf : X.func = f := hr.1
      obtain ⟨rfl, -⟩ := ticArgs_base htc
      refine ⟨_, callee, args, et, X.func.freshValue, bc, .refl _ _, hbd, ht,
        by rw [ticArgs_fold hXf]; exact htc, by rw [ciArgs_fold hXf]; exact hca,
        hpost X n bc _ hr, hhand X et hr⟩

/-- **The folded function simulates `f`**, for constants `kOk` accepts, all below
`f.freshValue`. -/
theorem foldFn_simU (hk : kOk f K = true) (hK : ∀ x v, K x = some v → x < f.freshValue) :
    FunSimU f (foldFn f K bs) where
  name := rfl
  sig := rfl
  slots := rfl
  externs := rfl
  sim syms := by
    refine ⟨FR f K bs, FR.isSimU hk hK syms, fun b hb => ?_⟩
    refine ⟨foldBlock K bs b, by rw [foldFn_entry?, hb]; rfl, rfl,
      fun args regs slots _ hset _ => ?_⟩
    have hbm : b ∈ f.blocks := List.mem_of_mem_head? hb
    refine ⟨rfl, kInv_set (kInv_empty K) (fun x hx => ?_) hset, b, hbm, List.suffix_refl _, rfl,
      rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (kOk_spec hk hbm).1 p hp

end

/-- `kLook fv`'s constants are below `fv`. -/
theorem kLook_lt {fv : Nat} {hm : Std.HashMap ValueId Val} {x : ValueId} {v : Val}
    (h : kLook fv hm x = some v) : x < fv := by
  unfold kLook at h
  split at h
  · assumption
  · cases h

/-- **Branch folding is simulated by its input.** -/
theorem foldBr_simU (f : Function) (bs : List BlockId) : FunSimU f (foldBr f bs) := by
  unfold foldBr
  split
  · exact FunSimU.refl f
  · dsimp only
    split
    · rename_i hk
      exact foldFn_simU hk (fun _ _ h => kLook_lt h)
    · exact FunSimU.refl f

/-- **The folded function without its unreachable blocks is simulated by its input.** -/
theorem foldPre_simU (f : Function) (bs : List BlockId) : FunSimU f (foldPre f bs) :=
  (foldBr_simU f bs).trans (ConstPhi.run_simU _)

end Opt.MidVal
