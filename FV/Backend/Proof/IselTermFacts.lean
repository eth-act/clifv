import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.LowerContract
import FV.Backend.Proof.IselTermFactsRules
import FV.Backend.Proof.IselTermFactsCall

/-!
# Completeness of `lowerCheck`: terminators and calls

* `term_emits`: the lowering of a `return`, `trap`, `jump`, `brif` or `br_table` emits at least
  one instruction (the block's terminator segment is never empty);
* `branch_last`: the last instruction of a branch's lowering targets the branch's labels;
* `call_outgoing`, `try_outgoing`: lowering a `call` / `try_call` of an extern raises the
  outgoing stack-argument area to the callee's stack-argument size.

The symbolic executions of the rules are in `IselTermFactsRules` (shapes of the terminator
rules' code) and `IselTermFactsCall` (the outgoing area of the call rules).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- An array extended by a non-empty list ends with the list's last element. -/
theorem back_append_concat (A : Array MInst) (ms : List MInst) (i : MInst) :
    (A ++ (ms ++ [i]).toArray).back? = some i := by
  rw [← Array.toArray_toList (xs := A), List.append_toArray, List.back?_toArray]
  simp

/-- The terminator's context (filled in at `buildCtx`'s placeholder) keeps `CtxInv` and holds
the terminator's data at `ti`. -/
theorem termCtx_facts {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some (⟨.op .unit, [], [], none⟩ : IInfo)) (data : V) :
    CtxInv f (termCtx ctx ti data) ∧
      (termCtx ctx ti data).insts[ti]? = some ⟨data, [], [], none⟩ :=
  ⟨ctxInv_termCtx hctx hph data, termCtx_insts_self hph data⟩

/-- The lowering of a non-`try_call` terminator emits at least one instruction. -/
theorem term_emits {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) (hph : ctx.insts[ti]? = some (⟨.op .unit, [], [], none⟩ : IInfo))
    {t : Clif.Terminator} (ht : t.isTry = false) {data : V}
    (hd : termData (abiTerm f t) = .ok data) {targets : List Label} (htg : TargetsLen t targets)
    {s : LState} (hvb : ValsBelow ctx s) (hbt : BrIdxTyped ctx t) {out : V} {s' : LState}
    {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (some out, s', tr)) :
    s.emitted.size < s'.emitted.size := by
  obtain ⟨hctx', hi'⟩ := termCtx_facts hctx hph data
  have hvb' : ValsBelow (termCtx ctx ti data) s := hvb
  have hbt' : BrIdxTyped (termCtx ctx ti data) t := hbt
  unfold termCallF at h
  cases t with
  | ret xs =>
    obtain ⟨ms, i, hem⟩ := termShape_runTerm (t := .ret (xs ++ sretRet f)) hctx' rfl hd hi' hvb' h
    rw [hem]; simp
  | trap c =>
    obtain ⟨ms, i, hem⟩ := termShape_runTerm (t := .trap c) hctx' rfl hd hi' hvb' h
    rw [hem]; simp
  | jump d =>
    obtain ⟨ms, i, hem, -⟩ := branchShape_runTerm hctx' rfl hd hi' hbt' htg hvb' h
    rw [hem]; simp
  | brif c a b =>
    obtain ⟨ms, i, hem, -⟩ := branchShape_runTerm hctx' rfl hd hi' hbt' htg hvb' h
    rw [hem]; simp
  | brTable x d tbl =>
    obtain ⟨ms, i, hem, -⟩ := branchShape_runTerm hctx' rfl hd hi' hbt' htg hvb' h
    rw [hem]; simp
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at ht
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at ht

/-- The last instruction a branch's lowering (`jump`, `brif`, `br_table`) emits targets the
branch's labels (M4's `LowerTermOk`). -/
theorem branch_last {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) (hph : ctx.insts[ti]? = some (⟨.op .unit, [], [], none⟩ : IInfo))
    {t : Clif.Terminator} (ht : t.isTry = false)
    (hnr : ∀ vs, t ≠ .ret vs) (hnt : ∀ c, t ≠ .trap c) {data : V}
    (hd : termData (abiTerm f t) = .ok data) {targets : List Label} (htg : TargetsLen t targets)
    {s : LState} (hvb : ValsBelow ctx s) (hbt : BrIdxTyped ctx t) {out : V} {s' : LState}
    {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (some out, s', tr)) :
    ∀ i, s'.emitted.back? = some i → s.emitted.size < s'.emitted.size → i.targets = targets := by
  obtain ⟨hctx', hi'⟩ := termCtx_facts hctx hph data
  have hvb' : ValsBelow (termCtx ctx ti data) s := hvb
  have hbt' : BrIdxTyped (termCtx ctx ti data) t := hbt
  have key : ∀ (hrt : retOrTrap t = false) (hd' : termData t = .ok data)
      (h' : runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s =
        .ok (some out, s', tr)),
      ∀ i, s'.emitted.back? = some i → i.targets = targets := by
    intro hrt hd' h' i hb
    obtain ⟨ms, j, hem, htj⟩ := branchShape_runTerm hctx' hrt hd' hi' hbt' htg hvb' h'
    rw [hem, back_append_concat] at hb
    cases hb
    exact htj
  intro i hb _
  unfold termCallF at h
  cases t with
  | ret xs => exact absurd rfl (hnr xs)
  | trap c => exact absurd rfl (hnt c)
  | jump d => exact key rfl hd h i hb
  | brif c a b => exact key rfl hd h i hb
  | brTable x d tbl => exact key rfl hd h i hb
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at ht
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at ht

/-- Lowering a `call` of an extern raises the outgoing area to the callee's stack arguments. -/
theorem call_outgoing {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {fn : Clif.FnRef} {args : List Clif.ValueId} {e : Clif.ExtFunc}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.call fn args))
    (he : f.extern? fn = some e) {s : LState} {out : V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (some out, s', tr)) :
    stackBytes e.sig ≤ s'.outgoing := by
  exact callOut_runTerm hctx hi hc he h

/-- Lowering a `try_call` of an extern raises the outgoing area to the callee's stack
arguments. -/
theorem try_outgoing {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) {fn : Clif.FnRef} {args : List Clif.ValueId} {et : Clif.ExnTable}
    {e : Clif.ExtFunc} {data : V} (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (he : f.extern? fn = some e) {trs : List Reg × List Reg} {targets : List Label} {s : LState}
    {out : V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (some out, s', tr)) :
    stackBytes e.sig ≤ s'.outgoing := by
  have hlt : ctx.insts[ti]? = some ctx.insts[ti] := Array.getElem?_eq_getElem hti
  exact tryOut_runTerm (ctx := tryCtx ctx ti data trs) ⟨hctx.func, hctx.valueReg⟩ hd
    (termCtx_insts_self hlt data) he h

end Backend.Proof.Driver
