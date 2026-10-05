import FV.E2E.Final
import FV.E2E.LowerDirect
import FV.Backend.Proof.FormsCoverComplete

/-!
# The final theorem without the lowering, `prepare` and form-coverage validators

`backend_correct_final` takes `Compiled` (the pipeline's results and the validators'
acceptance) and `FormsCovered` (decided per function by `formsCoveredB`). On `Dominated` input in
`LowerScope` (decided by `dominatedB`/`lowerScopeB` on the CLIF function alone) both are theorems:
`Compiled.of_lowerB` (V1, V2) and `formsCovered_completeB` (V3). What remains of the compiler's
checks is the register-allocation checker `checkAlloc` (V4), and the hypothesis
`hLI : LogicImmComplete`, discharged by `logicImmComplete`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov

/-- **The backend's end-to-end theorem from the pipeline's results**: `backend_correct_final`
with `Compiled` and `FormsCovered` replaced by the results of `lowerFunction`, `prepare`,
`checkAlloc`, `lowerRFunc`, `emitFunc` and the layout, on input with `dominatedB`/`lowerScopeB`.
The run and contract premises are `backend_correct_final`'s. -/
theorem backend_correct_final_of_lower (hLI : LogicImmComplete) {p : Clif.Program}
    {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final hsub (Compiled.of_lowerB hd hs hl hp hch ha he hla)
    (formsCovered_completeB hLI hs hl hp _) hC hCT hTls hX hXI hsym hslot hent hres hbe hargs hcs
    hrel htr fuel

/-! ## Non-vacuity

`lowerWitness` (a loop with block parameters, `LowerDirect.lean`) meets the input conditions,
and `lowerFunction` and `prepare` succeed on it: the premises of `formsCovered_complete` hold
together, and its conclusion is `formsCoveredB`'s acceptance without running it. -/

theorem lowerWitness_prepares :
    (match lowerFunction lowerWitness with
      | .ok vc => (Backend.prepare vc).isOk
      | .error _ => false) = true := by
  native_decide

/-- **Non-vacuity of `formsCovered_complete`**: its premises hold for `lowerWitness`, so the
prepared code is covered without `formsCoveredB` being run. -/
theorem formsCovered_complete_witness (hLI : LogicImmComplete) (cx : FnCtx) :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧
      ∃ vc vcp, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        FormsCovered cx vcp := by
  obtain ⟨hd, hs, -, -⟩ := lowerWitness_checks
  have hpr := lowerWitness_prepares
  cases h : lowerFunction lowerWitness with
  | error e => rw [h] at hpr; cases hpr
  | ok vc =>
    rw [h] at hpr
    simp only at hpr
    cases hp : Backend.prepare vc with
    | error e => rw [hp] at hpr; cases hpr
    | ok vcp =>
      exact ⟨dominated_of hd, lowerScope_of hs, vc, vcp, rfl, hp,
        formsCovered_complete hLI (lowerScope_of hs) h hp cx⟩

end E2E
