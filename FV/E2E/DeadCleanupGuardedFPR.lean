import FV.E2E.DeadCleanupGuardedFP
import FV.E2E.DeadCleanupGuardedR
import FV.E2E.GuardedFPR

/-!
# The guarded value semantics with the scalar float accesses and the register guard
(#753, stage R2)

`DeadCleanupGuardedFP`'s pinned call contracts for `valueSemGF` give the contracts with registers
for `regG P (valueSemGF …)`: `callsRefinePR_valueSemGF`, `indCallsRefinePR_valueSemGF`.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

set_option autoImplicit false

variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
  {P : BitVec 64 → Clif.Signature → Prop}

/-- A GOT load of `valueSemGF` gives the symbol's link-time address. -/
theorem valueSemGF_got : ∀ (rd : Reg) (n : String) (w : Arm.ArmState)
    (r : List CV × Arm.ArmState × Ctl),
    valueSemGF F ctx X Rd syms exts sigs sp0 Pc (.loadExtNameGot rd n) [] w = some r →
      r.1 = [ofX (X.sym n 0)] := by
  intro rd n w r h
  simp only [valueSemGF, specForm, pureForm, cmpForm, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte] at h
  exact csemGF_got rd n w r h

/-- **The pinned callee contract with registers for the register-guarded `valueSemGF`.** -/
theorem callsRefinePR_valueSemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) (hP : RegCompatGot P exts (fun n => X.sym n 0)) :
    CallsRefinePR Pc F env exts MR (regG P (valueSemGF F ctx X Rd syms exts sigs sp0 Pc)) :=
  (callsRefineP_valueSemGF hX hMRm hMRc).regG valueSemGF_got hP

/-- **The pinned indirect-call contract with registers for the register-guarded
`valueSemGF`.** -/
theorem indCallsRefinePR_valueSemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) (hP : RegCompatInd P env sigs syms) :
    IndCallsRefinePR Pc env sigs MR (regG P (valueSemGF F ctx X Rd syms exts sigs sp0 Pc)) :=
  (indCallsRefineP_valueSemGF hX hsym hMRm hMRc).regG
    (fun sl cm w h => (hMRm sl cm w h).symbols) hP

end E2E
