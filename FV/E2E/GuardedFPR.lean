import FV.E2E.GuardedFP
import FV.E2E.GuardedR

/-!
# The guarded semantics with the scalar float accesses and the register guard (#753, stage R2)

`GuardedFP`'s pinned call contracts for `csemGF` give the contracts with registers for
`regG P (csemGF …)`: `callsRefinePR_csemGF`, `indCallsRefinePR_csemGF`.
-/

namespace E2E
open Backend Backend.Proof

set_option autoImplicit false

variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
  {P : BitVec 64 → Clif.Signature → Prop}

/-- A GOT load of `csemGF` gives the symbol's link-time address. -/
theorem csemGF_gotR : ∀ (rd : Reg) (n : String) (w : Arm.ArmState) (r : List CV × Arm.ArmState × Ctl),
    csemGF F ctx X Rd syms exts sigs sp0 Pc (.loadExtNameGot rd n) [] w = some r →
      r.1 = [ofX (X.sym n 0)] :=
  fun rd n w r h => csemG_gotR rd n w r h

/-- **The pinned callee contract with registers for the register-guarded `csemGF`.** -/
theorem callsRefinePR_csemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) (hP : RegCompatGot P exts (fun n => X.sym n 0)) :
    CallsRefinePR Pc F env exts MR (regG P (csemGF F ctx X Rd syms exts sigs sp0 Pc)) :=
  (callsRefineP_csemGF hX hMRm hMRc).regG csemGF_gotR hP

/-- **The pinned indirect-call contract with registers for the register-guarded `csemGF`.** -/
theorem indCallsRefinePR_csemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) (hP : RegCompatInd P env sigs syms) :
    IndCallsRefinePR Pc env sigs MR (regG P (csemGF F ctx X Rd syms exts sigs sp0 Pc)) :=
  (indCallsRefineP_csemGF hX hsym hMRm hMRc).regG (fun sl cm w h => (hMRm sl cm w h).symbols) hP

end E2E
