import FV.E2E.Guarded
import FV.E2E.RegLevelDriverSemR

/-!
# The guarded semantics with the register guard (#753, stage R2)

`Guarded`'s pinned call contracts for `csemG` give the contracts with registers for
`regG P (csemG …)` (`CallsRefineP.regG`, `IndCallsRefineP.regG`, `RegLevelDriverSemR`):
`callsRefinePR_csemG`, `indCallsRefinePR_csemG`.
-/

namespace E2E
open Backend Backend.Proof

set_option autoImplicit false

variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
  {P : BitVec 64 → Clif.Signature → Prop}

/-- A GOT load of `csemG` gives the symbol's link-time address. -/
theorem csemG_got : ∀ (rd : Reg) (n : String) (w : Arm.ArmState) (r : List CV × Arm.ArmState × Ctl),
    csemG F ctx X Rd syms exts sigs sp0 Pc (.loadExtNameGot rd n) [] w = some r →
      r.1 = [ofX (X.sym n 0)] := by
  intro rd n w r h
  obtain ⟨-, -, h⟩ := csemG_sub h
  simp only [csem, Option.some.injEq] at h
  rw [← h]

/-- **The pinned callee contract with registers for the register-guarded `csemG`.** -/
theorem callsRefinePR_csemG {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) (hP : RegCompatGot P exts (fun n => X.sym n 0)) :
    CallsRefinePR Pc F env exts MR (regG P (csemG F ctx X Rd syms exts sigs sp0 Pc)) :=
  (callsRefineP_csemG hX hMRm hMRc).regG csemG_got hP

/-- **The pinned indirect-call contract with registers for the register-guarded `csemG`.** -/
theorem indCallsRefinePR_csemG {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) (hP : RegCompatInd P env sigs syms) :
    IndCallsRefinePR Pc env sigs MR (regG P (csemG F ctx X Rd syms exts sigs sp0 Pc)) :=
  (indCallsRefineP_csemG hX hsym hMRm hMRc).regG (fun sl cm w h => (hMRm sl cm w h).symbols) hP

end E2E
