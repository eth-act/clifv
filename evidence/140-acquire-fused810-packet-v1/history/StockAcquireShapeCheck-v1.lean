import FV.Backend.Proof.StockAcquirePrepare

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def acquireByteShapeB : MInst → Bool
  | .loadAcquire ty (.vreg _ .int) (.vreg _ .int) _ => decide (ty = .int 8)
  | .loadAcquire _ _ _ _ => false
  | _ => true

/-- This internal check derives the exact byte form at every reached acquire. -/
theorem acquireByteShape_of_check {inst : MInst} (checked : acquireByteShapeB inst = true)
    {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {address : BitVec 64} {bytes : Nat}
    (access : AcquireAt inst uses world code address bytes) :
    ∃ d pointer flags,inst = .loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags := by
  cases access with
  | @acquire ty d pointer flags value world code atomic flag =>
    cases d <;> cases pointer <;> simp_all [acquireByteShapeB]
    all_goals split at checked <;> simp_all

end Backend.Stock.Proof.Acquire810
