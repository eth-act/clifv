import FV.E2E.DeadCleanupUnwind
import FV.Backend.Lowering.StockArithmetic

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Both existing production stages retain the same raising call and original arguments. -/
theorem unwinds_stage {vc prepared : VCode} {cleanup : Bool}
    (checked : prepCheck (Stock.Arithmetic.stage cleanup vc) prepared = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {seed : Nat → CV} {initial after : Arm.ArmState} {obj : BitVec 64}
    (executed : VUnwinds vc (valueSemU F ctx X XR) XR seed initial obj after) :
    VUnwinds prepared (valueSemU F ctx X XR) XR seed initial obj after := by
  cases cleanup with
  | false =>
    exact (prepareCorrectU_of_check (driverSem_valueSemU F ctx X XR) checked XR).2 _ _ _ _ executed
  | true =>
    exact (prepareCorrectU_cleanup (driverSem_valueSemU F ctx X XR)
      (fun _ _ _ _ _ _ hp run => valueSemU_pure hp run)
      (valueSemU_cmpOverwrite F ctx X XR) checked XR).2 _ _ _ _ executed

end Backend.Stock.CallStore
