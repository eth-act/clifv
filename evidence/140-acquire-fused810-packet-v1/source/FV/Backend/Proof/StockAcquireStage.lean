import FV.Backend.Proof.StockAcquirePrepare
import FV.E2E.StockArithmeticStageContract
import FV.E2E.DeadCleanupContracts
import FV.E2E.DeadCleanupGot

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E
set_option autoImplicit false
set_option Elab.async false

/-- Both production cleanup modes preserve actual access boundaries. -/
theorem acquireTrap_stage {cleanup : Bool} {vc prepared : VCode}
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    (checked : prepCheck (Stock.Arithmetic.stage cleanup vc) prepared = true)
    {regs : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (fault : VAcquireBoundaryFrom vc (valueSem F ctx X) ⟨0,0,regs,world⟩ code property) :
    VAcquireBoundaryFrom prepared (valueSem F ctx X) ⟨0,0,regs,world⟩ code property := by
  apply acquireTraps_prepare (driverSem_valueSem F ctx X) checked
  cases cleanup with
  | false => exact fault
  | true =>
    exact acquireTraps_prune
      (fun _ _ _ _ _ _ pure execution => valueSem_pure pure execution)
      (valueSem_cmpOverwrite F ctx X) fault

/-- The existing GOT invariant preserves a reached access with all original operands. -/
theorem acquireTrap_gotV_value {vc : VCode}
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {regs : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (fault : VAcquireBoundaryFrom vc (valueSem F ctx X) ⟨0,0,regs,world⟩ code property) :
    VAcquireBoundaryFrom vc (valueSemV (GotV vc) F ctx X) ⟨0,0,regs,world⟩ code property := by
  obtain ⟨b,k,regs',next,block,inst,operands,uses,address,bytes,path,rest⟩ := fault
  obtain ⟨path',invariant⟩ := gotInv_star_value (gotInv_entry vc X regs world) path
  exact ⟨b,k,regs',next,block,inst,operands,uses,address,bytes,path',rest⟩

end Backend.Stock.Proof.Acquire810
