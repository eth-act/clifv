import FV.Backend.Proof.StockMemoryAccessPrepare
import FV.Backend.Proof.StockMemoryFaultContract
import FV.E2E.StockArithmeticStageContract
import FV.E2E.DeadCleanupContracts
import FV.E2E.DeadCleanupGot

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E
set_option autoImplicit false
set_option Elab.async false

/-- Both production cleanup modes preserve actual access boundaries. -/
theorem accessTrap_stage {cleanup : Bool} {vc prepared : VCode}
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    (checked : prepCheck (Stock.Arithmetic.stage cleanup vc) prepared = true)
    {regs : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (fault : VAccessTrapFrom ctx.slotBase vc (valueSem F ctx X) ⟨0,0,regs,world⟩ code property) :
    VAccessTrapFrom ctx.slotBase prepared (valueSem F ctx X) ⟨0,0,regs,world⟩ code property := by
  apply accessTraps_prepare (driverSem_valueSem F ctx X) checked
  cases cleanup with
  | false => exact fault
  | true =>
    exact accessTraps_prune
      (fun _ _ _ _ _ _ pure execution => valueSem_pure pure execution)
      (valueSem_cmpOverwrite F ctx X) fault

/-- The existing GOT invariant preserves a reached access with all original operands. -/
theorem accessTrap_gotV_value {sb : Nat} {vc : VCode}
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {regs : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (fault : VAccessTrapFrom sb vc (valueSem F ctx X) ⟨0,0,regs,world⟩ code property) :
    VAccessTrapFrom sb vc (valueSemV (GotV vc) F ctx X) ⟨0,0,regs,world⟩ code property := by
  obtain ⟨b,k,regs',next,block,inst,operands,uses,address,bytes,path,rest⟩ := fault
  obtain ⟨path',invariant⟩ := gotInv_star_value (gotInv_entry vc X regs world) path
  exact ⟨b,k,regs',next,block,inst,operands,uses,address,bytes,path',rest⟩

/-- Both production cleanup modes preserve the old ordinary return and explicit-trap contract. -/
theorem runOk_stage {f : Clif.Function} {cleanup : Bool} {vc prepared : VCode}
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    (checked : prepCheck (Stock.Arithmetic.stage cleanup vc) prepared = true)
    {regs : Nat → CV} {world : Arm.ArmState} {MR : MemRelT} {slots : List (Clif.SlotId × Nat)}
    {outcome : Clif.Outcome}
    (source : RunOkABI f vc (valueSem F ctx X) MR slots ⟨0,0,regs,world⟩ outcome) :
    RunOkABI f prepared (valueSem F ctx X) MR slots ⟨0,0,regs,world⟩ outcome := by
  have staged : RunOkABI f (Stock.Arithmetic.stage cleanup vc) (valueSem F ctx X) MR slots
      ⟨0,0,regs,world⟩ outcome := by
    cases cleanup with
    | false => exact source
    | true =>
      have runs := prune_correct (vc := vc) (sem := valueSem F ctx X)
        (fun _ _ _ _ _ _ pure execution => valueSem_pure pure execution)
        (valueSem_cmpOverwrite F ctx X) regs world
      cases outcome with
      | returned vals mem =>
        obtain ⟨us,outs,next,mem0,path,rest⟩ := source
        exact ⟨us,outs,next,mem0,runs.1 us outs next path,rest⟩
      | trapped code => exact runs.2 code source
      | stuck message => trivial
      | outOfFuel => trivial
  exact staged.prepared (driverSem_valueSem F ctx X) checked

end Backend.Stock.Proof.MemoryFaults
