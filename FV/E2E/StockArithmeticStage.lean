import FV.E2E.StockArithmeticArtifact
import FV.E2E.DeadCleanupContracts
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Lowering.StockArithmetic

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Cleanup and preparation preserve the selected return execution and its
exact register/output tuple, as needed by linked return-site contracts. -/
theorem StockArithmeticStage_returns {cleanup : Bool} {vc vcp : VCode}
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    (prepared : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    {ρ : Nat → CV} {w world : Arm.ArmState} {us : List (Reg × Reg)} {outs : List CV}
    (source : VReturns vc (valueSem F ctx X) ρ w us outs world) :
    VReturns vcp (valueSem F ctx X) ρ w us outs world := by
  apply (prep_sound (driverSem_valueSem F ctx X) prepared ρ w).1 us outs world
  cases cleanup with
  | false => exact source
  | true =>
    exact (Backend.DeadCleanup.prune_correct (vc := vc) (sem := valueSem F ctx X)
      (fun _ _ _ _ _ _ pure execution => valueSem_pure pure execution)
      (valueSem_cmpOverwrite F ctx X) ρ w).1 us outs world source

/-- The production cleanup stage preserves ABI-aware executions under the
value semantics used by the existing cleanup machine consumer. -/
theorem StockArithmeticStage_return {f : Clif.Function} {cleanup : Bool} {vc vcp : VCode}
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    (prepared : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    {ρ : Nat → CV} {w : Arm.ArmState} {MR : MemRelT} {slots : List (Clif.SlotId × Nat)}
    {outcome : Clif.Outcome}
    (source : RunOkABI f vc (valueSem F ctx X) MR slots ⟨0,0,ρ,w⟩ outcome) :
    RunOkABI f vcp (valueSem F ctx X) MR slots ⟨0,0,ρ,w⟩ outcome := by
  have stageRun : RunOkABI f (Stock.Arithmetic.stage cleanup vc) (valueSem F ctx X) MR slots
      ⟨0,0,ρ,w⟩ outcome := by
    cases cleanup with
    | false => exact source
    | true =>
      have pruned := Backend.DeadCleanup.prune_correct (vc := vc) (sem := valueSem F ctx X)
        (fun _ _ _ _ _ _ pure execution => valueSem_pure pure execution)
        (valueSem_cmpOverwrite F ctx X) ρ w
      cases outcome with
      | returned vals cm =>
        obtain ⟨us,outs,w',cm0,reached,abi,arity,values,memory,freed⟩ := source
        exact ⟨us,outs,w',cm0,pruned.1 us outs w' reached,abi,arity,values,memory,freed⟩
      | trapped code => exact pruned.2 code source
      | stuck message => trivial
      | outOfFuel => trivial
  exact stageRun.prepared (driverSem_valueSem F ctx X) prepared

end E2E
