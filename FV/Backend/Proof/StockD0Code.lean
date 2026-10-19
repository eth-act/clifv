import Lean
import FV.Backend.Lowering.StockD0
import FV.Backend.Proof.LowerLoopCode

namespace Backend.Stock.D0
open Backend.Proof.Driver
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

deriving instance DecidableEq for VBlock
deriving instance DecidableEq for VCode
deriving instance DecidableEq for Except
attribute [-instance] instDecidableEqVBlock_stockD0Code instDecidableEqVCode_stockD0Code instDecidableEqExcept_stockD0Code
attribute [local instance] instDecidableEqVBlock_stockD0Code instDecidableEqVCode_stockD0Code instDecidableEqExcept_stockD0Code

macro "d0_open_kernel_decide" : tactic => `(tactic|
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let proof ← Lean.Meta.mkDecideProof (← g.getType)
    g.assign proof)

def eraseName (vc : VCode) : VCode := {vc with name := ""}

private theorem erased_defaultI32 (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .defaultI32 runs)).map (fun r => eraseName (denseCode r.code)) =
      (lowerFunction (source name .defaultI32 runs)).map eraseName := by d0_open_kernel_decide
private theorem erased_systemVI32 (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .systemVI32 runs)).map (fun r => eraseName (denseCode r.code)) =
      (lowerFunction (source name .systemVI32 runs)).map eraseName := by d0_open_kernel_decide
private theorem erased_fastI32 (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .fastI32 runs)).map (fun r => eraseName (denseCode r.code)) =
      (lowerFunction (source name .fastI32 runs)).map eraseName := by d0_open_kernel_decide
private theorem erased_defaultI64 (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .defaultI64 runs)).map (fun r => eraseName (denseCode r.code)) =
      (lowerFunction (source name .defaultI64 runs)).map eraseName := by d0_open_kernel_decide
private theorem erased_systemVI64 (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .systemVI64 runs)).map (fun r => eraseName (denseCode r.code)) =
      (lowerFunction (source name .systemVI64 runs)).map eraseName := by d0_open_kernel_decide
private theorem erased_fastI64 (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .fastI64 runs)).map (fun r => eraseName (denseCode r.code)) =
      (lowerFunction (source name .fastI64 runs)).map eraseName := by d0_open_kernel_decide

theorem erased_code (name : String) (c : Configuration) (runs : List Clif.RunCommand) :
    (Stock.lower (source name c runs)).map (fun r => eraseName (denseCode r.code)) =
      (lowerFunction (source name c runs)).map eraseName := by
  cases c with
  | defaultI32 => exact erased_defaultI32 name runs
  | systemVI32 => exact erased_systemVI32 name runs
  | fastI32 => exact erased_fastI32 name runs
  | defaultI64 => exact erased_defaultI64 name runs
  | systemVI64 => exact erased_systemVI64 name runs
  | fastI64 => exact erased_fastI64 name runs

theorem legacy_name {f : Clif.Function} {vc : VCode}
    (h : lowerFunction f = .ok vc) : vc.name = f.name := by
  rw [lowerFunction_eq] at h
  simp only [lowerFunction', bind, Except.bind, pure, Except.pure] at h
  repeat' first | split at h | cases h
  all_goals rfl

theorem normalized_eq_legacy (name : String) (c : Configuration) (runs : List Clif.RunCommand) :
    (Stock.lower (source name c runs)).map (compact name) =
      lowerFunction (source name c runs) := by
  have h := congrArg (Except.map (fun vc : VCode => {vc with name})) (erased_code name c runs)
  have hl :
      ((Stock.lower (source name c runs)).map (fun r => eraseName (denseCode r.code))).map
          (fun vc : VCode => {vc with name}) =
        (Stock.lower (source name c runs)).map (compact name) := by
    cases Stock.lower (source name c runs) <;> rfl
  rw [hl] at h
  rw [h]
  cases hr : lowerFunction (source name c runs) with
  | error e => rfl
  | ok vc =>
    change Except.ok {eraseName vc with name} = Except.ok vc
    have hn : vc.name = name := legacy_name hr
    cases vc
    cases hn
    rfl

theorem eligible_sound {f : Clif.Function} (h : eligible f = true) :
    ∃ c ∈ configurations, f = source f.name c f.runs := by
  simpa [eligible, List.any_eq_true] using h

#print axioms erased_code
#print axioms normalized_eq_legacy
#print axioms eligible_sound
end Backend.Stock.D0
