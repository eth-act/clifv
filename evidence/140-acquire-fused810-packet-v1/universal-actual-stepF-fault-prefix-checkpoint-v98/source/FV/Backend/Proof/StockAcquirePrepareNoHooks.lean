import FV.Backend.Proof.PrepareComplete
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Lowering.StockArithmetic
import FV.E2E.RegLevelCall

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Backend.Proof.Prep Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- This internal instruction predicate excludes all model-hook instruction families. -/
def NoHookInst : MInst → Prop
  | .call .. | .tryCall .. | .loadExtNameGot .. | .loadExtNameNear .. | .elfTlsGetAddr .. => False
  | _ => True

/-- Retargeting cannot turn a non-hook into a call. -/
theorem noHookInst_setTargets {i i' : MInst} {labels : List Label}
    (noHook : NoHookInst i) (retargeted : i.setTargets labels = some i') : NoHookInst i' := by
  cases i <;> simp_all [MInst.setTargets,NoHookInst]
  all_goals
    repeat' first
      | (solve | simp_all [NoHookInst])
      | split at retargeted
  all_goals cases Option.some.inj retargeted <;> trivial

/-- Actual preparation retains only original non-hooks, retargeted non-hooks, and edge jumps. -/
theorem prepare_no_hook_insts {vc prepared : VCode}
    (run : prepare vc = .ok prepared) (domain : PrepDomain vc)
    (noHook : ∀ block ∈ vc.blocks.toList,∀ inst ∈ block.insts.toList,NoHookInst inst) :
    ∀ block ∈ prepared.blocks.toList,∀ inst ∈ block.insts.toList,NoHookInst inst := by
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,next,B,E,cfg0,cfg1,split,cfg2,rfl⟩ := prepare_facts run
  intro block member inst located
  rcases insts3 domain (cfg_spec cfg0) (cfg_spec cfg2) split member located with
    ⟨original,originalMember,originalInst⟩ |
    ⟨original,originalMember,originalInst,originalLocated,labels,retargeted⟩ | ⟨label,rfl⟩
  · exact noHook original originalMember inst originalInst
  · exact noHookInst_setTargets (noHook original originalMember originalInst originalLocated) retargeted
  · trivial

/-- Both actual cleanup modes preserve the non-hook facts before preparation. -/
theorem stage_no_hook_insts {vc : VCode}
    (noHook : ∀ block ∈ vc.blocks.toList,∀ inst ∈ block.insts.toList,NoHookInst inst) (cleanup : Bool) :
    ∀ block ∈ (Stock.Arithmetic.stage cleanup vc).blocks.toList,
      ∀ inst ∈ block.insts.toList,NoHookInst inst := by
  cases cleanup with
  | false => exact noHook
  | true => exact prune_insts noHook

/-- Both existing modes preserve the complete non-hook instruction property through actual preparation. -/
theorem stage_prepare_no_hook_insts {vc prepared : VCode} {cleanup : Bool}
    (run : prepare (Stock.Arithmetic.stage cleanup vc) = .ok prepared) (domain : PrepDomain vc)
    (noHook : ∀ block ∈ vc.blocks.toList,∀ inst ∈ block.insts.toList,NoHookInst inst) :
    ∀ block ∈ prepared.blocks.toList,∀ inst ∈ block.insts.toList,NoHookInst inst := by
  have stageDomain : PrepDomain (Stock.Arithmetic.stage cleanup vc) := by
    cases cleanup with
    | false => exact domain
    | true => exact prune_prepDomain domain
  exact prepare_no_hook_insts run stageDomain (stage_no_hook_insts noHook cleanup)

end Backend.Stock.Proof.Acquire810
