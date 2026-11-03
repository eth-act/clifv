import FV.Backend.Proof.PrepareComplete
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Lowering.StockArithmetic
import FV.E2E.RegLevelCall

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Backend.Proof.Prep Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- This internal instruction predicate excludes ordinary and exceptional calls. -/
def NoCallInst : MInst → Prop
  | .call .. | .tryCall .. => False
  | _ => True

/-- Retargeting cannot turn a non-call into a call. -/
theorem noCallInst_setTargets {i i' : MInst} {labels : List Label}
    (noCall : NoCallInst i) (retargeted : i.setTargets labels = some i') : NoCallInst i' := by
  cases i <;> simp_all [MInst.setTargets,NoCallInst]
  all_goals
    repeat' first
      | (solve | simp_all [NoCallInst])
      | split at retargeted
  all_goals cases Option.some.inj retargeted <;> trivial

/-- Actual preparation retains only original non-calls, retargeted non-calls, and edge jumps. -/
theorem prepare_no_call_insts {vc prepared : VCode}
    (run : prepare vc = .ok prepared) (domain : PrepDomain vc)
    (noCall : ∀ block ∈ vc.blocks.toList,∀ inst ∈ block.insts.toList,NoCallInst inst) :
    ∀ block ∈ prepared.blocks.toList,∀ inst ∈ block.insts.toList,NoCallInst inst := by
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,next,B,E,cfg0,cfg1,split,cfg2,rfl⟩ := prepare_facts run
  intro block member inst located
  rcases insts3 domain (cfg_spec cfg0) (cfg_spec cfg2) split member located with
    ⟨original,originalMember,originalInst⟩ |
    ⟨original,originalMember,originalInst,originalLocated,labels,retargeted⟩ | ⟨label,rfl⟩
  · exact noCall original originalMember inst originalInst
  · exact noCallInst_setTargets (noCall original originalMember originalInst originalLocated) retargeted
  · trivial

/-- Both actual cleanup modes preserve the non-call facts before preparation. -/
theorem stage_no_call_insts {vc : VCode}
    (noCall : ∀ block ∈ vc.blocks.toList,∀ inst ∈ block.insts.toList,NoCallInst inst) (cleanup : Bool) :
    ∀ block ∈ (Stock.Arithmetic.stage cleanup vc).blocks.toList,
      ∀ inst ∈ block.insts.toList,NoCallInst inst := by
  cases cleanup with
  | false => exact noCall
  | true => exact prune_insts noCall

/-- This internal preparation bridge covers both existing cleanup modes without a new check. -/
theorem stage_prepare_no_call_sites {vc prepared : VCode} {cleanup : Bool}
    (run : prepare (Stock.Arithmetic.stage cleanup vc) = .ok prepared)
    (domain : PrepDomain vc)
    (noCall : ∀ block ∈ vc.blocks.toList,∀ inst ∈ block.insts.toList,NoCallInst inst) :
    ∀ info,¬ prepared.CallSite info := by
  have stageDomain : PrepDomain (Stock.Arithmetic.stage cleanup vc) := by
    cases cleanup with
    | false => exact domain
    | true => exact prune_prepDomain domain
  have preserved := prepare_no_call_insts run stageDomain (stage_no_call_insts noCall cleanup)
  intro info site
  obtain ⟨b,block,k,present,located⟩ := site
  have member := Array.mem_of_getElem? present
  rcases located with located | ⟨ti,located⟩
  · exact preserved block (Array.mem_toList_iff.mpr member) (.call info)
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? located))
  · exact preserved block (Array.mem_toList_iff.mpr member) (.tryCall info ti)
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? located))

end Backend.Stock.Proof.Acquire810
