import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.StockParameterKernel
import FV.Backend.Proof.StockParameterInput

namespace Backend.Stock.Proof.ParameterCfg.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
theorem nonentry_condition_metadata {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx function = .ok (ctx,ranges,initial)) :
    ctx.defInst? 31 = none ∧
      (ctx.valueType? 31 = some (.int 32) ∨ ctx.valueType? 31 = some (.int 64)) :=
  parameter_condition_metadata_ssa
    (bi := 1) (b := function.blocks[1]!) (ty := .i64)
    dominated.ssa rfl (by decide +kernel) (Or.inr rfl) build

/-- An actual nonentry conditional body has no entry ABI prelude. -/
theorem nonentry_prelude_witness (X : ExtSem) :
    ∃ result,Stock.lower function = .ok result ∧
      ∃ spec : ConditionalBodySpec function result function.blocks[1]! 1 1 31 ⟨2,[]⟩ ⟨3,[]⟩
        (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []},
        spec.preludeCode.size = 0 := by
  obtain ⟨result,run,tag,_⟩ := lowered
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family
    tag (b := function.blocks[1]!) rfl rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  exact ⟨result,run,spec,conditional_nonentry_prelude spec (by decide)⟩

theorem selected_ranked_target_witness :
    ∃ result,Stock.lower function = .ok result ∧
      ∃ tl targetLabel target,blockIdx? function 2 = some tl ∧ function.block? 2 = some target ∧
        function.blocks[tl]? = some target ∧ result.order.nodes[targetLabel]? = some (.original tl) ∧
        tl ≠ 0 ∧ 1 < targetLabel := by
  obtain ⟨result,run,tag,_⟩ := lowered
  exact ⟨result,run,selected_ranked_target run scope ranked tag
    (b := function.blocks[1]!) rfl (index := 0) (bc := ⟨2,[]⟩) rfl⟩

theorem actual_return_continuation_witness (X : ExtSem) :
    ∃ result event,Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧ event.block = 1 ∧
      ReturnsAt function result 1 1 function.blocks[1]! event
        (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []} := by
  obtain ⟨result,run,tag,_⟩ := lowered
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨event,member,atBlock,returns⟩ := nonentry_parameter_returns run scope dominated rfl ranked nonentry_terms family
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []} tag (b := function.blocks[1]!) rfl (by decide)
  exact ⟨result,event,run,member,atBlock,returns⟩


namespace Trap
theorem actual_trap_continuation_witness (X : ExtSem) :
    ∃ result event,Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧ event.block = 1 ∧
      TrapsAt function result 1 1 function.blocks[1]! event
        (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []} := by
  obtain ⟨result,run,tag,_⟩ := lowered
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨event,member,atBlock,traps⟩ := nonentry_parameter_traps run scope dominated rfl ranked nonentry_terms family
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []} tag (b := function.blocks[1]!) rfl (by decide)
  exact ⟨result,event,run,member,atBlock,traps⟩
end Trap
theorem parameter_cfg_machine_return_witness (X : ExtSem) (branch : Bool) :
    ∃ result ρ0,Stock.lower function = .ok result ∧
      RunOkABI function result.code (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        (initial (if branch then 1 else 0)).slots
        ⟨0,0,ρ0,Arm.write_base_gpr 0#5 (if branch then 1 else 0) Arm.ArmState.default⟩
        (.returned [⟨.i64,if branch then 1 else 2⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,_,_⟩ := lowered
  have domain := original_domain_witness
  have entered : Clif.enterFunc function [⟨.i64,if branch then 1 else 0⟩] Clif.Mem.empty =
      .ok (initial (if branch then 1 else 0),Clif.Mem.empty) := by cases branch <;> rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 4
      ⟨initial (if branch then 1 else 0),[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,if branch then 1 else 2⟩] Clif.Mem.empty := by cases branch <;> rfl
  let initialWorld := Arm.write_base_gpr 0#5 (if branch then 1 else 0) Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,if branch then 1 else 0⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,if branch then 1 else 0⟩)] at member
    have same := List.mem_singleton.mp member
    cases same
    simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    cases branch <;> rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := domain.returns run (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,semantics⟩

namespace Trap
theorem parameter_cfg_machine_trap_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧
      RunOkABI function result.code (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        (initial 0).slots ⟨0,0,ρ0,Arm.write_base_gpr 0#5 0 Arm.ArmState.default⟩ (.trapped .intDivz) := by
  obtain ⟨result,run,_,_⟩ := lowered
  have domain := original_domain_witness
  have entered : Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial 0,Clif.Mem.empty) := rfl
  have trapped : Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial 0,[],Clif.Mem.empty⟩ = .trapped .intDivz := rfl
  let initialWorld := Arm.write_base_gpr 0#5 0 Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,0⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,0⟩)] at member
    cases List.mem_singleton.mp member
    simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := domain.traps run (SourceEntry.of_enterFunc entered) trapped
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,semantics⟩
end Trap

end Backend.Stock.Proof.ParameterCfg.Fixture
