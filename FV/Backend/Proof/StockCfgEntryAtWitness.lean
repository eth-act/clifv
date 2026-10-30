import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockTwoBlockCheck
import FV.Backend.Proof.StockTwoBlockReturn
import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockCfgReturnEdgeAt
import FV.Backend.Proof.StockInheritedJumpDefined
import FV.Backend.Proof.StockInheritedFixture
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.StockEntrySeed
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.StockJumpDemand
import FV.Backend.Proof.StockPerEdgeValues
import FV.Backend.Proof.StockSourceEdgeDFG

namespace Backend.Stock.Proof.CfgEntryAtWitness
open InheritedWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

private def initial : Clif.Frame := {
  func := function
  regs := Clif.Regs.empty.set 0 ⟨.i64,7⟩
  slots := []
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

private theorem globalFamily : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
    decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)

private theorem bodyFamily : ∀ stm ∈ function.blocks[0]!.body,
    (∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop := by
  intro stm member
  change stm ∈ [⟨[1],.iconst .i64 9⟩,⟨[],.nop⟩] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl ⟨.i64,9,rfl⟩
  · exact Or.inr rfl

/-- Actual instruction-zero ABI entry, inherited7, copied9 and return16
inhabit the general two-block return theorem, without a machine certificate. -/
theorem executable_entry_return_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        initial.slots ⟨0,0,ρ0,Arm.write_base_gpr 0#5 7 Arm.ArmState.default⟩
        (.returned [⟨.i64,16⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,scope,dominated⟩ := actual_inherited_driver_witness
  have entered : Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,16⟩] Clif.Mem.empty := rfl
  let initialWorld := Arm.write_base_gpr 0#5 7 Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,7⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,7⟩)] at member
    have same := List.mem_singleton.mp member
    cases same
    simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none)
      (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  have forwarded : ∀ stm ∈ function.blocks[0]!.body,∀ x ∈ stm.results,x ∈ ([1] : List Nat) := by
    intro stm member x defined
    change stm ∈ [⟨[1],.iconst .i64 9⟩,⟨[],.nop⟩] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact defined
    · cases defined
  obtain ⟨ρ0,semantics⟩ := TwoBlock.entry_return_frame run scope dominated (by decide +kernel)
    (entry := function.blocks[0]!) (target := function.blocks[1]!) (bc := ⟨10,[1]⟩) (xs := [3])
    rfl rfl rfl rfl (by decide +kernel) globalFamily bodyFamily forwarded (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,scope,dominated,entered,semantics⟩

-- witness: native_decide (fixed original-input scope/dominance/ABI checks only)
private theorem input_checks : Stock.TwoBlock.sourceOk function = true := by native_decide

/-- Executable source/artifact checks inhabit the reused production domain
and actual single-successor compatibility, including a nonempty copy vector. -/
theorem checked_domain_witness : ∃ result,Stock.lower function = .ok result ∧
    Stock.TwoBlock.check function result.code = true ∧ Stock.Scalar.Domain function ∧
    EdgeLegacyCompatible result.code result.edgeArgs := by
  obtain ⟨result,run,scope,dominated⟩ := actual_inherited_driver_witness
  have source := input_checks
  have checked : Stock.TwoBlock.check function result.code = true := by
    simp [Stock.TwoBlock.check,source,run]
  obtain ⟨actual,domain,compiled,equal⟩ := Stock.TwoBlock.check_sound checked
  have same : actual = result := Except.ok.inj (compiled.symm.trans run)
  subst actual
  exact ⟨result,run,checked,domain,TwoBlock.legacy_compatible run scope
    (entry := function.blocks[0]!) (target := function.blocks[1]!) (bc := ⟨10,[1]⟩) (xs := [3])
    rfl rfl rfl rfl (by decide +kernel)⟩

end Backend.Stock.Proof.CfgEntryAtWitness
