import FV.E2E.StockCfgReadFixture
import FV.E2E.ABIReadCfg
import FV.Backend.Lowering.StockTwoBlockNI
import FV.Backend.Proof.StockCfgEntryAtWitness

namespace E2E.StockCfgNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

private abbrev function := InheritedWitness.function
private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,7⟩,slots := [],
  body := function.blocks[0]!.body,term := function.blocks[0]!.term }

/-- The actual two-block compiler result passes default validation, transfers
its complete jump/return trace between ABI worlds, and realizes it in the
existing value semantics. All execution starts at instruction zero. -/
theorem actual_cfg_return_realization (X : ExtSem) :
    ∃ result ρ us outs world,
      Stock.lower function = .ok result ∧
      Stock.TwoBlock.lowerValidated function = .ok result.code ∧
      SemanticNI.check function result.code = true ∧
      VReturns result.code (valueSem (fun _ => False) ⟨0,0⟩ X) ρ
        (Arm.write_base_gpr 0#5 7 Arm.ArmState.default) us outs world ∧
      PrefixHold [⟨.i64,16⟩] outs := by
  obtain ⟨result,run,checked,domain,compatible⟩ := CfgEntryAtWitness.checked_domain_witness
  have readCheck := StockCfgReadFixture.actual_read_check run
  have lower : Stock.TwoBlock.lowerValidated function = .ok result.code := by
    have eligible : Stock.TwoBlock.eligible function = true := by decide +kernel
    simp [Stock.TwoBlock.lowerValidated,eligible,run,checked,readCheck]
  have semantic : SemanticNI.check function result.code = true := by
    simp [SemanticNI.check,checked,readCheck]
  let w0 := Arm.write_base_gpr 0#5 7 Arm.ArmState.default
  have entered : Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,16⟩] Clif.Mem.empty := rfl
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,7⟩] w0 := by
    intro loc v member
    change (loc,v) ∈ [(.reg (.x 0),⟨.i64,7⟩)] at member
    have eq := List.mem_singleton.mp member
    cases eq
    simp only [VHolds,regVal,w0,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ,source⟩ := domain.returns run (SourceEntry.of_enterFunc entered) returned
    (CfgBoundary.refines (fun _ => False) ⟨0,0⟩ X) (CfgBoundary.driver (fun _ => False) ⟨0,0⟩ X)
    (CfgBoundary.memory (fun _ => False) ⟨0,0⟩ X (syms := fun _ => none) rfl (fun _ _ h => by cases h)) stable trivial arguments
  obtain ⟨us,outs,world,cm0,reached,pins,arity,values,memory,freed⟩ := source
  obtain ⟨world',transported,related⟩ := CfgBoundary.return_transport (args := [⟨.i64,7⟩]) (by rfl) readCheck
    (SameWorld.refl (fun _ => False) w0) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) reached
  obtain ⟨actual,realized,worlds⟩ := CfgBoundary.return_realize (by rfl) readCheck arguments transported
  exact ⟨result,ρ,us,outs,actual,run,lower,semantic,realized,values⟩

end E2E.StockCfgNIWitness
