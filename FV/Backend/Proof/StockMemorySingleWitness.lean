import FV.Backend.Proof.StockMemorySingleFixture
import FV.Backend.Proof.StockMemorySingleDomain
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Memory.SingleFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A source-only complete memory domain, with no per-input proof certificate. -/
theorem domain : Domain function := domain_of_single_load_return scope dominated rfl rfl
  (b := function.blocks[0]!) rfl rfl rfl (by simp [function]) rfl

private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩,slots := [],
  body := [⟨[2],.load .load .i32 LoadFixture.flags 0 0⟩],term := .ret [2] }
private def world : Arm.ArmState := Arm.write_base_gpr 0#5 4096 LoadFixture.world

private theorem memory : LoadFixture.relation.holds function initial.slots LoadFixture.heap world := by
  refine ⟨⟨?_,LoadFixture.memory_world.1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact LoadFixture.memory_world.1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments : ArgsAtEntry LoadFixture.relation.F function.sig [⟨.i64,4096⟩] world := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
  cases List.mem_singleton.mp member
  simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  rfl

/-- Complete actual Stock instruction-zero execution reads the live nonzero
heap and returns its i32 value through the ABI. Original entry/memory premises,
source-defined retention, automatic root selection and result binding are used. -/
theorem complete_load_function_witness (X : ExtSem) :
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower function = .ok result ∧ Domain function ∧
      Clif.enterFunc function [⟨.i64,4096⟩] LoadFixture.heap = .ok (initial,LoadFixture.heap) ∧
      RunOkABI function result.code (csem LoadFixture.relation.F ⟨0,0⟩ X)
        (LoadFixture.relation.holds function) initial.slots ⟨0,0,ρ,world⟩
        (.returned [⟨.i32,2779096485⟩] LoadFixture.heap) := by
  have success := lowered
  cases run : Stock.lower function with
  | error err => rw [run] at success; cases success
  | ok result =>
    have entered : Clif.enterFunc function [⟨.i64,4096⟩] LoadFixture.heap = .ok (initial,LoadFixture.heap) := rfl
    obtain ⟨ρ,finished⟩ := domain.returns run (SourceEntry.of_enterFunc entered)
      (show Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],LoadFixture.heap⟩ =
        .returned [⟨.i32,2779096485⟩] LoadFixture.heap from rfl)
      (refines_csem LoadFixture.relation.F ⟨0,0⟩ X) (driverSem_csem LoadFixture.relation.F ⟨0,0⟩ X)
      (memRefines_csem LoadFixture.relation.F ⟨0,0⟩ X (syms := fun _ => none) rfl (fun _ _ h => by cases h))
      (E2E.mrStable_holds LoadFixture.relation function) (E2E.memRelOk_holds LoadFixture.relation function)
      memory arguments
    exact ⟨result,ρ,rfl,domain,entered,finished⟩

end Backend.Stock.Memory.SingleFixture
