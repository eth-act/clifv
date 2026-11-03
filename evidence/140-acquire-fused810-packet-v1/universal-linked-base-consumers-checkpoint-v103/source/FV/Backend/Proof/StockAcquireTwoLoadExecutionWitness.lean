import FV.Backend.Proof.StockAcquireTwoLoadSourceOutcome

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- One ordinary original allocation makes the first read succeed and the second read fault. -/
def witnessMemory : Clif.Mem := {
  allocs := [⟨4096,1,false⟩]
  bytes := fun address => if address = 4096 then some 42 else none }

def witnessArgs : List Clif.Val := [⟨.i64,(4096#64)⟩,⟨.i64,(8192#64)⟩]

def witnessWorld (before : Arm.ArmState) : Arm.ArmState :=
  Arm.w (.GPR 1#5) 8192 (Arm.w (.GPR 0#5) 4096 before)

/-- The two original source reads have compatible success and fault outcomes. -/
theorem witness_read_outcomes :
    witnessMemory.load {} (Clif.effAddr ⟨.i64,(4096#64)⟩ 0) 1 8 = .ok 42 ∧
    witnessMemory.load {} (Clif.effAddr ⟨.i64,(8192#64)⟩ 0) 1 8 = .trap .heapOob := by
  constructor <;> rfl

/-- The exact original body traps at its second load after the first load succeeds. -/
theorem witness_source_run (env : Clif.Env) (program : Clif.Program) :
    Clif.runLoop env program 5 ⟨entry 4096 8192,[],witnessMemory⟩ = .trapped .heapOob := by
  exact (source_five_steps env program 4096 8192 witnessMemory).trans (by rfl)

/-- Original source entry accepts both unchanged argument bindings. -/
theorem witness_source_entry : SourceEntry function witnessArgs (entry 4096 8192) := by
  refine ⟨function.blocks[0]!, (entry 4096 8192).regs,rfl,rfl,rfl,?_,rfl⟩
  simp only [function,witnessArgs,Clif.Regs.setMany,Clif.Regs.empty,Clif.Regs.set]
  apply congrArg some
  funext value
  by_cases first : value = 7 <;> by_cases second : value = 31 <;> simp_all [entry,Clif.Ty.width,Clif.Regs.empty]

/-- Existing ABI argument locations hold both original pointers in one compatible world. -/
theorem witness_abi_arguments (F : BitVec 64 → Prop) (before : Arm.ArmState) :
    ArgsAtEntry F function.sig witnessArgs (witnessWorld before) := by
  have locations : locsOf function.sig = [.reg (.x 0),.reg (.x 1)] := rfl
  intro location value member
  simp only [locations,witnessArgs,List.zip_cons_cons,List.zip_nil_left,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same
  · rcases Prod.mk.inj same with ⟨rfl,rfl⟩
    simp [VHolds,Clif.Ty.width,regVal,witnessWorld,rnum,Arm.r_of_w_same]
  · rcases Prod.mk.inj same with ⟨rfl,rfl⟩
    simp [VHolds,Clif.Ty.width,regVal,witnessWorld,rnum,Arm.r_of_w_same]

/-- One unchanged admitted input inhabits both selected consumers, compatible entry/ABI facts, and the second source fault. -/
-- witness: native_decide
theorem original_two_load_execution_witness :
    ∃ (result : Result) (event : BlockScanEvent),Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ sigAbiOk function.sig = true ∧
      result.blockScans.size = 1 ∧ event ∈ result.blockScans.toList ∧ ActualSchedule event ∧
      SourceEntry function witnessArgs (entry 4096 8192) ∧
      witnessMemory.load {} (Clif.effAddr ⟨.i64,(4096#64)⟩ 0) 1 8 = .ok 42 ∧
      witnessMemory.load {} (Clif.effAddr ⟨.i64,(8192#64)⟩ 0) 1 8 = .trap .heapOob ∧
      (∀ F before,ArgsAtEntry F function.sig witnessArgs (witnessWorld before)) ∧
      ∀ env program,Clif.runLoop env program 5 ⟨entry 4096 8192,[],witnessMemory⟩ = .trapped .heapOob := by
  obtain ⟨result,event,run,scope,dominated,abi,size,events,schedule⟩ := original_two_load_schedule
  exact ⟨result,event,run,scope,dominated,abi,size,events,schedule,witness_source_entry,
    witness_read_outcomes.1,witness_read_outcomes.2,witness_abi_arguments,witness_source_run⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix
