import FV.Backend.Proof.StockAcquireTwoLoadSourceOutcome

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every original returned execution contains both successful reads and the exact original returned values and memory. -/
theorem source_returned_iff (env : Clif.Env) (program : Clif.Program)
    (firstPointer secondPointer : BitVec 64) (memory : Clif.Mem) (fuel : Nat)
    (values : List Clif.Val) (final : Clif.Mem) :
    Clif.runLoop env program fuel ⟨entry firstPointer secondPointer,[],memory⟩ = .returned values final ↔
      5 ≤ fuel ∧ ∃ (first second : BitVec 8),
        memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first ∧
        memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second ∧
        values = [⟨.i64,first.setWidth 64⟩,⟨.i64,second.setWidth 64⟩] ∧ final = (memory.free []).leave := by
  have cases : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨ fuel = 4 ∨ ∃ n,fuel = n+5 := by
    by_cases short : fuel < 5
    · omega
    · exact .inr (.inr (.inr (.inr (.inr ⟨fuel-5,by omega⟩))))
  rcases cases with rfl | rfl | rfl | rfl | rfl | ⟨n,rfl⟩
  · simp [Clif.runLoop]
  · cases first : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 <;>
      cases second : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 <;>
      simp [Clif.runLoop,Clif.step,Clif.stepTerm,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.continueWith,Clif.returnValues,Clif.Frame.get,Clif.Frame.getMany,
      Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Nat.mod_one,Clif.checkTys,
      Clif.AbiParam.tys,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,first,second]
  · cases first : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 <;>
      cases second : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 <;>
      simp [Clif.runLoop,Clif.step,Clif.stepTerm,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.continueWith,Clif.returnValues,Clif.Frame.get,Clif.Frame.getMany,
      Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Nat.mod_one,Clif.checkTys,
      Clif.AbiParam.tys,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,first,second]
  · cases first : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 <;>
      cases second : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 <;>
      simp [Clif.runLoop,Clif.step,Clif.stepTerm,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.continueWith,Clif.returnValues,Clif.Frame.get,Clif.Frame.getMany,
      Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Nat.mod_one,Clif.checkTys,
      Clif.AbiParam.tys,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,first,second]
  · cases first : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 <;>
      cases second : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 <;>
      simp [Clif.runLoop,Clif.step,Clif.stepTerm,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.continueWith,Clif.returnValues,Clif.Frame.get,Clif.Frame.getMany,
      Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Nat.mod_one,Clif.checkTys,
      Clif.AbiParam.tys,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,first,second]
  · rw [source_more_steps]
    cases first : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 <;>
      cases second : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 <;>
      simp [first,second,and_comm,eq_comm]

end Backend.Stock.Proof.AcquireTwoLoadPrefix
