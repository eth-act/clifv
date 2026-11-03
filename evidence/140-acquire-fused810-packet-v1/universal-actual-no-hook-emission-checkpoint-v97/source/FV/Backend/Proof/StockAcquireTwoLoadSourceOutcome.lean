import FV.Backend.Proof.StockAcquireTwoLoadPrefixFixture

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The unchanged function receives arbitrary original i64 pointers and arbitrary memory. -/
def entry (first second : BitVec 64) : Clif.Frame := {
  func := function
  body := function.blocks[0]!.body
  term := .ret [100,101]
  regs := fun value => if value = 7 then some ⟨.i64,first⟩ else if value = 31 then some ⟨.i64,second⟩ else none
  slots := [] }

/-- The complete source run keeps both reads in their original order and retains every read outcome. -/
theorem source_five_steps (env : Clif.Env) (program : Clif.Program)
    (firstPointer secondPointer : BitVec 64) (memory : Clif.Mem) :
    Clif.runLoop env program 5 ⟨entry firstPointer secondPointer,[],memory⟩ =
      match memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 with
      | .trap code => .trapped code
      | .stuck message => .stuck message
      | .ok first =>
        match memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 with
        | .ok second => .returned [⟨.i64,first.setWidth 64⟩,⟨.i64,second.setWidth 64⟩] (memory.free []).leave
        | .trap code => .trapped code
        | .stuck message => .stuck message := by
  cases first : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 <;>
    cases second : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 <;>
    simp [Clif.runLoop,Clif.step,Clif.stepTerm,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.continueWith,Clif.returnValues,Clif.Frame.get,Clif.Frame.getMany,
      Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Nat.mod_one,Clif.checkTys,
      Clif.AbiParam.tys,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,first,second]

/-- Extra source fuel preserves the complete original outcome. -/
theorem source_more_steps (env : Clif.Env) (program : Clif.Program)
    (firstPointer secondPointer : BitVec 64) (memory : Clif.Mem) (fuel : Nat) :
    Clif.runLoop env program (fuel+5) ⟨entry firstPointer secondPointer,[],memory⟩ =
      match memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 with
      | .trap code => .trapped code
      | .stuck message => .stuck message
      | .ok first =>
        match memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 with
        | .ok second => .returned [⟨.i64,first.setWidth 64⟩,⟨.i64,second.setWidth 64⟩] (memory.free []).leave
        | .trap code => .trapped code
        | .stuck message => .stuck message := by
  cases first : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 <;>
    cases second : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 <;>
    simp [Clif.runLoop,Clif.step,Clif.stepTerm,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.continueWith,Clif.returnValues,Clif.Frame.get,Clif.Frame.getMany,
      Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Nat.mod_one,Clif.checkTys,
      Clif.AbiParam.tys,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,first,second]

/-- Every original source trap is exactly the first read fault or the second read fault after first-read success. -/
theorem source_first_trap (env : Clif.Env) (program : Clif.Program)
    (firstPointer secondPointer : BitVec 64) (memory : Clif.Mem) (fuel : Nat) (code : Clif.TrapCode) :
    Clif.runLoop env program fuel ⟨entry firstPointer secondPointer,[],memory⟩ = .trapped code ↔
      (0 < fuel ∧ memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .trap code) ∨
      (1 < fuel ∧ ∃ first,memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first ∧
        memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .trap code) := by
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
      simp [first,second]

end Backend.Stock.Proof.AcquireTwoLoadPrefix
