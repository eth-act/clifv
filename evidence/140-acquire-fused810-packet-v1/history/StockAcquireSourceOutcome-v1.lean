import FV.Backend.Proof.StockAcquire810Witness
import FV.Backend.Proof.StockAcquireBinding

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The original source entry keeps an arbitrary i64 pointer and arbitrary memory. -/
def entry (pointer : BitVec 64) : Clif.Frame := {
  func := function
  body := function.blocks[0]!.body
  term := .ret [2]
  regs := fun x => if x = 1 then some ⟨.i64,pointer⟩ else none
  slots := [] }

/-- Every complete source outcome is exactly the original atomic read outcome.
The widening and return add no source trap. -/
theorem source_three_steps (env : Clif.Env) (program : Clif.Program)
    (pointer : BitVec 64) (memory : Clif.Mem) :
    Clif.runLoop env program 3 ⟨entry pointer,[],memory⟩ =
      match memory.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 with
      | .ok raw => .returned [⟨.i64,raw.setWidth 64⟩] (memory.free []).leave
      | .trap code => .trapped code
      | .stuck message => .stuck message := by
  cases loaded : memory.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 with
  | ok raw =>
    simp [Clif.runLoop,Clif.step,Clif.stepTerm,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.continueWith,Clif.returnValues,Clif.Frame.get,Clif.Frame.getMany,
      Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,Clif.checkTys,
      Clif.AbiParam.tys,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,loaded]
  | trap code =>
    simp [Clif.runLoop,Clif.step,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.Frame.get,Clif.Res.ofOption,Clif.Res.check,Clif.Ty.bytes,entry,function,loaded]
  | stuck message =>
    simp [Clif.runLoop,Clif.step,Clif.evalInst,Clif.StepResult.ofRes,
      Clif.Frame.get,Clif.Res.ofOption,Clif.Res.check,Clif.Ty.bytes,entry,function,loaded]

end Backend.Stock.Proof.Acquire810
