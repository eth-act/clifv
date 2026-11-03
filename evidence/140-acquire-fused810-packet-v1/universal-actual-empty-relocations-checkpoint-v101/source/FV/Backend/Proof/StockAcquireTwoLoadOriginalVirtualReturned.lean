import FV.Backend.Proof.StockAcquireTwoLoadVirtualReturned
import FV.Backend.Proof.StockAcquireTwoLoadOriginalReturned

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- Original public returned execution derives the complete real virtual return and exact free/leave result.
No caller supplies source steps, pending history, recovered bindings, or a scan schedule. -/
-- witness: native_decide
theorem original_returned_runOkABI {result : Result} (lowered : Stock.lower function = .ok result)
    {args : List Clif.Val} {state : Clif.State} (entered : ClifEntry function args state)
    (env : Clif.Env) (program : Clif.Program) (fuel : Nat) {values : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env program fuel state = .returned values final)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT}
    (refines : Refines F isem) (driver : DriverSem isem) (stable : MRStable F MR)
    (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR state.frame.slots state.mem world)
    (arguments : ArgsAtEntry F function.sig args world) :
    ∃ regs,RunOkABI function result.code isem MR state.frame.slots ⟨0,0,regs,world⟩ (.returned values final) := by
  obtain ⟨actual,event,run,scope,dominated,abi,size,events,schedule⟩ := original_two_load_schedule
  have resultEq := Except.ok.inj (run.symm.trans lowered)
  subst actual
  obtain ⟨firstPointer,secondPointer,first,second,argumentList,frame,callers,read0,read1,valuesEq,memoryEq⟩ :=
    original_returned_reads entered env program fuel returned
  have slots : state.frame.slots = [] := by rw [frame];rfl
  have execution := two_load_returned_runOkABI (env := env) (program := program) lowered scope dominated abi size events schedule read0 read1 refines driver memorySem stable memoryOk
    (by simpa only [slots] using memory) (by simpa only [argumentList] using arguments)
  refine ⟨entrySeed event.ctx (entry firstPointer secondPointer),?_⟩
  rw [slots,valuesEq,memoryEq]
  exact execution

end Backend.Stock.Proof.AcquireTwoLoadPrefix
