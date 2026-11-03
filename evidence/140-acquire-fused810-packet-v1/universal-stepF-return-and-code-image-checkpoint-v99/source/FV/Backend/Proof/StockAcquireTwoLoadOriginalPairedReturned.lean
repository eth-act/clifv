import FV.Backend.Proof.StockAcquireTwoLoadPairedReturned
import FV.Backend.Proof.StockAcquireTwoLoadOriginalReturned

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- Original public returned execution derives the complete real virtual return and exact free/leave result.
No caller supplies source steps, pending history, recovered bindings, or a scan schedule. -/
-- witness: native_decide
theorem original_returned_paired_runOkABI {result : Result} (lowered : Stock.lower function = .ok result)
    {args : List Clif.Val} {state : Clif.State} (entered : ClifEntry function args state)
    (env : Clif.Env) (program : Clif.Program) (fuel : Nat) {values : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env program fuel state = .returned values final)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (tls : XTls Γ.F X) (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    {world otherWorld : Arm.ArmState} (memory : MRP Γ function c D state.frame.slots state.mem (world,otherWorld))
    (arguments : ArgsAtEntry Γ.F function.sig args world)
    (otherArguments : ArgsAtEntry Γ.F function.sig args otherWorld)
    (registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈ (locsOf function.sig).zip args → regVal otherWorld pin = regVal world pin) :
    ∃ regs,RunOkABI function result.code (pairSem (Backend.DeadCleanup.valueSem Γ.F fc X)) (MRP Γ function c D)
      state.frame.slots ⟨0,0,regs,(world,otherWorld)⟩ (.returned values final) := by
  obtain ⟨actual,event,run,scope,dominated,abi,size,events,schedule⟩ := original_two_load_schedule
  have resultEq := Except.ok.inj (run.symm.trans lowered)
  subst actual
  obtain ⟨firstPointer,secondPointer,first,second,argumentList,frame,callers,read0,read1,valuesEq,memoryEq⟩ :=
    original_returned_reads entered env program fuel returned
  have slots : state.frame.slots = [] := by rw [frame];rfl
  have execution := two_load_returned_paired_runOkABI (env := env) (program := program) lowered scope dominated abi size events schedule read0 read1 tls slot symbols
    (by simpa only [slots] using memory) (by simpa only [argumentList] using arguments)
    (by simpa only [argumentList] using otherArguments) (by simpa only [argumentList] using registers)
  refine ⟨entrySeed event.ctx (entry firstPointer secondPointer),?_⟩
  rw [slots,valuesEq,memoryEq]
  exact execution

end Backend.Stock.Proof.AcquireTwoLoadPrefix
