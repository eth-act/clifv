import FV.Backend.Proof.StockAcquireVirtualReturn
import FV.Backend.Proof.StockAcquireSourceReturn
import FV.Backend.Proof.StockAcquireTrapBoundary
import FV.Backend.Proof.StockTermContract

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem pointer_argument {F : BitVec 64 → Prop} {args : List Clif.Val} {pointer : BitVec 64}
    {world : Arm.ArmState} (same : args = [⟨.i64,pointer⟩])
    (arguments : ArgsAtEntry F function.sig args world) : VHolds ⟨.i64,pointer⟩ (regVal world (.x 0)) := by
  apply arguments (.reg (.x 0)) ⟨.i64,pointer⟩
  rw [same]
  exact List.mem_singleton_self _

private theorem wide_prefix (raw : BitVec 8) :
    PrefixHold [⟨.i64,raw.setWidth 64⟩] [ofX (raw.setWidth 64)] := by
  refine ⟨Nat.le_refl 1,?_⟩
  intro j value output present located
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at present located
    subst value
    subst output
    change (ofX (raw.setWidth 64)).setWidth 64 = raw.setWidth 64
    simp only [ofX,BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by decide),BitVec.setWidth_eq]
  | succ j => simp at present

/-- The actual original source entry derives complete return refinement internally.
The original arguments and memory have no additional acceptance guard. -/
theorem original_returns {result : Stock.Result} (lowered : Stock.lower function = .ok result)
    {args : List Clif.Val} {state : Clif.State} (entered : ClifEntry function args state)
    (env : Clif.Env) (program : Clif.Program) (fuel : Nat) {values : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env program fuel state = .returned values final)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Backend.Proof.Sem} {MR : MemRelT}
    (refines : Refines F isem) (driver : DriverSem isem) (stable : MRStable F MR)
    (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR state.frame.slots state.mem world)
    (arguments : ArgsAtEntry F function.sig args world) :
    ∃ regs,RunOkABI function result.code isem MR state.frame.slots ⟨0,0,regs,world⟩ (.returned values final) := by
  obtain ⟨pointer,raw,argumentList,read,sourceValues,sourceMemory⟩ :=
    entry_returned_read entered env program fuel returned
  have slots : state.frame.slots = [] := by simpa [function] using entered.slotIds
  let regs : Nat → CV := fun _ => 0
  obtain ⟨next,executed,kept⟩ := lowered_byte_return lowered refines driver stable memorySem memoryOk
    pointer state.mem raw read regs world (by simpa only [slots] using memory)
    (pointer_argument argumentList arguments)
  refine ⟨regs,[(.vreg 195 .int,.x 0)],[ofX (raw.setWidth 64)],next,state.mem,executed,
    (by rfl),rfl,?_,?_,?_⟩
  · rw [sourceValues]
    exact wide_prefix raw
  · simpa only [slots] using kept
  · simpa only [slots,List.map_nil] using sourceMemory

/-- Every first source memory trap reaches its actual deferred acquire.
The existing MapFaults condition supplies its precise unmapped byte. -/
theorem original_traps {result : Stock.Result} (lowered : Stock.lower function = .ok result)
    {args : List Clif.Val} {state : Clif.State} (entered : ClifEntry function args state)
    (env : Clif.Env) (program : Clif.Program) (fuel : Nat) (code : Clif.TrapCode)
    (trapped : Clif.runLoop env program fuel state = .trapped code)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {F : BitVec 64 → Prop}
    (mp : ArmFault.MemMap) (faults : MapFaults mp env program state)
    {world : Arm.ArmState} (arguments : ArgsAtEntry F function.sig args world) :
    ∃ regs,VAcquireTrapFrom result.code isem ⟨0,0,regs,world⟩ code
      (fun address bytes => ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) := by
  obtain ⟨pointer,argumentList,frame,callers⟩ := original_entry_normal_form entered
  have same : (⟨entry pointer,[],state.mem⟩ : Clif.State) = state := by cases state; simp_all
  let regs : Nat → CV := fun _ => 0
  refine ⟨regs,?_⟩
  exact lowered_byte_access_fault lowered driver env program pointer state.mem fuel code
    (by rwa [same]) mp (by rwa [same]) regs world (pointer_argument argumentList arguments)

end Backend.Stock.Proof.Acquire810
