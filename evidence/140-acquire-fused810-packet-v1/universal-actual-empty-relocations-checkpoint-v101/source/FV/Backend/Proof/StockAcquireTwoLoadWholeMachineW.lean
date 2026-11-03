import FV.Backend.Proof.StockAcquireTwoLoadWholeBoundary
import FV.Backend.Proof.StockAcquireMachineCoveredW
import FV.Backend.Proof.StockAcquireStage

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 Backend.DeadCleanup E2E
set_option autoImplicit false
set_option Elab.async false

/-- Both original first-fault branches derive the actual physical trap site and every preceding W state.
The public helper accepts the original source trap, with no branch-only read certificate. -/
theorem two_load_whole_source_machine_fault {prepared : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (checked : checkAlloc prepared rf = .ok ()) (allocated : lowerRFunc prepared rf = .ok af)
    (emitted : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop}
    (covered : FormsCovered ⟨fa.k,af.slotBase⟩ prepared)
    {base ra : BitVec 64} {initial : Arm.ArmState} (called : AbiCall fb base ra initial)
    (stack : StackAvail K af initial)
    (globals : ∀ a,G a → ¬ StackBelow (frameDrop af+K) (spv initial) a)
    (callees : CalleeOkG (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial)
      K G initial (CallAt fa base) X H prepared.CallSite (GotV prepared))
    (tryCallees : prepared.hasTryCall = true →
      CalleeTryOkG (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial)
        K G initial (CallAt fa base) X H prepared.TrySite (GotV prepared))
    (tls : prepared.hasTls = true →
      TlsOk (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) K X H)
    {world : Arm.ArmState}
    (bodyEntry : BodyEntryW (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial)
      prepared.EntryArg af initial world)
    (mp : ArmFault.MemMap)
    {result : Result} (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {cleanup : Bool} (preparedCheck : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true)
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env program fuel ⟨entry firstPointer secondPointer,[],cm⟩ = .trapped code)
    {syms : String → Option Nat}
    (symbols : ∀ name address,syms name = some address → X.sym name 0 = BitVec.ofNat 64 address)
    {MR : MemRelT} (stable : MRStable (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) MR)
    (memoryOk : MemRelOk (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) af.slotBase syms function MR)
    (memory : MR (entry firstPointer secondPointer).slots cm world) (arguments : ArgsAtEntry (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world)
    (callers : List (Clif.Frame × List Clif.ValueId))
    (faults : MapFaults mp env program ⟨(entry firstPointer secondPointer),callers,cm⟩) :
    ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n initial) ∧
      ∀ j < n,actGoodXW prepared rf af fa fb base initial X H K G (GotV prepared) (runX (ArmStepX X H fa) j initial) := by
  let F := frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial
  have raw := two_load_whole_source_fault_boundary run scope dominated size events schedule trapped
    (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X) (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X rfl symbols)
    stable memoryOk memory arguments callers mp faults
  have staged := acquireTrap_stage preparedCheck raw
  have boundary := acquireTrap_gotV_value staged
  exact regLevel_acquire_fault_covered_worldX_valueW checked allocated emitted layout covered called stack globals callees tryCallees tls
    bodyEntry (entrySeed event.ctx (entry firstPointer secondPointer)) mp code _ (fun address bytes allowed => allowed) boundary

end Backend.Stock.Proof.AcquireTwoLoadPrefix
