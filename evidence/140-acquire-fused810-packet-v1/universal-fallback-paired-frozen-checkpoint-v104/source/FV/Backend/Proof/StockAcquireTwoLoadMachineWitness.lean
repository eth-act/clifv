import FV.Backend.Proof.StockAcquireTwoLoadMachineW

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- The original admitted two-load function supplies lowering, entry-event identity, and schedule internally.
The physical transfer retains the existing pipeline, ABI, W, memory, and source execution contracts. -/
-- witness: native_decide
theorem original_two_load_prepared_machine_fault :
    ∃ (result : Result) (event : BlockScanEvent),Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ event ∈ result.blockScans.toList ∧
      ∀ {prepared : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    {cleanup : Bool} (preparedCheck : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true)
    {args : List Clif.Val} {cm : Clif.Mem} {frame : Clif.Frame} (entered : SourceEntry function args frame)
    {env : Clif.Env} {program : Clif.Program} {atFault : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (source : SourceInstResult env program event.ctx 0 (frame,cm) atFault)
    (failed : SourceInstFault env program event.ctx 1 atFault code)
    {syms : String → Option Nat}
    (symbols : ∀ name address,syms name = some address → X.sym name 0 = BitVec.ofNat 64 address)
    {MR : MemRelT} (stable : MRStable (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) MR)
    (memoryOk : MemRelOk (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) af.slotBase syms function MR)
    (memory : MR frame.slots cm world) (arguments : ArgsAtEntry (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) function.sig args world)
    (callers : List (Clif.Frame × List Clif.ValueId))
    (faults : MapFaults mp env program ⟨frame,callers,cm⟩),
    ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n initial) ∧
      ∀ j < n,actGoodXW prepared rf af fa fb base initial X H K G (GotV prepared) (runX (ArmStepX X H fa) j initial) := by
  obtain ⟨result,event,run,scope,dominated,abi,size,events,schedule⟩ := original_two_load_schedule
  refine ⟨result,event,run,scope,dominated,events,?_⟩
  intro prepared rf af fa fb k checked allocated emitted layout X H K G covered base ra initial called stack globals callees tryCallees tls
    world bodyEntry mp cleanup preparedCheck args cm frame entered env program atFault code source failed syms symbols MR stable memoryOk memory arguments callers faults
  exact two_load_prepared_machine_fault checked allocated emitted layout covered called stack globals callees tryCallees tls
    bodyEntry mp run scope dominated size events schedule preparedCheck entered source failed symbols stable memoryOk memory arguments callers faults

end Backend.Stock.Proof.AcquireTwoLoadPrefix
