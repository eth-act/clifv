import FV.Backend.Proof.StockAcquireTwoLoadWholeMachineW

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- Original admitted lowering and every whole-source trap derive the physical W fault prefix for either load.
The original pipeline, ABI, body-entry, and memory contracts remain exact. -/
-- witness: native_decide
theorem original_two_load_whole_source_machine_fault :
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
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env program fuel ⟨entry firstPointer secondPointer,[],cm⟩ = .trapped code)
    {syms : String → Option Nat}
    (symbols : ∀ name address,syms name = some address → X.sym name 0 = BitVec.ofNat 64 address)
    {MR : MemRelT} (stable : MRStable (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) MR)
    (memoryOk : MemRelOk (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) af.slotBase syms function MR)
    (memory : MR (entry firstPointer secondPointer).slots cm world) (arguments : ArgsAtEntry (frameWG K (RAFrame.compute prepared rf).intBase (RAFrame.compute prepared rf).size af G initial) function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world)
    (callers : List (Clif.Frame × List Clif.ValueId))
    (faults : MapFaults mp env program ⟨(entry firstPointer secondPointer),callers,cm⟩),
    ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n initial) ∧
      ∀ j < n,actGoodXW prepared rf af fa fb base initial X H K G (GotV prepared) (runX (ArmStepX X H fa) j initial) := by
  obtain ⟨result,event,run,scope,dominated,abi,size,events,schedule⟩ := original_two_load_schedule
  refine ⟨result,event,run,scope,dominated,events,?_⟩
  intro prepared rf af fa fb k checked allocated emitted layout X H K G covered base ra initial called stack globals callees tryCallees tls
    world bodyEntry mp cleanup preparedCheck env program firstPointer secondPointer cm fuel code trapped syms symbols MR stable memoryOk memory arguments callers faults
  exact two_load_whole_source_machine_fault checked allocated emitted layout covered called stack globals callees tryCallees tls
    bodyEntry mp run scope dominated size events schedule preparedCheck trapped symbols stable memoryOk memory arguments callers faults

end Backend.Stock.Proof.AcquireTwoLoadPrefix
