import FV.Backend.Proof.StockAcquireMachineShape

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual allocator check discharges the entry invariant for any initial virtual file. -/
theorem regLevel_acquire_fault_covered_worldX_valueW {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (checked : checkAlloc vc rf = .ok ()) (allocated : lowerRFunc vc rf = .ok af)
    (emitted : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vc)
    {base ra : BitVec 64} {initial : Arm.ArmState} (called : AbiCall fb base ra initial)
    (stack : StackAvail K af initial)
    (globals : ∀ a,G a → ¬ StackBelow (frameDrop af+K) (spv initial) a)
    (callees : CalleeOkG (frameWG K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af G initial)
      K G initial (CallAt fa base) X H vc.CallSite gv)
    (tryCallees : vc.hasTryCall = true →
      CalleeTryOkG (frameWG K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af G initial)
        K G initial (CallAt fa base) X H vc.TrySite gv)
    (tls : vc.hasTls = true →
      TlsOk (frameWG K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af G initial) K X H)
    {world : Arm.ArmState}
    (bodyEntry : BodyEntryW (frameWG K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af G initial)
      vc.EntryArg af initial world)
    (regs : Nat → CV)
    (mp : ArmFault.MemMap) :
    ∀ code (property : BitVec 64 → Nat → Prop),
      (∀ address bytes,property address bytes → ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) →
      VAcquireBoundaryFrom vc
        (valueSemV gv (frameWG K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af G initial)
          ⟨fa.k,af.slotBase⟩ X) ⟨0,0,regs,world⟩ code property →
      ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n initial) ∧
        ∀ j < n,actGoodXW vc rf af fa fb base initial X H K G gv (runX (ArmStepX X H fa) j initial) := by
  exact regLevel_acquire_fault_worldX_valueW checked allocated emitted layout covered called stack globals callees tryCallees tls bodyEntry regs
    (fun b block j inst found located uses world code address bytes access => acquire_shape_of_forms_covered covered found located access) mp

end Backend.Stock.Proof.Acquire810
