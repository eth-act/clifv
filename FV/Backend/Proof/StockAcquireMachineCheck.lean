import FV.Backend.Proof.StockAcquireMachineBoundary

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual allocator check discharges the entry invariant for any initial virtual file. -/
theorem regLevel_acquire_fault_boundary_worldX_value {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    (shapes : ∀ (b : Nat) (block : VBlock) (j : Nat) (inst : MInst),
      vc.blocks[b]? = some block → block.insts[j]? = some inst →
      ∀ (uses : List CV) (world : Arm.ArmState) (code : Clif.TrapCode) (address : BitVec 64) (bytes : Nat),
        AcquireAt inst uses world code address bytes → (∃ d pointer flags,inst = .loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags))
    (mp : ArmFault.MemMap) :
    ∀ code (property : BitVec 64 → Nat → Prop),
      (∀ address bytes,property address bytes → ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) →
      VAcquireBoundaryFrom vc
        (valueSemV gv (frameWG K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af G initial)
          ⟨fa.k,af.slotBase⟩ X) ⟨0,0,regs,world⟩ code property →
      ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n initial) ∧
        ∀ j < n,actGoodX vc rf af fa fb base initial X H K G gv (runX (ArmStepX X H fa) j initial) := by
  obtain ⟨cc,ins,accepted⟩ := checked_of_checkAlloc checked
  obtain ⟨a0,atEntry,entryLe⟩ := accepted.at
  obtain ⟨values,executes⟩ := regLevel_acquire_fault_boundary_world_value atEntry (entryOk_of_le entryLe)
    allocated emitted layout covered called stack globals callees tryCallees tls bodyEntry
    (fun _ => regs) (fun _ => Inv_mono entryLe Inv_entryState) shapes mp
  exact executes

end Backend.Stock.Proof.Acquire810
