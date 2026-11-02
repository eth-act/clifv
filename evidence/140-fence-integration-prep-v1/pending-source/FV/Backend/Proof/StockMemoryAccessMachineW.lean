import FV.Backend.Proof.StockMemoryAccessRegisterLevel
import FV.E2E.DeadCleanupRealizesW
import FV.Backend.Proof.StockMemoryAccessTrace

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The existing ABI entry and concrete realizer derive the actual ordinary memory-fault trace. -/
theorem regLevel_access_fault_world_valueW {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (checked : CheckedAt vc rf cc ins a0) (entryOk : EntryOk a0) (allocated : lowerRFunc vc rf = .ok af)
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
    (regs : (Loc → CV) → Nat → CV)
    (bindings : ∀ values,Inv ckeep a0 values (regs values) (fun r => values (.reg r)))
    (shapes : ∀ (b : Nat) (block : VBlock) (j : Nat) (inst : MInst),
      vc.blocks[b]? = some block → block.insts[j]? = some inst →
      ∀ (uses : List CV) (world : Arm.ArmState) (code : Clif.TrapCode) (address : BitVec 64) (bytes : Nat),
        AccessAt af.slotBase inst uses world code address bytes → OrdinaryAccessShape inst)
    (mp : ArmFault.MemMap) :
    ∃ values : Loc → CV,∀ code (property : BitVec 64 → Nat → Prop),
      (∀ address bytes,property address bytes → ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) →
      VAccessTrapFrom af.slotBase vc
        (valueSemV gv (frameWG K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af G initial)
          ⟨fa.k,af.slotBase⟩ X) ⟨0,0,regs values,world⟩ code property →
      ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n initial) ∧
        ∀ j < n,actGoodXW vc rf af fa fb base initial X H K G gv (runX (ArmStepX X H fa) j initial) := by
  obtain ⟨labels,labelOffsets⟩ := FnAsm.layout_labelOffsets layout
  obtain ⟨body,psF,bodyCode,other,sameK⟩ := emitFunc_ok emitted
  subst sameK
  let R : RL := ⟨vc,rf,af,fa,fb,labels,base,initial,X,H,psF,K,G,gv⟩
  have wellFormed : R.Wf := ⟨⟨cc,ins,a0,checked,entryOk⟩,allocated,emitted,layout,labelOffsets,
    by show 4*fb.words.size ≤ 2^64; have := called.fits; omega,
    stack,⟨body,bodyCode⟩,called.program,globals⟩
  obtain ⟨n0,good0,related0,invariant0,other⟩ := q_initW wellFormed called bodyEntry
  let values := locVal R.fr (iterN R.step n0 initial)
  refine ⟨values,?_⟩
  intro code property unmapped fault
  have realization := realizes_value_allW wellFormed callees tryCallees tls covered
  obtain ⟨n,site,good⟩ := access_register_level_boundary_trace wellFormed checked realization values
    (regs values) world (bindings values) (.inl ⟨related0,invariant0⟩) fault
    (fun b block j inst found located uses world address bytes access =>
      shapes b block j inst found located uses world code address bytes access) mp unmapped
  refine ⟨n0+n,?_,?_⟩
  · rw [runX_eq,iterN_add]
    exact site
  · intro j bound
    rw [runX_eq]
    exact (trace_add good0 good j bound).act

end Backend.Stock.Proof.MemoryFaults
