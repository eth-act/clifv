import FV.Backend.Proof.StockAcquirePairedReadFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual ABI execution constructs the full shared invariant without an external frontier or history. -/
theorem stock_lower_entry_paired_frontier_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    {left right : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (left,right))
    (arguments : ArgsAtEntry Γ.F f.sig args left) (otherArguments : ArgsAtEntry Γ.F f.sig args right)
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal right pin = regVal left pin) :
    ∃ (event : BlockScanEvent) (block : VBlock) (prelude after : Array MInst) (regs : Nat → CV),
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧ result.code.blocks[0]? = some block ∧
      block.insts = prelude++event.output.code.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++after ∧
      seqRun (pairSem (Backend.DeadCleanup.valueSem Γ.F fc X)) prelude.toList (entrySeed event.ctx fr) (left,right) =
        some (.fall regs (left,right)) ∧
      ∀ (env : Clif.Env) (program : Clif.Program),
        Nonempty (PairedReadFrontierAt f result event env program (RelW Γ f c) (fun a => Γ.F a ∨ D a)
          (fr,cm) [] event.output.state (0,fr,cm) regs (left,right)) := by
  obtain ⟨event,block,prelude,after,regs,events,entryBlock,located,pieces,execution,initial⟩ :=
    E2E.StockAcquirePair.stock_lower_entry_paired_pending_frontier run scope dominated entered registerOnly slot symbols
      memory arguments otherArguments registers
  refine ⟨event,block,prelude,after,regs,events,entryBlock,located,pieces,execution,?_⟩
  intro env program
  obtain ⟨history,pending,retiredMarks,retiredValues,leftHeld,rightHeld⟩ := initial env program
  exact ⟨⟨ReadEffectFrontier.empty event.ctx env program,history,(by intro captured member;cases member),
    pending,retiredMarks,retiredValues,leftHeld,rightHeld,SameWorld.mono (zof_sub cm) memory.2.2⟩⟩

end Backend.Stock.Proof.Acquire810
