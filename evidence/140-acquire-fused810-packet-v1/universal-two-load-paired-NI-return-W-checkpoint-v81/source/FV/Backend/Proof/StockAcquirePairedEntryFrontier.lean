import FV.Backend.Proof.StockAcquireEntryFrontier
import FV.E2E.StockMemoryPairedEntryValue

namespace E2E.StockAcquirePair
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual register-only ABI entry constructs both pending states and one complete shared register file. -/
theorem stock_lower_entry_paired_pending_frontier {f : Clif.Function} {result : Result}
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
        SourceReadCaptures event.ctx env program [] (fr,cm) (fr,cm) (ReadEffectFrontier.empty event.ctx env program).history ∧
        PendingReadMarks (ReadEffectFrontier.empty event.ctx env program) event.output.state ∧
        RetiredReadUnmarked (ReadEffectFrontier.empty event.ctx env program) event.output.state ∧
        RetiredUndemanded (ReadEffectFrontier.empty event.ctx env program) event.output.state ∧
        PendingGuardedScanRel f result event.ctx event.block env program (RelW Γ f c)
          (ReadEffectFrontier.empty event.ctx env program).history event.output.state (0,fr,cm) regs left ∧
        PendingGuardedScanRel f result event.ctx event.block env program (RelW Γ f c)
          (ReadEffectFrontier.empty event.ctx env program).history event.output.state (0,fr,cm) regs right := by
  obtain ⟨event,block,prelude,body,regs,events,entryBlock,placed,pieces,execution,values,after,code⟩ :=
    StockMemory.stock_lower_entry_prelude_paired_frame_value run scope dominated entered registerOnly slot symbols memory
      arguments otherArguments registers
  refine ⟨event,block,prelude,after,regs,events,entryBlock,placed,?_,execution,?_⟩
  · rw [pieces,code,Array.append_assoc]
  · intro env program
    have leftHeld := stock_lower_entered_values_guarded_frame run scope dominated events entered values event.output.state left memory.1
    have rightHeld := stock_lower_entered_values_guarded_frame run scope dominated events entered values event.output.state right memory.2.1
    refine ⟨.nil (fr,cm),?_,?_,?_,pending_guarded_nil.mpr leftHeld,pending_guarded_nil.mpr rightHeld⟩
    all_goals intro captured member;cases member

end E2E.StockAcquirePair
