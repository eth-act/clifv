import FV.Backend.Proof.StockAcquireEntryFrontier
import FV.Backend.Proof.StockAcquireProgramEntryPrefixFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual successful history before the faulting producer supplies its pointer binding and fault address.
No successful read, consumer source step, or completed-frontier certificate is required. -/
theorem stock_lower_acquire_fault_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest label index : Nat) (block : VBlock),
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] ∧
      ∀ (env : Clif.Env) (program : Clif.Program) (args : List Clif.Val) (initial : Clif.State)
        (atFault : Clif.Frame × Clif.Mem) (mp : ArmFault.MemMap) (code : Clif.TrapCode),
        SourceEntry f args initial.frame → initial.frame.body = R.block.body →
        MapFaults mp env program initial →
        SourceInstFault env program event.ctx R.producer atFault code →
        ∀ (MR : MemRelT) (frontier : ReadEffectFrontier event.ctx env program) (regs : Nat → CV) (world : Arm.ArmState),
          SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.producerIndex)
            (initial.frame,initial.mem) atFault frontier.history →
          PendingReadMarks frontier record.output.state → RetiredUndemanded frontier record.output.state →
          PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state
            (R.producerIndex,atFault) regs world →
          frontier.pending = [] ∧
          GuardedScanRel f result event.ctx event.block MR record.output.state (R.producerIndex,atFault) regs world ∧
          ∃ address bytes,AcquireAt (block.insts[index]!) [regs (aliasNum result.final.alias pointerReg)] world code address bytes ∧
            ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none := by
  obtain ⟨R,pointerReg,dest,label,index,block,found,segment,transfer⟩ :=
    stock_lower_acquire_program_entry_prefix_fault run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,label,index,block,found,segment,?_⟩
  intro env program args initial atFault mp code entered body faults failed MR frontier regs world history pending retired prior
  have empty := stock_lower_acquire_fault_pending_empty run scope events records recorded emitted selectedId R history pending
  have guarded := stock_lower_acquire_fault_guarded_recovery run scope events records recorded emitted selectedId R
    history pending retired prior
  have retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records := by
    intro captured member
    exact List.mem_reverse.mp (List.mem_of_mem_take (history.record_membership captured member))
  have held := stock_lower_acquire_pending_pointer_at_prefix run scope dominated events records recorded emitted selectedId R
    (Nat.le_refl _) retained pending retired prior.2.2.2
  obtain ⟨sourceBlock,blockAt,indices⟩ := stock_lower_event_forward_source_indices run scope events
  have blockEq := Option.some.inj (blockAt.symm.trans R.blockAt)
  subst sourceBlock
  have inside := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have prefixIndices : (event.output.records.reverse.take R.producerIndex).map (·.inst) =
      List.range' (blockStart f event.block) R.producerIndex := by
    rw [List.map_take,indices]
    exact List.take_range'_of_length_ge (by omega)
  have executed := history.source_steps
  rw [prefixIndices] at executed
  exact ⟨empty,guarded,transfer env program args initial atFault mp code entered body faults executed failed regs world held⟩

end Backend.Stock.Proof.Acquire810
