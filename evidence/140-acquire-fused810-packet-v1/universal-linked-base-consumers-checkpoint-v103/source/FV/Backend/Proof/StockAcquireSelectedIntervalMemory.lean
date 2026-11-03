import FV.Backend.Proof.StockAcquireSelectedStatementFrames

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Successful original source slices between the selected producer and consumer preserve the whole memory. -/
theorem stock_lower_acquire_successful_interval_memory {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (value producer : Nat) (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      event.ctx.defInst? value = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      ∀ (bi start count : Nat) (block : Clif.Block),f.blocks[bi]? = some block →
        start+count ≤ block.body.length → producer ≤ blockStart f bi+start →
        blockStart f bi+(start+count) ≤ record.inst →
        ∀ (env : Clif.Env) (p : Clif.Program) (before after : Clif.Frame × Clif.Mem),
          SourceSteps (SourceInstResult env p event.ctx)
            ((List.range count).map (fun offset => blockStart f bi+(start+offset))) before after →
          after.2 = before.2 := by
  obtain ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,
    integer,little,frames⟩ := stock_lower_acquire_between_statement_read_frames run scope events records recorded emitted selectedId
  refine ⟨value,producer,info,ty,flags,pointer,defined,installed,source,integer,little,?_⟩
  intro bi start count block blockAt inside lower upper env p before after steps
  apply source_steps_read_memory steps
  intro slot member
  obtain ⟨offset,inRange,equal⟩ := List.mem_map.mp member
  subst slot
  have offsetBound := List.mem_range.mp inRange
  have statementBound : start+offset < block.body.length := by omega
  have statement : block.body[start+offset]? = some block.body[start+offset] := by simp [statementBound]
  exact frames bi (start+offset) block block.body[start+offset] blockAt statement (by omega) (by omega)

end Backend.Stock.Proof.Acquire810
