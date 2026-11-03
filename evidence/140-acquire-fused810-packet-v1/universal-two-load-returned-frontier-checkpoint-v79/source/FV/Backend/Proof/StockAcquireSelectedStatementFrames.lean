import FV.Backend.Proof.StockAcquireOriginalStatementView

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The complete original statement interval derives read frames for effects and uncolored instructions. -/
theorem stock_lower_acquire_between_statement_read_frames {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (value producer : Nat)
      (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      event.ctx.defInst? value = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      ∀ (bi j : Nat) (block : Clif.Block) (stm : Clif.Stmt),f.blocks[bi]? = some block →
        block.body[j]? = some stm → producer ≤ blockStart f bi+j → blockStart f bi+j < record.inst →
        SourceReadFrame event.ctx (blockStart f bi+j) := by
  obtain ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,
    integer,little,crossed⟩ := stock_lower_acquire_between_source_read_frames run scope events records recorded emitted selectedId
  have view := stock_lower_event_build_source_slots run scope events built
  refine ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,integer,little,?_⟩
  intro bi j block stm blockAt statement lower upper
  cases effect : Stock.colored stm.inst with
  | true =>
    exact crossed _ (original_colored_statement_event built blockAt statement effect) lower upper
  | false =>
    obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of built).facts.stmt bi block j stm blockAt statement
    exact uncolored_source_read_frame (view _ actualInfo stm.inst present actualSource) actualSource effect

end Backend.Stock.Proof.Acquire810
