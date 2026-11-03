import FV.Backend.Proof.StockAcquireConstantFreshRun

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual constant code executes at a fixed earlier source fault point.
The original source frame and memory remain fixed. No later source step is assumed. -/
theorem stock_lower_constant_frozen_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {bi j : Nat} {block : Clif.Block} {statement : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statementAt : block.body[j]? = some statement)
    (current : record.inst = blockStart f bi+j)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i,isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1))) = isem i)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {program : Clif.Program}
    {frontier : ReadEffectFrontier event.ctx env program} {point : SourcePoint}
    (order : point.1 ≤ j) {regs : Nat → CV} {world : Arm.ArmState}
    (related : PendingGuardedScanRel f result event.ctx bi env program MR frontier.history
      record.output.state point regs world)
    (pending : PendingReadMarks frontier record.output.state)
    (retiredMarks : RetiredReadUnmarked frontier record.output.state)
    (retiredValues : RetiredUndemanded frontier record.output.state) :
    ∃ nextRegs nextWorld,
      seqRun isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        regs world = some (.fall nextRegs nextWorld) ∧
      SameWorld F nextWorld world ∧
      PendingGuardedScanRel f result event.ctx bi env program MR frontier.history record.input point nextRegs nextWorld ∧
      PendingReadMarks frontier record.input ∧ RetiredReadUnmarked frontier record.input ∧
      RetiredUndemanded frontier record.input := by
  obtain ⟨definitions,execute⟩ := stock_lower_constant_fresh_run run scope events records source clif results
    mapped recorded emitted refines semantics
  obtain ⟨nextRegs,runCode⟩ := execute regs
  obtain ⟨nextWorld,executed,same⟩ := runCode world
  have post := stock_lower_pending_frozen_source_frame run scope dominated events records blockAt statementAt
    current recorded emitted stable order related definitions executed same
  have marks := stock_lower_constant_empty_marks run scope events records source clif results mapped
    recorded emitted refines
  have sunkEq : record.output.state.sunk = record.input.sunk := by
    simpa only [List.foldl_nil,scanState_sunk] using marks.sunk_exact
  refine ⟨nextRegs,nextWorld,executed,same,post,?_,?_,?_⟩
  · intro captured member
    rw [← sunkEq]
    exact pending captured member
  · intro captured member
    rw [← sunkEq]
    exact retiredMarks captured member
  · exact retired_undemanded_of_le retiredValues
      (stock_lower_record_demand_mono run events records recorded emitted)

end Backend.Stock.Proof.Acquire810
