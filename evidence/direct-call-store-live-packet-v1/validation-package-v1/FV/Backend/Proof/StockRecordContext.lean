import FV.Backend.Proof.StockTraversalRecordOrigin
import FV.Backend.Proof.StockCoreScanOrigin
import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.StockSourceOrder
import FV.Backend.Proof.LowerContract
import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.StockDFG

/-! The scan context of an actual retained record: the proved source context with only its
terminator placeholder and exception reservations changed (`stock_lower_record_context`). Its own
module, so that its users need not wait for the constant value transfer of
`StockConstantRecordValues`. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem event_context {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ ti data trs, event.ctx = {Driver.termCtx result.ctx ti data with tryRegs := trs} := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq]
  exact ⟨_, _, _, (stock_lowerBlockCore_scanOrigin coreRun).2.1⟩

private theorem event_map {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (x : Nat) :
    event.ctx.valueReg? x = result.ctx.valueReg? x := by
  obtain ⟨ti, data, trs, context⟩ := event_context run events
  rw [context]
  rfl

private theorem event_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[i]? = some info) (clif : info.clif = some inst) :
    result.ctx.insts[i]? = some info := by
  obtain ⟨ti, data, trs, context⟩ := event_context run events
  rw [context] at source
  change (Driver.termCtx result.ctx ti data).insts[i]? = some info at source
  by_cases equal : i = ti
  · subst i
    have self : (Driver.termCtx result.ctx ti data).insts[ti]? =
        (result.ctx.insts[ti]?).map (fun _ => ⟨data, [], [], none⟩) := by
      by_cases bound : ti < result.ctx.insts.size
      · simp [Driver.termCtx, Array.getElem?_setIfInBounds, bound, Array.getElem?_eq_getElem bound]
      · simp [Driver.termCtx, Array.getElem?_setIfInBounds, bound,
          Array.getElem?_eq_none (Nat.le_of_not_lt bound)]
    rw [self] at source
    cases original : result.ctx.insts[ti]? <;> simp only [original, Option.map_none, Option.map_some] at source
    · cases source
    · cases source
      cases clif
  · rw [termCtx_insts_ne equal] at source
    exact source

/-- An actual original-node scan uses the proved source context with only its
terminator placeholder and exception reservations changed. Source slots and
mapped source registers are the actual whole-run slots and registers. -/
theorem stock_lower_record_context {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    MappedCtxInv f event.ctx ∧
      (∀ x, event.ctx.valueReg? x = result.ctx.valueReg? x) ∧
      (∀ (i : Nat) (info : IInfo) (inst : Clif.Inst), event.ctx.insts[i]? = some info → info.clif = some inst →
        result.ctx.insts[i]? = some info) := by
  refine ⟨?_, event_map run events, fun _ _ _ => event_source run events⟩
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have nonempty : f.blocks.length ≠ 0 := (fun h => scope.nonempty (List.length_eq_zero_iff.mp h))
  have labelBound := (stock_backward_suffix_split parts).1
  have lookup : result.order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos result.order.nodes label labelBound] at node
    simp only [Array.getElem?_eq_getElem labelBound, node]
  have valid := (stock_blockOrder_originals_nodup ordered nonempty).2
  have projected : bi ∈ stockOriginals result.order.nodes := by
    unfold stockOriginals
    apply List.mem_filterMap.mpr
    exact ⟨.original bi, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩
  have biBound := valid bi projected
  have block : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨original, oldState, oldBuild, spec, view⟩ := buildCtx_source build
  have range := spec.ranges bi f.blocks[bi] block
  have rangeValue : ranges[bi]! =
      (blockStart f bi, blockStart f bi + f.blocks[bi].body.length + 1) := by
    simp only [getElem!_def, range]
  have placeholder : result.ctx.insts[ranges[bi]!.2 - 1]? =
      some ⟨.op .unit, [], [], none⟩ := by
    rw [rangeValue]
    have terminal : blockStart f bi + f.blocks[bi].body.length + 1 - 1 =
        blockStart f bi + f.blocks[bi].body.length := by omega
    rw [terminal, view.insts]
    exact spec.facts.term bi f.blocks[bi] block
  rw [eventEq, (stock_lowerBlockCore_scanOrigin coreRun).2.1]
  exact ((buildCtx_mappedInv scope build).termCtx placeholder data).withTryRegs _

end Backend.Stock.Proof
