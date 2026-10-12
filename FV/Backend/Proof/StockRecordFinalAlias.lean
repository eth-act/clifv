import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.StockTraversalAliasConnection
import FV.Backend.Proof.StockTraversalRecordOrigin
import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.StockCoreScanOrigin

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Every recorded source definition's post-scan alias survives the complete
actual whole-driver traversal. SSA and real source mappings supply exclusion;
no caller-provided block or final alias-preservation fact is assumed. -/
theorem stock_lower_record_finalAliasEntry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (nonempty : f.blocks.length ≠ 0)
    (ssa : (valueDefs f).Nodup) {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {x key : Nat} {info : IInfo} (definition : result.ctx.insts[record.inst]? = some info)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int)) :
    (result.final.alias[key]?).join = (record.output.state.alias[key]?).join := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, step, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run eventMem
  obtain ⟨labelBound, suffixEq⟩ := stock_backward_suffix_split parts
  have lookup : result.order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos result.order.nodes label labelBound] at node
    simp only [Array.getElem?_eq_getElem labelBound, node]
  have valid := (stock_blockOrder_originals_nodup ordered nonempty).2
  have projected : bi ∈ stockOriginals result.order.nodes := by
    unfold stockOriginals
    apply List.mem_filterMap.mpr
    exact ⟨.original bi, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩
  have biBound := valid bi projected
  have firstBlock : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨original, st0, sourceBuild, spec, view⟩ := buildCtx_source build
  have firstRange := spec.ranges bi f.blocks[bi] firstBlock
  have initialBound : starting.state.alias.size ≤ result.initial.base.nextVreg ∧
      result.initial.base.nextVreg ≤ starting.state.base.nextVreg ∧
      starting.state.tryRegs = result.initial.tryRegs := by
    rw [initial]
    obtain ⟨original, st0, requests, _, _, allocated⟩ := buildCtx_allocation build
    have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) allocated
    change result.initial = _ at state
    rw [state]
    exact ⟨Nat.zero_le _, Nat.le_refl _, rfl⟩
  have beforeBound := stock_lowerNodes_allocationBounds build initialBound prefixRun
  have afterBound := stock_lowerNode_allocationBounds build beforeBound step
  obtain ⟨coreState, scanCtx, scanBlockId, scanTerm, scanIndices, scanRun⟩ :=
    stock_lowerBlockCore_scanOrigin coreRun
  rw [eventEq] at recordMem
  have index : record.inst ∈ core.scan.indices := by
    rw [← (runScans_spec scanRun).order]
    exact List.mem_map.mpr ⟨record, recordMem, rfl⟩
  rw [scanIndices] at index
  obtain ⟨lower, upper⟩ := stock_backward_indices_mem index
  have normalized : scanBlock
      { Driver.termCtx result.ctx (ranges[bi]!.2 - 1) data with
        tryRegs := result.initial.tryRegs[ranges[bi]!.2 - 1]! }
      bi (ranges[bi]!.2 - 1) core.scan.isBranch
      (((Array.range (ranges[bi]!.2 - ranges[bi]!.1)).map (ranges[bi]!.1 + ·)).reverse.toList)
      core.scan.input = .ok core.scan.output := by
    simpa only [scanCtx, scanBlockId, scanTerm, scanIndices, beforeBound.2.2] using scanRun
  have blockAlias := stock_scanBlock_backward_record_aliasEntry build ssa definition defines
    mapped data normalized recordMem rfl
  rw [suffixEq] at suffixRun
  have ownerRange : ranges[bi]? = some ranges[bi]! := by
    obtain ⟨bound, eq⟩ := Array.getElem?_eq_some_iff.mp firstRange
    rw [getElem!_pos ranges bi bound]
    exact Array.getElem?_eq_getElem bound
  have remaining := stock_lowerNodes_backward_aliasEntry build ssa definition defines mapped
    firstBlock ownerRange lower upper ordered nonempty lookup afterBound suffixRun
  rw [final, stateEq, coreState] at remaining
  exact remaining.trans blockAlias

/-- A source definition retained by actual whole-driver lowering has no alias
at its record input. Actual allocation, traversal order, core setup and SSA scan
frames derive this absence; no caller-supplied alias or edge-origin premise. -/
theorem stock_lower_record_inputNoAlias {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (nonempty : f.blocks.length ≠ 0)
    (ssa : (valueDefs f).Nodup) {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {x key : Nat} {info : IInfo} (definition : result.ctx.insts[record.inst]? = some info)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int)) :
    (record.input.alias[key]?).join = none := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, step, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run eventMem
  obtain ⟨labelBound, _⟩ := stock_backward_suffix_split parts
  have lookup : result.order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos result.order.nodes label labelBound] at node
    simp only [Array.getElem?_eq_getElem labelBound, node]
  have valid := (stock_blockOrder_originals_nodup ordered nonempty).2
  have projected : bi ∈ stockOriginals result.order.nodes := by
    unfold stockOriginals
    apply List.mem_filterMap.mpr
    exact ⟨.original bi, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩
  have biBound := valid bi projected
  have firstBlock : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨original, st0, sourceBuild, spec, view⟩ := buildCtx_source build
  have firstRange := spec.ranges bi f.blocks[bi] firstBlock
  have initialBound : starting.state.alias.size ≤ result.initial.base.nextVreg ∧
      result.initial.base.nextVreg ≤ starting.state.base.nextVreg ∧
      starting.state.tryRegs = result.initial.tryRegs := by
    rw [initial]
    obtain ⟨original, st0, requests, _, _, allocated⟩ := buildCtx_allocation build
    have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) allocated
    change result.initial = _ at state
    rw [state]
    exact ⟨Nat.zero_le _, Nat.le_refl _, rfl⟩
  have beforeBound := stock_lowerNodes_allocationBounds build initialBound prefixRun
  obtain ⟨coreState, scanCtx, scanBlockId, scanTerm, scanIndices, scanRun⟩ :=
    stock_lowerBlockCore_scanOrigin coreRun
  rw [eventEq] at recordMem
  have index : record.inst ∈ core.scan.indices := by
    rw [← (runScans_spec scanRun).order]
    exact List.mem_map.mpr ⟨record, recordMem, rfl⟩
  rw [scanIndices] at index
  obtain ⟨lower, upper⟩ := stock_backward_indices_mem index
  have normalized : scanBlock
      { Driver.termCtx result.ctx (ranges[bi]!.2 - 1) data with
        tryRegs := result.initial.tryRegs[ranges[bi]!.2 - 1]! }
      bi (ranges[bi]!.2 - 1) core.scan.isBranch
      (((Array.range (ranges[bi]!.2 - ranges[bi]!.1)).map (ranges[bi]!.1 + ·)).reverse.toList)
      core.scan.input = .ok core.scan.output := by
    simpa only [scanCtx, scanBlockId, scanTerm, scanIndices, beforeBound.2.2] using scanRun
  have ownerRange : ranges[bi]? = some ranges[bi]! := by
    obtain ⟨bound, eq⟩ := Array.getElem?_eq_some_iff.mp firstRange
    rw [getElem!_pos ranges bi bound]
    exact Array.getElem?_eq_getElem bound
  have prefixAlias := stock_lowerNodes_prefix_noAlias build ssa definition defines mapped
    firstBlock ownerRange lower upper ordered nonempty lookup parts initial prefixRun
  have coreAlias := stock_lowerBlockCore_scanAliasEntry build mapped beforeBound.2.2 coreRun
  have recordAlias := stock_scanBlock_record_inputAliasEntry build ssa definition defines mapped
    data (stock_scan_indices_nodup _ _) normalized recordMem rfl
  exact recordAlias.trans (coreAlias.trans prefixAlias)

/-- A fresh target installed by a recorded definition resolves in the final
alias array. Record-to-final transport and final capacity are derived from the
successful driver; the caller supplies only the local emission's alias/fresh facts. -/
theorem stock_lower_record_resultAlias_of_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (nonempty : f.blocks.length ≠ 0)
    (ssa : (valueDefs f).Nodup) {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {x key target : Nat} {info : IInfo} (definition : result.ctx.insts[record.inst]? = some info)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (entry : (record.output.state.alias[key]?).join = some target)
    (fresh : (scanState record.input record.inst).base.nextVreg ≤ target) :
    aliasNum result.final.alias key = target := by
  have finalEntry := (stock_lower_record_finalAliasEntry run nonempty ssa eventMem recordMem
    definition defines mapped).trans entry
  have bound := Nat.le_trans
    (stock_lower_blockScanAliasBounds run event eventMem record recordMem) fresh
  unfold aliasNum
  rw [chaseF, finalEntry]
  exact chaseF_none (by simp [Array.getElem?_eq_none bound]) _

private def finalAliasFunction : Clif.Function := {
  name := "record_final_alias"
  sig := { params := [], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{ id := 0, params := [], body := [⟨[0], .iconst .i64 9⟩], term := .ret [0] }] }
private def finalAliasInfo := infoOf finalAliasFunction ⟨[0], .iconst .i64 9⟩
private def finalAliasCall := Stock.lower finalAliasFunction
private theorem finalAlias_success : finalAliasCall.isOk = true := by decide +kernel
private def finalAliasBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx finalAliasFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem finalAlias_observed : finalAliasCall.toOption.map (fun r =>
    (r.ctx.valueReg? 0,
     r.blockScans.toList.any (fun event => event.output.records.any (fun record =>
       record.inst == 0 && decide ((record.output.state.alias[192]?).join = some 193) &&
         decide ((scanState record.input record.inst).base.nextVreg ≤ 193))))) =
    some (some (.vreg 192 .int), true) := by decide +kernel

/-- A successful whole-driver constant/return run records the actual definition
and installed192→193 alias. This inhabits every source/SSA/mapping premise and
applies the record-to-final transport theorem, rather than assuming its result. -/
theorem stock_lower_record_finalAliasEntry_witness :
    (valueDefs finalAliasFunction).Nodup ∧ finalAliasFunction.blocks.length ≠ 0 ∧
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord),
      Stock.lower finalAliasFunction = .ok result ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ record.inst = 0 ∧
      result.ctx.insts[record.inst]? = some finalAliasInfo ∧
      (0 : Nat) ∈ finalAliasInfo.results ∧ result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (record.output.state.alias[192]?).join = some 193 ∧
      (result.final.alias[192]?).join = (record.output.state.alias[192]?).join ∧
      (scanState record.input record.inst).base.nextVreg ≤ 193 ∧
      aliasNum result.final.alias 192 = 193 := by
  have ssa : (valueDefs finalAliasFunction).Nodup := by decide
  have nonempty : finalAliasFunction.blocks.length ≠ 0 := by decide
  refine ⟨ssa, nonempty, ?_⟩
  cases call : finalAliasCall with
  | error e =>
    have success := finalAlias_success
    simp only [call, Except.isOk] at success
    cases success
  | ok result =>
    have observation := finalAlias_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observation
    obtain ⟨event, eventMem, record, recordMem, inst, alias, fresh⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
        using observation.2 : ∃ event ∈ result.blockScans.toList,
          ∃ record ∈ event.output.records, record.inst = 0 ∧
            (record.output.state.alias[192]?).join = some 193 ∧
            (scanState record.input record.inst).base.nextVreg ≤ 193)
    have actual : Stock.lower finalAliasFunction = .ok result := call
    obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
      label, bi, data, core, build, _⟩ := stock_lower_blockScanOrigin actual eventMem
    have concrete : Stock.buildCtx finalAliasFunction = .ok finalAliasBuilt := rfl
    rw [concrete] at build
    have ctxEq : result.ctx = finalAliasBuilt.1 :=
      (congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.1) (Except.ok.inj build)).symm
    have definition : result.ctx.insts[record.inst]? = some finalAliasInfo := by
      rw [inst, ctxEq]; rfl
    have defines : (0 : Nat) ∈ finalAliasInfo.results := by decide
    exact ⟨result, event, record, actual, eventMem, recordMem, inst, definition, defines,
      observation.1, alias,
      stock_lower_record_finalAliasEntry actual nonempty ssa eventMem recordMem
        definition defines observation.1, fresh,
      stock_lower_record_resultAlias_of_record actual nonempty ssa eventMem recordMem
        definition defines observation.1 alias fresh⟩

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
/-- The inhabited whole-driver transport fixture also witnesses the new resolver
variant's local alias/fresh premises and final resolved result. -/
theorem stock_lower_record_resultAlias_of_record_witness :
    (valueDefs finalAliasFunction).Nodup ∧ finalAliasFunction.blocks.length ≠ 0 ∧
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord),
      Stock.lower finalAliasFunction = .ok result ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ record.inst = 0 ∧
      result.ctx.insts[record.inst]? = some finalAliasInfo ∧
      (0 : Nat) ∈ finalAliasInfo.results ∧ result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (record.output.state.alias[192]?).join = some 193 ∧
      (result.final.alias[192]?).join = (record.output.state.alias[192]?).join ∧
      (scanState record.input record.inst).base.nextVreg ≤ 193 ∧
      aliasNum result.final.alias 192 = 193 := stock_lower_record_finalAliasEntry_witness
/-- Successful whole-function lowering, a retained source definition and its
real mapping inhabit the alias-absence result. The same definition actually
installs a final alias, so this is not an empty-output fixture. -/
theorem stock_lower_record_inputNoAlias_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord),
      Stock.lower finalAliasFunction = .ok result ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ record.inst = 0 ∧
      result.ctx.insts[record.inst]? = some finalAliasInfo ∧
      (0 : Nat) ∈ finalAliasInfo.results ∧ result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (record.input.alias[192]?).join = none ∧
      (record.output.state.alias[192]?).join = some 193 := by
  obtain ⟨ssa, nonempty, result, event, record, run, eventMem, recordMem, inst,
    source, defines, mapped, entry, _⟩ := stock_lower_record_finalAliasEntry_witness
  exact ⟨result, event, record, run, eventMem, recordMem, inst, source, defines, mapped,
    stock_lower_record_inputNoAlias run nonempty ssa eventMem recordMem source defines mapped, entry⟩

end Backend.Stock.Proof
