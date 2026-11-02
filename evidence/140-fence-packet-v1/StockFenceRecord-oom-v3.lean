import FV.Backend.Proof.StockFenceUnsunk
import FV.Backend.Proof.StockFenceRoot
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.IselCtlRuleIds

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

private theorem record_execute {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) :
    scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ := stock_lower_blockScanOrigin run events
  rw [eventEq] at records ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record records

/-- An original source instruction differs from the installed terminator slot. -/
private theorem source_not_term {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {i : Nat} {info : IInfo}
    {inst : Clif.Inst} (found : event.ctx.insts[i]? = some info)
    (source : info.clif = some inst) : i ≠ event.termInst := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  intro same
  rw [same,eventEq,origin.2.1,origin.2.2.2.1] at found
  change (termCtx result.ctx (ranges[bi]!.2-1) data).insts[ranges[bi]!.2-1]? = some info at found
  by_cases bound : ranges[bi]!.2-1 < result.ctx.insts.size
  · have old : result.ctx.insts[ranges[bi]!.2-1]? = some result.ctx.insts[ranges[bi]!.2-1] :=
      Array.getElem?_eq_getElem bound
    rw [termCtx_insts_self old data] at found
    cases found
    cases source
  · have outside : (termCtx result.ctx (ranges[bi]!.2-1) data).insts[ranges[bi]!.2-1]? = none := by
      apply Array.getElem?_eq_none
      simpa [termCtx] using Nat.le_of_not_gt bound
    rw [outside] at found
    cases found

/-- Every actual retained source fence emits; demand does not control this decision. -/
theorem stock_lower_fence_emission {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence) :
    ∃ emission, emitInstruction event.ctx record.inst (scanState record.input record.inst) = .ok emission ∧
      record.output = emission.scan event.block record.inst (scanState record.input record.inst) := by
  have original := (stock_lower_record_context run scope events).2.2 _ _ _ found source
  have unsunk := ((SinkRules.stock_lower_fence_unsunk run scope original source).2 event events).2 record records
  have different := source_not_term run events found source
  have actual := record_execute run events records
  have lookup : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,found,Option.getD_some]
  simp only [scanInstruction,unsunk.1,Bool.false_eq_true,ite_false,
    show (record.inst == event.termInst) = false from (by simp [different]),
    Bool.false_and,lookup,source,Option.any_some,mustLower,Bool.not_true,
    Bool.false_and,Bool.and_false] at actual
  cases emitted : emitInstruction event.ctx record.inst (scanState record.input record.inst) with
  | error error => simp [emitted] at actual
  | ok emission =>
    simp only [emitted,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at actual
    exact ⟨emission,rfl,actual.symm⟩

end Backend.Stock.Proof
