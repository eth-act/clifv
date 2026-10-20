import FV.Backend.Proof.StockBindingCoverage
import FV.Backend.Proof.StockConstantRecordValues

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
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
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq] at records ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record records

/-- Every retained source-statement record in an actual whole Stock run emits
covered forms and ordinary spill-valid instructions. The source mapping, real
scan execution, normalized emission buffer and binding facts are derived.
Clean terminator/context data remains an internal producer obligation, not a
new source acceptance condition or executable check. -/
theorem stock_lower_source_record_form_coverage {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (clean : Clean (sourceIdentityCtx event.ctx))
    {info : IInfo} {inst : Clif.Inst} (source : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some inst) :
    ∀ i ∈ record.output.emitted.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  exact stock_scanInstruction_form_coverage (stock_lower_record_context run scope events).1 clean source original
    (record_execute run events records)

end Backend.Stock.Proof.Coverage.Result
