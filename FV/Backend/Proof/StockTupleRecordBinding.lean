import FV.Backend.Proof.StockTupleBinding
import FV.Backend.Proof.StockSelectionReceipts
namespace Backend.Stock.Proof.TupleRecordBindingDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 TupleBindingDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- Original SSA supplies distinct result identifiers for every actual retained
source record. No result-distinctness certificate is imposed on the caller. -/
theorem stock_lower_record_results_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst) :
    info.results.Nodup := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, rest⟩ := stock_lower_blockScanOrigin run events
  have table := stock_buildCtx_resultTable_nodup build ssa
  have global := (stock_lower_record_context run scope events).2.2 _ _ _ source clif
  exact (List.pairwise_flatMap.mp table).1 info
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? global))

/-- Actual emitted tuple outputs install all result aliases, and original SSA
carries each installed entry to the final driver state. The internally derived
whole-run frontier then makes every result resolve to its own fresh component. -/
theorem stock_lower_record_fresh_tuple {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (output : step.results = freshVectors record.input.base.nextVreg info.results.length) :
    ∀ j x,info.results[j]? = some x → ∃ key,event.ctx.valueReg? x = some (.vreg key .int) ∧
      (result.final.alias[key]?).join = some (record.input.base.nextVreg+j) ∧
      aliasNum result.final.alias key = record.input.base.nextVreg+j := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨mapped,maps,sources⟩ := stock_lower_record_context run scope events
  have distinct := stock_lower_record_results_nodup run scope ssa events source clif
  have results : receipt.results = freshVectors record.input.base.nextVreg info.results.length :=
    receipt.resultRegs.symm.trans output
  have binding := receipt.binding
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  rw [bang,results] at binding
  have installed := stock_bindResults_fresh_tuple mapped distinct binding
  intro j x atValue
  obtain ⟨key,lookup⟩ := installed.2.2.1 x (List.mem_of_getElem? atValue)
  have entry : (result.final.alias[key]?).join = some (record.input.base.nextVreg+j) := by
    rw [stock_lower_record_finalAliasEntry run
      (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) ssa events records
      (sources _ _ _ source clif) (List.mem_of_getElem? atValue) (by rw [← maps]; exact lookup)]
    rw [receipt.state]
    exact installed.2.2.2 j x key atValue lookup
  exact ⟨key,lookup,entry,stock_lower_freshAlias_resolves run
    (Nat.le_trans (stock_lower_blockScanInitialFrontier run event events record records) (Nat.le_add_right _ _)) key entry⟩
end Backend.Stock.Proof.TupleRecordBindingDraft
