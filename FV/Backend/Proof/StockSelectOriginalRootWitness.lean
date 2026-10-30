import FV.Backend.Proof.StockSelectOriginalSourceMatch
import FV.Backend.Proof.StockOriginalSelectFixture
import FV.Backend.Proof.StockSelectionReceipts
namespace Backend.Stock.Proof.ScalarSelect.OriginalSelectFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- A complete original Stock driver run inhabits source data, unique root
selection and actual650/659/output decomposition, including retained result binding.
Condition truth and full source-step execution remain separate obligations. -/
theorem stock_original_select_root_calls_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step)
      (receipt : RecordSelection event record step),
      Stock.lower function = .ok result ∧ LowerScope function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.inst = 0 ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.select .i64 7 31 63) ∧
      info.data = .data 152 24 [.data 151 65 [],.values [7,31,63]] ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      receipt.selected.rule = rule_lower_2267 ∧ receipt.selected.env = originalSelectEnv 64 7 31 63 ∧
      receipt.selected.matched = scanState record.input record.inst ∧ receipt.selected.matchTrace = #[] ∧
      OriginalSelectRootCalls program event.ctx 64 7 31 63 (scanState record.input record.inst)
        receipt.next #[] receipt.selected.rhsTrace receipt.out := by
  have scope : LowerScope function := lowerScope_of (by rfl)
  have actual := stock_original_select_driver_observed
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨_,_,_,event,events,ctxEq,record,records,current,stepData⟩ := actual
    simp only [minmaxCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,_,_,_⟩ := ctxEq
    obtain ⟨step,recorded,emitted,_⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some rule_lower_2267.id)
    have keyAt : (event.ctx.insts[record.inst]?).map minmaxSourceKey =
        some (some (.select .i64 7 31 63),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    change info.clif = some (.select .i64 7 31 63) at clif
    have inv := (stock_lower_record_context run scope events).1
    obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
    have data := (stock_original_select_source_data inv source clif).2.1
    obtain ⟨chosen,env,matched,trace,calls⟩ := stock_original_select_selected_calls inv source clif receipt.selected
    exact ⟨result,event,record,info,step,receipt,rfl,scope,events,records,current,source,clif,data,
      recorded,emitted,chosen,env,matched,trace,calls⟩
end Backend.Stock.Proof.ScalarSelect.OriginalSelectFixture
