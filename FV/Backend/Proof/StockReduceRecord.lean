module

public import FV.Backend.Proof.StockReduceSelected
public import FV.Backend.Proof.StockRecordFinalAlias
public import FV.Backend.Proof.StockAliasTerminal

@[expose] public section

namespace Backend.Stock.Proof.ScalarCast.Reduce
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem scan_empty (st : State) (i : Nat) : (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> rfl
/-- Actual reduction records emit no instructions. Their real result binding
survives the whole traversal, and both source/result keys resolve to the same
final endpoint even when the source itself aliases an earlier producer. -/
theorem stock_lower_reduce_record_receipts {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.ireduce ty x))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some rule_lower_2146.id) :
    ∃ nx,event.ctx.valueReg? x = some (.vreg nx .int) ∧ step.results = [[.vreg nx .int]] ∧
      record.output.emitted = #[] ∧ record.output.state.demand = (record.input.mark x).demand ∧
      aliasNum result.final.alias a = aliasNum result.final.alias nx := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some rule_lower_2146.id := by rw [← receipt.rules]; exact selectedId
  have idEq := Option.some.inj (receipt.selected.last_rule.symm.trans last)
  have candidate : rule_lower_2146 ∈ program.rulesOf T.lower.id := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  have chosen := eq_of_mem_of_id lower_ids_nodup receipt.selected.rule_mem candidate idEq
  obtain ⟨context,maps,sources⟩ := stock_lower_record_context run scope events
  obtain ⟨nx,sourceMap,output,nextEq⟩ := stock_reduce_selected_receipts context source clif receipt.selected chosen
  have rss : receipt.results = [[.vreg nx .int]] := V.regsVec.inj (receipt.output.symm.trans output)
  have installed := bindResults_virtual event.ctx receipt.next [(z,a,nx)] (by
    intro p member; have same := List.mem_singleton.mp member; subst p; exact mapped)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at installed
  have binding := receipt.binding
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  rw [infoBang,results,rss] at binding
  simp only [List.zip_cons_cons,List.zip_nil_left] at binding
  rw [installed] at binding
  have boundEq := (Prod.mk.inj (Except.ok.inj binding)).1.symm
  have copiesEq := (Prod.mk.inj (Except.ok.inj binding)).2.symm
  have code : record.output.emitted = #[] := by
    rw [receipt.code,boundEq,copiesEq,nextEq]
    change (scanState record.input record.inst).base.emitted ++ #[] = #[]
    rw [scan_empty]; rfl
  have demand : record.output.state.demand = (record.input.mark x).demand := by
    rw [receipt.state,boundEq,nextEq]
    simp only [State.mark,scanState_demands]
  have entry : (result.final.alias[a]?).join = some nx := by
    rw [stock_lower_record_finalAliasEntry run (fun h => scope.nonempty (List.length_eq_zero_iff.mp h))
      dominated.ssa events records (x := z) (key := a) (sources _ _ _ source clif)
      (by rw [results]; simp) (by rw [← maps]; exact mapped)]
    rw [receipt.state,boundEq]
    change ((aliasStep receipt.next.alias (a,nx))[a]?).join = some nx
    rw [aliasStep_get]
    simp only [ite_true]
  exact ⟨nx,sourceMap,receipt.resultRegs.trans rss,code,demand,stock_lower_alias_step run scope dominated entry⟩
end Backend.Stock.Proof.ScalarCast.Reduce
