import FV.Backend.Proof.StockScopeRoots
import FV.Backend.Proof.StockScopeRootsWitness
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- This partition concerns ordinary source matches only. Terminator/branch
semantics and execution of the retained closure are separate obligations. -/
def sourceClosureRoots : List Rule := (program.rulesOf TId.lower).filter closureRoot
def excludedSourceRoots : List Rule := (program.rulesOf TId.lower).filter (fun r => !closureRoot r)
/-- Kernel evaluation of the real generated rule list gives the exact
partition; these numbers are not whole-driver execution-proof coverage. -/
theorem stock_source_root_partition_counts : (program.rulesOf TId.lower).length = 517 ∧
    sourceClosureRoots.length = 182 ∧ excludedSourceRoots.length = 335 := by
  rw [sourceClosureRoots,excludedSourceRoots,show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel
/-- Every actual selected ordinary source root belongs to the remaining real
rule list; unsupported roots are excluded by the original mapped context. -/
theorem stock_selected_source_root_partition {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) {before after : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out after trace) : selected.rule ∈ sourceClosureRoots := by
  exact List.mem_filter.mpr ⟨selected.rule_mem,stock_selected_source_root_closure mapped source clif selected⟩
/-- The partition is nonempty on both sides and contains actual generated
scalar and floating rules, with full source-rule membership.
The float ↔ integer conversion roots (`IselFloatCvt`, #140: `fcvt_from_{s,u}int`,
`fcvt_to_{s,u}int_sat`, 16 rules) are part of the source-closure root set
(the 166→182 bump). -/
theorem stock_source_root_partition_witness : rule_lower_53 ∈ sourceClosureRoots ∧
    rule_lower_58 ∈ excludedSourceRoots ∧ (program.rulesOf TId.lower).length = 517 ∧
    sourceClosureRoots.length = 182 ∧ excludedSourceRoots.length = 335 := by
  refine ⟨?_,?_,stock_source_root_partition_counts⟩
  · rw [sourceClosureRoots,show TId.lower = 686 from rfl,data_program.r686]; decide +kernel
  · rw [excludedSourceRoots,show TId.lower = 686 from rfl,data_program.r686]; decide +kernel
/-- A real completed source lowering selects a member of the exact remaining
partition, with nonempty retained selection and the original source scope. -/
theorem stock_selected_source_partition_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord)
      (step : Step) (info : IInfo) (receipt : RecordSelection event record step),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ event.ctx.insts[record.inst]? = some info ∧
      info.clif = some (.iconst .i8 7) ∧ record.output.step = some step ∧
      step.decision = .emitted ∧ receipt.selected.rule ∈ sourceClosureRoots := by
  obtain ⟨result,event,record,step,info,receipt,run,scope,events,records,source,clif,recorded,emitted,closed,last⟩ :=
    stock_selected_source_closure_witness
  exact ⟨_,result,event,record,step,info,receipt,run,scope,events,records,source,clif,recorded,emitted,
    List.mem_filter.mpr ⟨receipt.selected.rule_mem,closed⟩⟩
end Backend.Stock.Proof
