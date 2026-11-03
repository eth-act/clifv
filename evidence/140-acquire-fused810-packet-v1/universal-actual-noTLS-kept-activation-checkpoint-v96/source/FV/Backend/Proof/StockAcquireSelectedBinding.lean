import FV.Backend.Proof.StockAcquireRhsOutput
import FV.Backend.Proof.StockAcquireRuleSource
import FV.Backend.Proof.StockAcquireAllWidthsBinding
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.IselCtlRuleIds

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem acquire_member : rule_lower_1272 ∈ program.rulesOf T.lower.id :=
  List.mem_iff_getElem?.mpr ⟨131,by rw [show T.lower.id = 686 from rfl,data_program.r686];rfl⟩

/-- The final recorded rule ID identifies the actual root rather than a nested helper. -/
theorem acquire_selected_rule {ctx : Ctx} {i : Nat} {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) (last : trace.getLast? = some 810) :
    selected.rule = rule_lower_1272 := by
  have idEq : selected.rule.id = 810 := Option.some.inj (selected.last_rule.symm.trans last)
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem acquire_member idEq

/-- A real retained root810 record derives its single fresh output and final alias internally.
The recorded rule ID classifies this proof case. It adds no accepted source condition. -/
theorem acquire_selected_final_binding {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} {z key : Nat}
    (installed : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg key .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ d,record.input.base.nextVreg ≤ d ∧ step.results = [[.vreg d .int]] ∧
      (result.final.alias[key]?).join = some d ∧ aliasNum result.final.alias key = d := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some 810 := by
    rw [← receipt.rules]
    exact selectedId
  have chosen := acquire_selected_rule receipt.selected last
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686];rfl
  have fuel := receipt.selected.fuelBound
  rw [count] at fuel
  obtain ⟨m,fuelEq⟩ : ∃ m,receipt.selected.matchFuel = m+5 :=
    ⟨receipt.selected.matchFuel-5,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨env,value,producer,args,held,source,stateEq,traceEq,producerValue⟩ :=
    acquire_root_match_source matched
  have rhs := receipt.selected.rhsRun
  rw [chosen,stateEq,traceEq] at rhs
  obtain ⟨ty,flags,typeValue,flagValue⟩ := AcquireHelpers.acquire_rhs_inputs (n := 999979) rhs
  obtain ⟨address,sunk,sinkTrace,instruction,sinkCall,decoded,output,state,fresh⟩ :=
    AcquireHelpers.acquire_rhs_output (n := 999899) typeValue flagValue producerValue rhs
  have root := receipt.rootRun
  rw [output] at root
  have binding := acquire_record_binding run events records installed results mapped recorded emitted root
  have lower : record.input.base.nextVreg ≤ sunk.base.nextVreg := by
    have frontier : (scanState record.input record.inst).base.nextVreg = record.input.base.nextVreg := by
      simp only [scanState]
      split <;> rfl
    rw [← frontier]
    exact fresh
  have final := stock_lower_record_fresh_result run scope dominated.ssa events records installed clif results mapped
    recorded emitted binding.2.1 lower
  exact ⟨sunk.base.nextVreg,lower,binding.2.1,final⟩

end Backend.Stock.Proof.Acquire810
