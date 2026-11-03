import FV.Backend.Proof.StockAcquireActualRecordSlot
import FV.Backend.Proof.StockBodyScanOrigin

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- An actual emitted decision cannot be the body's skipped branch terminator. -/
theorem scan_emitted_nonbranch {ctx : Ctx} {block inst terminal : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step}
    (actual : scanInstruction ctx block inst terminal isBranch input = .ok output)
    (recorded : output.step = some step) (emitted : step.decision = .emitted) :
    ¬(inst = terminal ∧ isBranch = true) := by
  rintro ⟨rfl,rfl⟩
  cases sunk : input.sunk[terminal]! with
  | true =>
    simp only [scanInstruction,sunk,ite_true,pure,Except.pure] at actual
    cases actual;cases recorded;cases emitted
  | false =>
    simp only [scanInstruction,sunk,Bool.false_eq_true,ite_false,beq_self_eq_true,Bool.true_and,ite_true,
      pure,Except.pure] at actual
    cases actual;cases recorded

/-- Actual retained selection derives its unary consumer data without an external match certificate. -/
theorem stock_lower_acquire_consumer_unary_data {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ info fields,event.ctx.insts[record.inst]? = some info ∧ info.data = .data 152 29 fields := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some 810 := by rw [← receipt.rules];exact selectedId
  have chosen := acquire_selected_rule receipt.selected last
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuel := receipt.selected.fuelBound
  rw [count] at fuel
  obtain ⟨m,fuelEq⟩ : ∃ m,receipt.selected.matchFuel = m+1 := ⟨receipt.selected.matchFuel-1,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨env,args,iflets⟩ := matchRule_some_inv matched
  exact acquire_root_args_unary_data args

/-- Actual unary selection excludes both terminal alternatives and derives original source payload. -/
theorem stock_lower_acquire_consumer_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ info inst,event.ctx.insts[record.inst]? = some info ∧ info.clif = some inst := by
  have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
  have nonbranch := scan_emitted_nonbranch actual recorded emitted
  obtain ⟨info,fields,installed,shape⟩ := stock_lower_acquire_consumer_unary_data run events records recorded emitted selectedId
  rcases stock_lower_record_source_slot run scope events records with source | branch | ⟨term,data,kind,prepared,present⟩
  · exact source
  · exact False.elim (nonbranch branch)
  · have equal := Option.some.inj (installed.symm.trans present)
    rw [equal] at shape
    exact False.elim (ret_trap_data_not_unary kind prepared shape)

end Backend.Stock.Proof.Acquire810
