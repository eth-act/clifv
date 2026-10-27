import FV.Backend.Proof.StockMemoryRecordKernel
import FV.Backend.Proof.StockMemoryRecordValues

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private instance : DecidableEq V := fun a b => decidable_of_iff ((a == b) = true) beq_iff_eq

private theorem of_toOption {ε α : Type} {e : Except ε α} {a : α}
    (h : e.toOption = some a) : e = .ok a := by
  cases e with
  | error err => cases h
  | ok value => simp only [Except.toOption,Option.some.injEq] at h; subst value; rfl

structure RecordInput where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  step : Step
  info : IInfo
  next : State
  trace : Array RuleId
  run : Stock.lower function = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 1
  frontier : record.input.base.nextVreg = 194
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.load .load .i32 flags 0 0)
  results : info.results = [2]
  mapped : event.ctx.valueReg? 2 = some (.vreg 193 .int)
  pointer : event.ctx.valueReg? 0 = some (.vreg 192 .int)
  parameter : event.ctx.defInst? 0 = none
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  evalRun : (evalExpr program (Stock.sem event.ctx) {} 120 rule_lower_2610.rhs
    (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run
    (scanState record.input record.inst,#[]) = .ok (some (.regsVec [[.vreg 194 .int]]),next,trace)
  rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
    .ok (some (.regsVec [[.vreg 194 .int]]),next,trace.toList ++ [1043])

/-- The complete lowering supplies the selected record's real receipts. -/
theorem record_input : Nonempty RecordInput := by
  have actual := record_observed
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨event,events,record,records,current,frontier,sourceData,mapped,pointer,parameter,stepData,rhsData⟩ :=
      (by simpa only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc,Except.toOption] using actual :
        ∃ event ∈ result.blockScans.toList,∃ record ∈ event.output.records,
          record.inst = 1 ∧ record.input.base.nextVreg = 194 ∧
          (event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
            some (some (.load .load .i32 flags 0 0),[2]) ∧
          event.ctx.valueReg? 2 = some (.vreg 193 .int) ∧ event.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
          event.ctx.defInst? 0 = none ∧ record.output.step.any (fun step => step.decision == .emitted) = true ∧
          ((evalExpr program (Stock.sem event.ctx) {} 120 rule_lower_2610.rhs
            (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run
            (scanState record.input record.inst,#[])).toOption.any (fun evaluated =>
              decide (evaluated.1 = some (.regsVec [[.vreg 194 .int]])) &&
              decide ((Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst)).toOption =
                some (evaluated.1,evaluated.2.1,evaluated.2.2.toList ++ [1043]))) = true)
    obtain ⟨info,source,clif,results⟩ := (by
      simpa only [Option.map_eq_some_iff,Prod.mk.injEq] using sourceData :
        ∃ info,event.ctx.insts[record.inst]? = some info ∧
          info.clif = some (.load .load .i32 flags 0 0) ∧ info.results = [2])
    obtain ⟨step,recorded,emitted⟩ := (by simpa only [Option.any_eq_true,beq_iff_eq] using stepData :
      ∃ step,record.output.step = some step ∧ step.decision = .emitted)
    obtain ⟨evaluated,evalOption,outEq,rootOption⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] using rhsData :
        ∃ evaluated,((evalExpr program (Stock.sem event.ctx) {} 120 rule_lower_2610.rhs
          (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run
          (scanState record.input record.inst,#[])).toOption = some evaluated ∧
          evaluated.1 = some (.regsVec [[.vreg 194 .int]]) ∧
          (Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst)).toOption =
            some (evaluated.1,evaluated.2.1,evaluated.2.2.toList ++ [1043]))
    have evalRun := of_toOption evalOption
    have rootRun := of_toOption rootOption
    obtain ⟨out,next,trace⟩ := evaluated
    simp only at outEq
    subst out
    exact ⟨⟨result,event,record,step,info,next,trace,run,events,records,current,frontier,source,clif,results,
      mapped,pointer,parameter,recorded,emitted,evalRun,rootRun⟩⟩

/-- The complete original two-block lowering retains a real load record whose
actual emitter installs193→194; selected-code and final-alias facts are derived. -/
theorem actual_load_record_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step),
      Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.inst = 1 ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      step.results = [[.vreg 194 .int]] ∧
      record.output.emitted = #[.load .uload32 (.vreg 194 .int) (.unsignedOffset (.vreg 192 .int) 0) flags] ∧
      aliasNum result.final.alias 193 = 194 := by
  obtain ⟨input⟩ := record_input
  have shape := stock_lower_parameter_load_record input.run scope dominated input.events input.records
    input.source input.clif input.results input.mapped input.parameter input.pointer input.recorded input.emitted
    (n := 0) input.evalRun input.rootRun
  rw [input.frontier] at shape
  exact ⟨input.result,input.event,input.record,input.step,input.run,input.events,input.records,input.current,
    input.recorded,input.emitted,shape.1,shape.2.1,shape.2.2.2⟩

end Backend.Stock.Memory.LoadFixture
