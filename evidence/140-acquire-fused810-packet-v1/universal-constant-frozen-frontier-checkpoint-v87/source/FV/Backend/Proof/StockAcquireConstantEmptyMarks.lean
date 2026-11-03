import FV.Backend.Proof.StockAcquireConstantRecordNeededValues
import FV.Backend.Proof.StockAcquirePendingMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- Actual constant selection derives an empty sink group from its real interpreter runs.
Inherited sink marks remain unchanged. -/
theorem stock_lower_constant_empty_marks {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) :
    PendingMarks event.ctx (scanState record.input record.inst) [] record.output.state := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have context := (stock_lower_record_context run scope events).1
  have chosen := ConstantComplete.selected_rule context source clif receipt.selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686];rfl
  have enough := receipt.selected.fuelBound
  have matched := receipt.selected.matchedRun
  have evaluated := receipt.selected.rhsRun
  rw [chosen] at matched evaluated
  obtain ⟨_,_,_,dest,_,outEq,_,_⟩ := stock_iconst_ok data_program context source clif rfl refines
    (by omega) (by decide) matched evaluated
  have root := receipt.rootRun
  have evaluatedOut := evaluated.trans (congrArg (fun value : V =>
    (Except.ok (some value,receipt.next,receipt.selected.rhsTrace) :
      Except Err (Option V × State × Array RuleId))) outEq)
  rw [outEq] at root
  obtain ⟨actual,actualRun,actualState,_,_⟩ := stock_iconst_emission_alias data_program
    source results mapped rfl matched evaluatedOut root
  obtain ⟨observed,observedRun,scanEq⟩ := stock_emitted_scan
    (stock_fence_record_execute run events records) recorded emitted
  have same : observed = actual := Except.ok.inj (observedRun.symm.trans actualRun)
  rw [same] at scanEq
  apply PendingMarks.frame (middle := record.output.state)
  · rw [scanEq]
    change actual.state.entryColor = _
    rw [actualState]
  · rw [scanEq]
    change actual.state.color = _
    rw [actualState]
  · rw [scanEq]
    change actual.state.sunk = _
    rw [actualState]
  · exact .nil _

end Backend.Stock.Proof.Acquire810
