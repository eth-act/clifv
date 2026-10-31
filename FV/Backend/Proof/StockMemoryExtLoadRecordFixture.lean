import FV.Backend.Proof.StockMemoryExtLoadSelected
import FV.Backend.Proof.StockMemoryExtLoadRecordValues
import FV.Backend.Proof.StockMemoryExtLoadRecordFrame
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Memory.ExtendedRoots.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def flags : Clif.MemFlags := {trapCode := none}
def function (kind : Kind) : Clif.Function := {
  name := "stock_integer_memory_record"
  sig := {
    params := [⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64)]
    body := [⟨[2],.load kind.sourceOp .i64 flags 0 0⟩]
    term := .ret [2] }] }

theorem scope (kind : Kind) : LowerScope (function kind) := by
  cases kind <;> exact lowerScope_of rfl

theorem dominated (kind : Kind) : Dominated (function kind) := by
  constructor
  · change ([0,2] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [function] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [function] at found
    subst b
    constructor
    · intro j stm present
      cases j with
      | zero =>
        simp [function] at present
        subst stm
        intro x member
        have zero : x = 0 := by simpa [Driver.instArgs] using member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
      | succ j => simp [function] at present
    · intro x member
      have two : x = 2 := by
        cases kind <;> simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function,Kind.sourceOp] using member
      subst x
      simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function kind) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function kind).blocks.length = 1 := rfl
    omega

private def observed (kind : Kind) : Option Bool :=
  (Stock.lower (function kind)).toOption.map fun result =>
    result.blockScans.toList.any fun event => event.output.records.any fun record =>
      record.inst == 0 && record.input.base.nextVreg == 194 &&
      decide ((event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
        some (some (.load kind.sourceOp .i64 flags 0 0),[2])) &&
      decide (event.ctx.valueReg? 2 = some (.vreg 193 .int)) &&
      decide (event.ctx.valueReg? 0 = some (.vreg 192 .int)) &&
      decide (event.ctx.defInst? 0 = none) &&
      record.output.step.any (fun step => step.decision == .emitted)

private theorem observation (kind : Kind) : observed kind = some true := by
  cases kind <;> decide +kernel

structure RecordInput (kind : Kind) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  step : Step
  info : IInfo
  run : Stock.lower (function kind) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 0
  frontier : record.input.base.nextVreg = 194
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.load kind.sourceOp .i64 flags 0 0)
  results : info.results = [2]
  mapped : event.ctx.valueReg? 2 = some (.vreg 193 .int)
  pointer : event.ctx.valueReg? 0 = some (.vreg 192 .int)
  parameter : event.ctx.defInst? 0 = none
  recorded : record.output.step = some step
  emitted : step.decision = .emitted

/-- Complete real lowering retains the original load record for every kind. -/
theorem record_input (kind : Kind) : Nonempty (RecordInput kind) := by
  have actual := observation kind
  unfold observed at actual
  cases run : Stock.lower (function kind) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨event,events,record,records,current,frontier,sourceData,mapped,pointer,parameter,stepData⟩ :=
      (by simpa only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] using actual :
        ∃ event ∈ result.blockScans.toList,∃ record ∈ event.output.records,
          record.inst = 0 ∧ record.input.base.nextVreg = 194 ∧
          (event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
            some (some (.load kind.sourceOp .i64 flags 0 0),[2]) ∧
          event.ctx.valueReg? 2 = some (.vreg 193 .int) ∧
          event.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
          event.ctx.defInst? 0 = none ∧
          record.output.step.any (fun step => step.decision == .emitted) = true)
    obtain ⟨info,source,clif,results⟩ := (by
      simpa only [Option.map_eq_some_iff,Prod.mk.injEq] using sourceData :
        ∃ info,event.ctx.insts[record.inst]? = some info ∧
          info.clif = some (.load kind.sourceOp .i64 flags 0 0) ∧ info.results = [2])
    obtain ⟨step,recorded,emitted⟩ := (by
      simpa only [Option.any_eq_true,beq_iff_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted)
    exact ⟨⟨result,event,record,step,info,run,events,records,current,frontier,source,clif,results,
      mapped,pointer,parameter,recorded,emitted⟩⟩

/-- Real retained code, fresh binding and scheduling preservation follow from
original source metadata, without an external execution certificate. -/
theorem extending_record_witness (kind : Kind) :
    ∃ input : RecordInput kind,
      input.step.results = [[.vreg 194 .int]] ∧
      input.record.output.emitted = #[.load kind.loadOp (.vreg 194 .int)
        (.unsignedOffset (.vreg 192 .int) 0) flags] ∧
      aliasNum input.result.final.alias 193 = 194 ∧
      input.record.output.state.sunk = input.record.input.sunk := by
  obtain ⟨input⟩ := record_input kind
  obtain ⟨little,out,next,trace,rhsTrace,root,rhs⟩ := stock_lower_extending_load_selected_receipts kind
    input.run (scope kind) input.events input.records input.source input.clif input.recorded input.emitted
  obtain ⟨outputs,code,upper,alias,demands⟩ := stock_lower_extending_load_record_full kind input.run
    (scope kind) (dominated kind) input.events input.records input.source input.clif input.results
    input.mapped input.parameter input.pointer input.recorded input.emitted (n := 999879) rhs root
  have unsunk := stock_lower_extending_load_sunk_eq kind input.run (scope kind) input.events input.records
    input.source input.clif input.parameter input.pointer input.recorded input.emitted
  rw [input.frontier] at outputs code alias
  exact ⟨input,outputs,code,alias,unsunk⟩

end Backend.Stock.Memory.ExtendedRoots.Fixture
