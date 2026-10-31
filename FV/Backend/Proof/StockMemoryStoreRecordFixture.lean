import FV.Backend.Proof.StockMemoryStoreSourceValues
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Memory.StoreRoots.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def flags : Clif.MemFlags := {trapCode := none}
def function (kind : Kind) : Clif.Function := {
  name := "stock_integer_store_record"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨kind.sourceTy,.none,.normal⟩]
    returns := []
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64),(1,kind.sourceTy)]
    body := [⟨[],.store kind.sourceOp kind.sourceTy flags 1 0 0⟩]
    term := .ret [] }] }

theorem scope (kind : Kind) : LowerScope (function kind) := by
  cases kind <;> exact lowerScope_of rfl

theorem dominated (kind : Kind) : Dominated (function kind) := by
  constructor
  · change ([0,1] : List Nat).Nodup; decide
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
        have either : x = 1 ∨ x = 0 := by simpa [Driver.instArgs] using member
        rcases either with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
      | succ j => simp [function] at present
    · intro x member
      cases kind <;> simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function kind) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function kind).blocks.length = 1 := rfl
    omega

private def observed (kind : Kind) : Option Bool :=
  (Stock.lower (function kind)).toOption.map fun result =>
    result.blockScans.toList.any fun event => event.output.records.any fun record =>
      record.inst == 0 &&
      decide ((event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
        some (some (.store kind.sourceOp kind.sourceTy flags 1 0 0),[])) &&
      decide (event.ctx.valueReg? 1 = some (.vreg 193 .int)) &&
      decide (event.ctx.valueReg? 0 = some (.vreg 192 .int)) &&
      decide (event.ctx.defInst? 0 = none) && decide (event.ctx.defInst? 1 = none) &&
      decide (event.ctx.valueType? 1 = some (CTy.ofClif kind.sourceTy)) &&
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
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
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.store kind.sourceOp kind.sourceTy flags 1 0 0)
  results : info.results = []
  valueMapped : event.ctx.valueReg? 1 = some (.vreg 193 .int)
  pointerMapped : event.ctx.valueReg? 0 = some (.vreg 192 .int)
  pointerParameter : event.ctx.defInst? 0 = none
  valueParameter : event.ctx.defInst? 1 = none
  valueType : event.ctx.valueType? 1 = some (CTy.ofClif kind.sourceTy)
  pointerAlias : aliasNum result.final.alias 192 = 192
  valueAlias : aliasNum result.final.alias 193 = 193
  recorded : record.output.step = some step
  emitted : step.decision = .emitted

/-- Complete real lowering supplies all source and alias facts needed by the store record contracts. -/
theorem record_input (kind : Kind) : Nonempty (RecordInput kind) := by
  have actual := observation kind
  unfold observed at actual
  cases run : Stock.lower (function kind) with
  | error error => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨event,events,record,records,current,sourceData,valueMapped,pointerMapped,
      pointerParameter,valueParameter,valueType,pointerAlias,valueAlias,stepData⟩ :=
      (by simpa only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] using actual :
        ∃ event ∈ result.blockScans.toList,∃ record ∈ event.output.records,
          record.inst = 0 ∧
          (event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
            some (some (.store kind.sourceOp kind.sourceTy flags 1 0 0),[]) ∧
          event.ctx.valueReg? 1 = some (.vreg 193 .int) ∧
          event.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
          event.ctx.defInst? 0 = none ∧ event.ctx.defInst? 1 = none ∧
          event.ctx.valueType? 1 = some (CTy.ofClif kind.sourceTy) ∧
          aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 193 = 193 ∧
          record.output.step.any (fun step => step.decision == .emitted) = true)
    obtain ⟨info,source,clif,results⟩ := (by
      simpa only [Option.map_eq_some_iff,Prod.mk.injEq] using sourceData :
        ∃ info,event.ctx.insts[record.inst]? = some info ∧
          info.clif = some (.store kind.sourceOp kind.sourceTy flags 1 0 0) ∧ info.results = [])
    obtain ⟨step,recorded,emitted⟩ := (by
      simpa only [Option.any_eq_true,beq_iff_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted)
    exact ⟨⟨result,event,record,step,info,run,events,records,current,source,clif,results,
      valueMapped,pointerMapped,pointerParameter,valueParameter,valueType,pointerAlias,valueAlias,recorded,emitted⟩⟩

theorem RecordInput.typed {kind : Kind} (input : RecordInput kind) :
    kind.sourceOp = .store → input.event.ctx.valueType? 1 = some (.int kind.width.bits) := by
  intro plain
  rw [input.valueType]
  cases kind <;> first | rfl | cases plain

/-- Every store record contract is inhabited by full lowering with exact code and empty result binding. -/
theorem integer_store_record_witness (kind : Kind) :
    ∃ input : RecordInput kind,input.step.results = [] ∧
      input.record.output.emitted =
        #[.store kind.storeOp (.vreg 193 .int) (.unsignedOffset (.vreg 192 .int) 0) flags] ∧
      input.record.output.state.alias = input.record.input.alias := by
  obtain ⟨input⟩ := record_input kind
  obtain ⟨_,_,results,_,code,_,alias,_⟩ := stock_lower_integer_store_record_full kind input.run (scope kind)
    input.events input.records input.source input.clif input.typed input.pointerParameter input.pointerMapped
    input.valueMapped input.recorded input.emitted
  exact ⟨input,results,code,alias⟩

end Backend.Stock.Memory.StoreRoots.Fixture
