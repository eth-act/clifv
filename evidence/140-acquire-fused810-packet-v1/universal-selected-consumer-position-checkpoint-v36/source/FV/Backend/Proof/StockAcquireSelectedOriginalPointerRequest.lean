import FV.Backend.Proof.StockAcquireOriginalRequest
import FV.Backend.Proof.StockAcquireRootSourceValue
import FV.Backend.Proof.StockAcquireRulePendingSource
import FV.Backend.Proof.StockAcquireSelectedBinding

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual selection connects the original extension operand, atomic producer, and pointer request. -/
theorem stock_lower_acquire_selected_original_pointer_request {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {rootInfo : IInfo} {target : Clif.Ty} {originalValue : Nat}
    (rootInstalled : event.ctx.insts[record.inst]? = some rootInfo)
    (rootSource : rootInfo.clif = some (.extend .uextend target originalValue))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ producer info ty flags pointer middle requested address out next fired,
      event.ctx.defInst? originalValue = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some out,next,fired) ∧
      Stock.externCtor event.ctx T.sink_inst [.inst producer] (scanState record.input record.inst) =
        .ok (.op .unit,middle) ∧
      Stock.externCtor event.ctx T.put_in_reg [.value pointer] middle = .ok (.reg address,requested) ∧
      DemandAllowed event.ctx middle pointer ∧ event.ctx.valueReg? pointer = some address ∧
      requested = middle.mark pointer ∧ next.demand = requested.demand := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some 810 := by
    rw [← receipt.rules]
    exact selectedId
  have chosen := acquire_selected_rule receipt.selected last
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuel := receipt.selected.fuelBound
  rw [count] at fuel
  obtain ⟨m,fuelEq⟩ : ∃ m,receipt.selected.matchFuel = m+5 :=
    ⟨receipt.selected.matchFuel-5,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  have rhs := receipt.selected.rhsRun
  rw [chosen] at rhs
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨value,producer,sunk,info,ty,flags,pointer,defined,once,arity,positive,color,
    sink,state,installed,original,integer,little,binding,sameState,sameTrace⟩ :=
    acquire_rule_pending_source mapped (n := 999979) matched rhs
  obtain ⟨originalProducer,originalSource,_,_,originalBinding⟩ :=
    acquire_root_match_original_value mapped rootInstalled rootSource matched
  have producerEq : originalProducer = producer :=
    V.inst.inj (Option.some.inj (Option.some.inj (originalBinding.symm.trans binding)))
  subst originalProducer
  have originalDefined := (source_effect_eligible originalSource positive).1
  rw [sameState,sameTrace] at rhs
  obtain ⟨typeV,flagsV,typeValue,flagValue⟩ := AcquireHelpers.acquire_rhs_inputs (n := 999979) rhs
  obtain ⟨addressValue,requested,sinkTrace,instruction,called,decoded,output,stateEq,fresh⟩ :=
    AcquireHelpers.acquire_rhs_output (n := 999899) typeValue flagValue binding rhs
  obtain ⟨actualTy,actualFlags,actualPointer,middle,address,sourceEq,actualInteger,actualLittle,
    actualSink,request,safe,register,returned,marked⟩ :=
    sink_atomic_original_request mapped installed original (fuel := 999991) (by omega) called
  have source : info.clif = some (.atomicLoad actualTy actualFlags actualPointer) :=
    original.trans (congrArg some sourceEq)
  have demand : receipt.next.demand = requested.demand := by rw [stateEq]
  exact ⟨producer,info,actualTy,actualFlags,actualPointer,middle,requested,address,
    receipt.out,receipt.next,receipt.fired,originalDefined,installed,source,actualInteger,actualLittle,receipt.rootRun,
    actualSink,request,safe,register,marked,demand⟩

end Backend.Stock.Proof.Acquire810
