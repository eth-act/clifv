import FV.Backend.Proof.StockAcquireFallbackExtendShape

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual retained fallback selection derives the exact raw fragment and fresh result internally.
Original SSA supplies result typing; no future source frame or successful extension is assumed. -/
theorem stock_lower_fallback_extend_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id) :
    ∃ (sourceType : CTy) (pointer resultId key dest : Nat),
      event.ctx.valueType? x = some sourceType ∧ sourceType ∈ eCTys ∧
      event.ctx.valueReg? x = some (.vreg pointer .int) ∧ info.results = [resultId] ∧
      event.ctx.valueReg? resultId = some (.vreg key .int) ∧ dest = record.input.base.nextVreg ∧
      step.results = [[.vreg dest .int]] ∧
      record.output.emitted = #[.extend (.vreg dest .int) (.vreg pointer .int) signed sourceType.bits target.width] := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some (ScalarCast.extendRule signed).id := by rw [← receipt.rules];exact selectedId
  have idEq := Option.some.inj (receipt.selected.last_rule.symm.trans last)
  have candidate : ScalarCast.extendRule signed ∈ program.rulesOf T.lower.id := by
    cases signed <;> rw [ScalarCast.extendRule,show T.lower.id = 686 from rfl,data_program.r686] <;> decide +kernel
  have chosen := eq_of_mem_of_id lower_ids_nodup receipt.selected.rule_mem candidate idEq
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨sourceType,pointer,sourceTyped,accepted,pointerMap,output,nextEq⟩ :=
    fallback_extend_selected_shape mapped signed installed source receipt.selected chosen
  let dest := (scanState record.input record.inst).base.nextVreg
  have fresh : dest = record.input.base.nextVreg := by
    simp only [dest,scanState]
    split <;> rfl
  have actualResults : receipt.results = [[.vreg dest .int]] := V.regsVec.inj (receipt.output.symm.trans output)
  obtain ⟨tys,types,resultTypes,length⟩ := mapped.resTys record.inst info _ installed source
  have tysEq : tys = [target] := by simpa only [Clif.Inst.resultTypes,Option.some.injEq] using types.symm
  rw [tysEq] at resultTypes length
  obtain ⟨resultId,results⟩ := List.length_eq_one_iff.mp length
  have resultAt : info.results[0]? = some resultId := by rw [results];rfl
  have typeAt : info.resTys[0]? = some (CTy.ofClif target) := by rw [resultTypes];rfl
  have typed := stock_lower_event_result_type run scope dominated events installed source resultAt typeAt
  obtain ⟨key,resultMap⟩ := mapped.typedReg resultId (CTy.ofClif target) typed
  have binding := receipt.binding
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,installed]
  rw [infoBang,results,actualResults] at binding
  have exactBinding := bindResults_virtual event.ctx receipt.next [(resultId,key,dest)] (by
    intro item member
    have same := List.mem_singleton.mp member
    subst item
    exact resultMap)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at exactBinding
  simp only [List.zip_cons_cons,List.zip_nil_left] at binding
  rw [exactBinding] at binding
  have boundEq := (Prod.mk.inj (Except.ok.inj binding)).1.symm
  have copiesEq := (Prod.mk.inj (Except.ok.inj binding)).2.symm
  refine ⟨sourceType,pointer,resultId,key,dest,sourceTyped,accepted,pointerMap,results,resultMap,fresh,?_,?_⟩
  · rw [receipt.resultRegs,actualResults]
  · rw [receipt.code,boundEq,copiesEq,nextEq]
    simp only [State.mark,LState.fresh,LState.emit]
    have empty : (scanState record.input record.inst).base.emitted = #[] := by
      simp only [scanState]
      split <;> rfl
    rw [empty]
    rfl

end Backend.Stock.Proof.Acquire810
