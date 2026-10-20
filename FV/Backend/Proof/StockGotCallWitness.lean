import FV.Backend.Proof.StockGotCallRecordEmission
import FV.Backend.Proof.StockGotCallObservation
namespace Backend.Stock.Proof.GotCallWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open GotCallFixture GotCallRhsDraft GotCallRecordEmissionDraft
open CallStaticFixture (signature arguments calleeName)
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

private theorem record_found (implicit : Bool) (out : Output) (facts : Facts implicit out) :
    ∃ (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  have found := facts.2.2.2
  simp only [List.any_eq_true] at found
  obtain ⟨event,events,record,records,checked⟩ := found
  cases slot : event.ctx.insts[record.inst]? with
  | none => simp [callRecord,slot] at checked
  | some info =>
    cases recorded : record.output.step with
    | none => simp [callRecord,slot,recorded] at checked
    | some step =>
      simp only [callRecord,slot,recorded,Bool.and_eq_true,beq_iff_eq] at checked
      exact ⟨event,record,info,step,events,records,slot,checked.1,recorded,checked.2⟩

/-- Complete ordinary nine-argument/two-result and implicit-sret GOT-call
sources inhabit actual selected RHS/helper/target-load/record emission,
raw/final-alias static validity and returned load/call instruction positions.
All original source conditions and successful raw/globalcheckedfallback/
physical stages are included. The new observation is checked by Lean’s kernel. -/
theorem stock_complete_got_call_emission_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      LowerScope (function implicit) ∧ Dominated (function implicit) ∧ ArityOk (function implicit) ∧
      AbiSigsOk (function implicit) ∧ Stock.lower (function implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      (∃ receipt : RecordSelection event record step,receipt.selected.rule = rule_lower_2518 ∧
        GotRootCalls program event.ctx (arguments false implicit) (signature false implicit) calleeName
          (scanState record.input record.inst) receipt.next #[] receipt.selected.rhsTrace receipt.out) ∧
      GotRecordEmission event.ctx record (signature false implicit) calleeName (arguments false implicit) out.result.final.alias ∧
      ∃ (target : Nat) (call : CallInfo),∀ i ∈ [MInst.loadExtNameGot (.vreg target .int) calleeName,MInst.call call],
        ∃ (label : Nat) (vb : VBlock) (k : Nat),out.result.code.blocks[label]? = some vb ∧
          vb.insts[k]? = some (i.mapRegs (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))) ∧
          SpillInstOk (i.mapRegs (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))) := by
  have actual := observed implicit
  unfold Observed at actual
  cases run : pipeline implicit with
  | error error => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok out =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq] at actual
    have facts : Facts implicit out := of_decide_eq_true actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,allocated,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    cases h
    have checked := PerEdge.allocResultAt_checked allocated
    have fallback : rf = spillAllocAt prepared.code prepared.edges := by
      unfold allocResultAt checkedSpillAt at allocated
      simp only [bind,Except.bind] at allocated
      split at allocated <;> cases allocated
      rfl
    obtain ⟨scope,dominated,arity,abi⟩ := source_conditions implicit
    obtain ⟨event,record,info,step,events,records,slot,clif,recorded,emitted⟩ := record_found implicit _ facts
    let ext : Clif.ExtFunc := {name := calleeName,sig := signature false implicit,colocated := false}
    have external : (function implicit).extern? 0 = some ext := rfl
    have protocol := stock_lower_got_call_record_protocol lowered scope events records slot clif external rfl recorded emitted
    have code := stock_lower_got_call_record_emission lowered scope abi events records slot clif external rfl recorded emitted
    have placed := stock_lower_got_call_instructions_static lowered scope abi events records slot clif external rfl recorded emitted
    exact ⟨_,event,record,info,step,scope,dominated,arity,abi,lowered,prepare,fallback,checked,physical,
      facts,events,records,slot,clif,recorded,emitted,protocol,code,placed⟩
end Backend.Stock.Proof.GotCallWitnessDraft
