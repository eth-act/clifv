import FV.Backend.Proof.StockCallRecordCalls
import FV.Backend.Proof.StockCallRhsStatic
import FV.Backend.Proof.StockCallRecordObservation
import FV.Backend.Proof.StockCallStaticWitness
namespace Backend.Stock.Proof.CallRecordWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open CallStaticFixture CallRhsCallsDraft CallRecordCallsDraft CallRootSelectionDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

private theorem record_found (indirect implicit : Bool) {result : Result}
    (lowered : Stock.lower (function indirect implicit) = .ok result) :
    ∃ (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (callStatement indirect implicit).inst ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  have found := CallRecordFixture.observed indirect implicit
  unfold CallRecordFixture.Observed at found
  rw [lowered] at found
  simp only [Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true] at found
  obtain ⟨event,events,record,records,checked⟩ := found
  cases slot : event.ctx.insts[record.inst]? with
  | none => simp [CallRecordFixture.callRecord,slot] at checked
  | some info =>
    cases recorded : record.output.step with
    | none => simp [CallRecordFixture.callRecord,slot,recorded] at checked
    | some step =>
      simp only [CallRecordFixture.callRecord,slot,recorded,Bool.and_eq_true,beq_iff_eq] at checked
      exact ⟨event,record,info,step,events,records,slot,checked.1,recorded,checked.2⟩

/-- Complete ordinary and sret direct-call pipelines inhabit the actual
selected-root/RHS/retained-record helper connection, with the same real binder
and after-state. All original source conditions and raw/checked/physical
stages are included; the earlier sibling helper replay is not used here. -/
theorem stock_complete_direct_call_record_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      LowerScope (function false implicit) ∧ Dominated (function false implicit) ∧
      ArityOk (function false implicit) ∧ sigAbiOk (signature false implicit) = true ∧
      Stock.lower (function false implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts false implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      ∃ receipt : RecordSelection event record step,
        receipt.selected.rule = rule_lower_2508 ∧ step.rules.getLast? = some rule_lower_2508.id ∧
        receipt.selected.env = directEnv (arguments false implicit) (signature false implicit) calleeName false ∧
        receipt.selected.matched = scanState record.input record.inst ∧ receipt.selected.matchTrace = #[] ∧
        DirectRootCalls program event.ctx (arguments false implicit) (signature false implicit) calleeName false
          (scanState record.input record.inst) receipt.next #[] receipt.selected.rhsTrace receipt.out ∧
        ∃ (call : CallInfo) (atCall afterCall : State) (callTrace : Array RuleId) (machine : V) (fuel : Nat),
          SpillInstOk (.call call) ∧ 30 ≤ fuel ∧
          ApplyInternal program (Stock.sem event.ctx) {} fuel 46 638 [.op (.callInfo call)]
            (atCall,#[]) machine (afterCall,callTrace) := by
  obtain ⟨out,pipeline,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,facts,
    output,pinned,argumentsRun,infoRun,fresh,static⟩ := CallStaticWitnessDraft.stock_complete_call_static_witness false implicit
  obtain ⟨event,record,info,step,events,records,slot,clif,recorded,emitted⟩ := record_found false implicit lowered
  change info.clif = some (.call 0 (arguments false implicit)) at clif
  let ext : Clif.ExtFunc := {name := calleeName,sig := signature false implicit,colocated := true}
  have external : (function false implicit).extern? 0 = some ext := rfl
  have actual := stock_lower_direct_call_record_calls lowered scope events records slot clif external rfl recorded emitted
  obtain ⟨receipt,chosen,last,environment,state,trace,calls⟩ := actual
  have static := CallRhsStaticDraft.stock_direct_call_rhs_info_static
    (stock_lower_record_context lowered scope events).1 abi calls
  exact ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,receipt,chosen,last,environment,state,trace,calls,static⟩

private theorem indirect_data {implicit : Bool} {ctx : Ctx}
    (mapped : MappedCtxInv (function true implicit) ctx) {ti : Nat} {info : IInfo}
    (slot : ctx.insts[ti]? = some info)
    (clif : info.clif = some (.callIndirect 0 80 (arguments true implicit))) :
    info.data = .data 152 7 [.data 151 9 [],.values (80 :: arguments true implicit),.op (.sig (signature true implicit))] := by
  have data := mapped.data ti info _ slot clif
  have declared : (function true implicit).sigDecls.lookup 0 = some (signature true implicit) := rfl
  simp only [instData,declared] at data
  unfold instDataV opcodeV mkVariant variantIdx variantNames Isle.Aarch64.program at data
  change Except.ok (V.data 152 7 [.data 151 9 [],.values (80 :: arguments true implicit),.op (.sig (signature true implicit))]) = .ok info.data at data
  exact (Except.ok.inj data).symm

/-- Both complete indirect-call sources supply an actual emitted record whose
selected rule is derived from real source matching. Helper and whole-call
semantic composition for this case remains required separately. -/
theorem stock_complete_indirect_call_selection_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step)
      (receipt : RecordSelection event record step),
      LowerScope (function true implicit) ∧ Dominated (function true implicit) ∧
      ArityOk (function true implicit) ∧ sigAbiOk (signature true implicit) = true ∧
      Stock.lower (function true implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts true implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.callIndirect 0 80 (arguments true implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ receipt.selected.rule = rule_lower_2529 := by
  obtain ⟨out,pipeline,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,facts,
    output,pinned,argumentsRun,infoRun,fresh,static⟩ := CallStaticWitnessDraft.stock_complete_call_static_witness true implicit
  obtain ⟨event,record,info,step,events,records,slot,clif,recorded,emitted⟩ := record_found true implicit lowered
  change info.clif = some (.callIndirect 0 80 (arguments true implicit)) at clif
  obtain ⟨receipt⟩ := stock_lower_record_selection lowered events records recorded emitted
  have data := indirect_data (stock_lower_record_context lowered scope events).1 slot clif
  have chosen := stock_selected_call_indirect_rule slot data receipt.selected
  exact ⟨out,event,record,info,step,receipt,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,chosen⟩
end Backend.Stock.Proof.CallRecordWitnessDraft
