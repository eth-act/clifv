import FV.Backend.Proof.StockCallRecordEmission
import FV.Backend.Proof.StockCallRecordWitness
namespace Backend.Stock.Proof.CallEmissionWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open CallStaticFixture CallRecordEmissionDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

private theorem source_abi (implicit : Bool) : AbiSigsOk (function false implicit) := by
  have signatureOk := (source_conditions false implicit).2.2.2
  constructor
  · constructor
    · exact signatureOk
    · intro e member
      simp only [function,List.mem_singleton] at member
      subst e
      exact signatureOk
  · intro sig member
    cases implicit <;> simp [indSigs,function,callStatement] at member

/-- Complete ordinary/sret direct-call source pipelines inhabit exact actual
stack-store/call/binder-copy emission and raw/final-resolved SpillInstOk. The
real resolved call has an actual returned instruction lookup. Original source
conditions, successful raw/checked-fallback/physical stages and real retained
source records are all preserved; cached pipeline observations are reused. -/
theorem stock_complete_direct_call_emission_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      LowerScope (function false implicit) ∧ Dominated (function false implicit) ∧
      ArityOk (function false implicit) ∧ AbiSigsOk (function false implicit) ∧
      Stock.lower (function false implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts false implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      DirectRecordEmission event.ctx record (signature false implicit) calleeName
        (arguments false implicit) out.result.final.alias ∧
      ∃ (label : Nat) (vb : VBlock) (k : Nat) (call : CallInfo),
        out.result.code.blocks[label]? = some vb ∧
        vb.insts[k]? = some ((MInst.call call).mapRegs
          (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))) ∧
        SpillInstOk ((MInst.call call).mapRegs
          (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))) := by
  obtain ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,receipt,chosen,last,environment,state,trace,calls,infoStatic⟩ :=
    CallRecordWitnessDraft.stock_complete_direct_call_record_witness implicit
  let ext : Clif.ExtFunc := {name := calleeName,sig := signature false implicit,colocated := true}
  have external : (function false implicit).extern? 0 = some ext := rfl
  have actual := stock_lower_direct_call_record_emission lowered scope (source_abi implicit)
    events records slot clif external rfl recorded emitted
  have placed := stock_lower_direct_call_instruction_static lowered scope (source_abi implicit)
    events records slot clif external rfl recorded emitted
  exact ⟨out,event,record,info,step,scope,dominated,arity,source_abi implicit,lowered,prepared,fallback,
    checked,physical,facts,events,records,slot,clif,recorded,emitted,actual,placed⟩
end Backend.Stock.Proof.CallEmissionWitnessDraft
