import FV.Backend.Proof.StockIndirectCallRecordEmission
import FV.Backend.Proof.StockCallRecordWitness
namespace Backend.Stock.Proof.IndirectCallEmissionWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open CallStaticFixture IndirectCallRecordEmissionDraft SourceRecordStatementDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

private theorem source_abi (implicit : Bool) : AbiSigsOk (function true implicit) := by
  have signatureOk := (source_conditions true implicit).2.2.2
  constructor
  · constructor
    · exact signatureOk
    · intro e member
      simp only [function,List.mem_singleton] at member
      subst e
      exact signatureOk
  · intro sig member
    cases implicit <;> simp [indSigs,function,callStatement] at member
    all_goals subst sig; exact ⟨by decide,signatureOk⟩

/-- Complete ordinary/sret indirect-call pipelines retain the actual guarded
callee request, selected helpers, exact emitted stack-store/call/binder-copy
code, real source-body position, final-alias SpillInstOk and returned call
instruction lookup. All original input conditions and successful pipeline
stages are included; the earlier observation kernels are reused. -/
theorem stock_complete_indirect_call_emission_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      LowerScope (function true implicit) ∧ Dominated (function true implicit) ∧
      ArityOk (function true implicit) ∧ AbiSigsOk (function true implicit) ∧
      Stock.lower (function true implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts true implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.callIndirect 0 80 (arguments true implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      (∃ (b : Clif.Block) (j : Nat) (stm : Clif.Stmt),(function true implicit).blocks[event.block]? = some b ∧
        b.body[j]? = some stm ∧ record.inst = blockStart (function true implicit) event.block+j ∧
        stm.inst = .callIndirect 0 80 (arguments true implicit)) ∧
      IndirectRecordEmission event.ctx record (signature true implicit) 80 (arguments true implicit) out.result.final.alias ∧
      ∃ (label : Nat) (vb : VBlock) (k : Nat) (call : CallInfo),
        out.result.code.blocks[label]? = some vb ∧
        vb.insts[k]? = some ((MInst.call call).mapRegs
          (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))) ∧
        SpillInstOk ((MInst.call call).mapRegs
          (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))) := by
  obtain ⟨out,event,record,info,step,receipt,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,chosen⟩ :=
    CallRecordWitnessDraft.stock_complete_indirect_call_selection_witness implicit
  obtain ⟨sig,declared,actual⟩ := stock_lower_indirect_call_record_emission lowered scope (source_abi implicit)
    events records slot clif recorded emitted
  have expected : (function true implicit).sigDecls.lookup 0 = some (signature true implicit) := rfl
  have same := Option.some.inj (declared.symm.trans expected)
  subst sig
  have origin := stock_lower_source_record_statement lowered scope events records slot clif
  have placed := stock_lower_indirect_call_instruction_static lowered scope (source_abi implicit)
    events records slot clif recorded emitted
  exact ⟨out,event,record,info,step,scope,dominated,arity,source_abi implicit,lowered,prepared,fallback,
    checked,physical,facts,events,records,slot,clif,recorded,emitted,origin,actual,placed⟩
end Backend.Stock.Proof.IndirectCallEmissionWitnessDraft
