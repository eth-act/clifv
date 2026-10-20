import FV.Backend.Proof.StockTupleRecordBinding
import FV.Backend.Proof.StockCallRecordEmission
import FV.Backend.Proof.StockIndirectCallRecordEmission
import FV.Backend.Proof.StockGotCallRecordEmission
namespace Backend.Stock.Proof.CallResultBindingDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open TupleBindingDraft TupleRecordBindingDraft CallRecordCallsDraft CallEmissionDraft
open IndirectCallRecordEmissionDraft IndirectCallEmissionDraft GotCallRecordEmissionDraft GotCallEmissionDraft
open SourceRecordStatementDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem scan_frontier (st : State) (i : Nat) : (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState; dsimp only; split <;> rfl

private theorem direct_length {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i fn : Nat} {args : List Nat} {info : IInfo} {ext : Clif.ExtFunc}
    (slot : ctx.insts[i]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) : info.results.length = ext.sig.returns.length := by
  obtain ⟨tys,typed,_,length⟩ := mapped.resTys i info _ slot clif
  simp only [Clif.Inst.resultTypes,external,Option.map_some] at typed
  cases typed
  simpa using length
private theorem indirect_length {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i ref callee : Nat} {args : List Nat} {info : IInfo} {sig : Clif.Signature}
    (slot : ctx.insts[i]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    (declared : f.sigDecls.lookup ref = some sig) : info.results.length = sig.returns.length := by
  obtain ⟨tys,typed,_,length⟩ := mapped.resTys i info _ slot clif
  simp only [Clif.Inst.resultTypes,declared,Option.map_some] at typed
  cases typed
  simpa using length

/-- The real call's fresh vector is bound to every source result and preserved
by final aliases. Both colocated and GOT selection are derived internally;
result arity comes from original source typing, including zero explicit sret outputs. -/
theorem stock_lower_call_result_binding {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    info.results.length = ext.sig.returns.length ∧
    step.results = freshVectors record.input.base.nextVreg info.results.length ∧
    ∀ j x,info.results[j]? = some x → ∃ key,event.ctx.valueReg? x = some (.vreg key .int) ∧
      (result.final.alias[key]?).join = some (record.input.base.nextVreg+j) ∧
      aliasNum result.final.alias key = record.input.base.nextVreg+j := by
  have mapped := (stock_lower_record_context run scope events).1
  have length := direct_length mapped slot clif external
  have output : step.results = freshVectors record.input.base.nextVreg info.results.length := by
    cases located : ext.colocated with
    | false =>
      obtain ⟨receipt,chosen,calls⟩ := stock_lower_got_call_record_protocol run scope events records slot clif external located recorded emitted
      obtain ⟨ns,locs,bytes,stack,target,call,mapping,byteRun,locations,targetEq,shape,out,rest⟩ :=
        stock_got_call_protocol_emission data_program mapped (extern_sigAbiOk abi external) calls
      have same := receipt.output.symm.trans out
      have vector := V.regsVec.inj same
      rw [receipt.resultRegs,vector]
      simp only [outRegs,freshVectors,scan_frontier,length]
    | true =>
      obtain ⟨receipt,chosen,last,environment,state,trace,calls⟩ := stock_lower_direct_call_record_calls run scope events records slot clif external located recorded emitted
      obtain ⟨ns,locs,bytes,stack,call,mapping,byteRun,locations,shape,out,rest⟩ :=
        stock_direct_call_protocol_emission data_program mapped (extern_sigAbiOk abi external) calls
      have vector := V.regsVec.inj (receipt.output.symm.trans out)
      rw [receipt.resultRegs,vector]
      simp only [outRegs,freshVectors,scan_frontier,length]
  exact ⟨length,output,stock_lower_record_fresh_tuple run scope ssa events records slot clif recorded emitted output⟩

/-- Actual indirect selection derives the declared signature, fresh explicit
result vector and every final source alias. Original source statement membership
supplies its ABI contract; no caller result-shape or alias certificate is added. -/
theorem stock_lower_indirect_call_result_binding {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ sig,f.sigDecls.lookup ref = some sig ∧ info.results.length = sig.returns.length ∧
      step.results = freshVectors record.input.base.nextVreg info.results.length ∧
      ∀ j x,info.results[j]? = some x → ∃ key,event.ctx.valueReg? x = some (.vreg key .int) ∧
        (result.final.alias[key]?).join = some (record.input.base.nextVreg+j) ∧
        aliasNum result.final.alias key = record.input.base.nextVreg+j := by
  obtain ⟨sig,declared,receipt,chosen,calls⟩ := stock_lower_indirect_call_record_protocol run scope events records slot clif recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨b,j,stm,block,statement,current,inst⟩ := stock_lower_source_record_statement run scope events records slot clif
  have member : ∃ B ∈ f.blocks,∃ st ∈ B.body,st.inst = .callIndirect ref callee args :=
    ⟨b,List.mem_of_getElem? block,stm,List.mem_of_getElem? statement,inst⟩
  have signatureOk := (abi.2 sig (mem_indSigs member declared)).2
  obtain ⟨target,ns,locs,bytes,stack,call,targetMap,mapping,byteRun,locations,shape,out,rest⟩ :=
    stock_indirect_call_protocol_emission data_program mapped signatureOk calls
  have vector := V.regsVec.inj (receipt.output.symm.trans out)
  have length := indirect_length mapped slot clif declared
  have output : step.results = freshVectors record.input.base.nextVreg info.results.length := by
    rw [receipt.resultRegs,vector]
    simp only [outRegs,freshVectors,scan_frontier,length]
  exact ⟨sig,declared,length,output,stock_lower_record_fresh_tuple run scope ssa events records slot clif recorded emitted output⟩
end Backend.Stock.Proof.CallResultBindingDraft
