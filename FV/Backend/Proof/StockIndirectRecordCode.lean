import FV.Backend.Proof.StockIndirectCallRecordEmission
import FV.Backend.Proof.StockCallResultValues
namespace Backend.Stock.Proof.IndirectRecordCodeDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open IndirectCallRecordEmissionDraft IndirectCallEmissionDraft TupleBindingDraft TupleRecordBindingDraft CallResultBindingDraft
open SourceRecordStatementDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem scan_empty (st : State) (i : Nat) : (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> rfl
private theorem scan_frontier (st : State) (i : Nat) : (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState; dsimp only; split <;> rfl

/-- Actual indirect-call source position derives the ORIGINAL ABI facts and
signature. Real explicit tuple binding eliminates all binder copies, leaving
the SAME retained record's exact argument-store/call instruction sequence. -/
theorem stock_lower_indirect_call_record_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ (sig : Clif.Signature),f.sigDecls.lookup ref = some sig ∧ sig.params.length ≤ 8 ∧ sigAbiOk sig = true ∧
      ∃ (target : Nat) (ns : List Nat) (locs : List ArgLoc) (bytes : List Nat) (stack : Nat),
        event.ctx.valueReg? callee = some (.vreg target .int) ∧
        args.mapM event.ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int) ∧
        sigParamBytes sig = .ok bytes ∧ sigArgLocs sig = .ok (locs,stack) ∧
        record.output.emitted.toList = ((stackEnts ((locs.zip ns).zip bytes)).map argStore) ++
          [.call ⟨.reg (.vreg target .int),retPairs (regPairsOf ((locs.zip ns).zip bytes)),
            callDefs (outDefs record.input.base.nextVreg sig.returns.length)⟩] := by
  obtain ⟨sig,declared,receipt,chosen,calls⟩ := stock_lower_indirect_call_record_protocol run scope events records slot clif recorded emitted
  obtain ⟨b,j,stm,block,statement,current,inst⟩ := stock_lower_source_record_statement run scope events records slot clif
  have member : ∃ B ∈ f.blocks,∃ st ∈ B.body,st.inst = .callIndirect ref callee args :=
    ⟨b,List.mem_of_getElem? block,stm,List.mem_of_getElem? statement,inst⟩
  have signatureOk := abi.2 sig (mem_indSigs member declared)
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨target,ns,locs,bytes,stack,call,targetMap,mapping,byteRun,locations,shape,output,emission,static,fresh⟩ :=
    stock_indirect_call_protocol_emission data_program mapped signatureOk.2 calls
  obtain ⟨sig',declared',length,vectors,bindings⟩ := stock_lower_indirect_call_result_binding run scope ssa abi events records slot clif recorded emitted
  have binding := receipt.binding
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,slot]
  rw [bang,receipt.resultRegs.symm.trans vectors] at binding
  have installed := stock_bindResults_fresh_tuple mapped (stock_lower_record_results_nodup run scope ssa events slot clif) binding
  have code := receipt.code
  rw [installed.2.1,emission,scan_empty,Array.empty_append,installed.1,Array.append_empty] at code
  rw [shape,scan_frontier] at code
  exact ⟨sig,declared,signatureOk.1,signatureOk.2,target,ns,locs,bytes,stack,targetMap,mapping,byteRun,locations,
    by rw [code,Array.toList_push,List.toList_toArray]⟩
end Backend.Stock.Proof.IndirectRecordCodeDraft
