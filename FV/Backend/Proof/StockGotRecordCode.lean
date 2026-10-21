import FV.Backend.Proof.StockGotCallRecordEmission
import FV.Backend.Proof.StockCallRecordEmission
import FV.Backend.Proof.StockCallResultValues
import FV.Backend.Proof.StockSourceRecordStatement
namespace Backend.Stock.Proof.GotRecordCodeDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open GotCallRecordEmissionDraft GotCallEmissionDraft TupleBindingDraft TupleRecordBindingDraft CallResultBindingDraft CallResultValuesDraft
open SourceRecordStatementDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem scan_empty (st : State) (i : Nat) : (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> rfl
private theorem scan_frontier (st : State) (i : Nat) : (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState; dsimp only; split <;> rfl

/-- The actual retained direct call has exactly its stack stores and call.
Original SSA plus real explicit tuple outputs prove the real binder emits NO
copies; the selected RHS and helper executions are derived from the record. -/
theorem stock_lower_got_call_record_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (far : ext.colocated = false)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ (ns : List Nat) (locs : List ArgLoc) (bytes : List Nat) (stack target : Nat),
      args.mapM event.ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int) ∧
      sigParamBytes ext.sig = .ok bytes ∧ sigArgLocs ext.sig = .ok (locs,stack) ∧
      target = record.input.base.nextVreg + ext.sig.returns.length ∧
      record.output.emitted.toList = ((stackEnts ((locs.zip ns).zip bytes)).map argStore) ++
        [.loadExtNameGot (.vreg target .int) ext.name, .call ⟨.reg (.vreg target .int),retPairs (regPairsOf ((locs.zip ns).zip bytes)),
          callDefs (outDefs record.input.base.nextVreg ext.sig.returns.length)⟩] := by
  obtain ⟨receipt,chosen,calls⟩ := stock_lower_got_call_record_protocol
    run scope events records slot clif external far recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨ns,locs,bytes,stack,target,call,mapping,byteRun,locations,targetEq,shape,output,emission,loadShape,callShape⟩ :=
    stock_got_call_protocol_emission data_program mapped (extern_sigAbiOk abi external) calls
  have bindings := stock_lower_call_result_binding run scope ssa abi events records slot clif external recorded emitted
  have vector : receipt.results = freshVectors record.input.base.nextVreg info.results.length := receipt.resultRegs.symm.trans bindings.2.1
  have binding := receipt.binding
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,slot]
  rw [bang,vector] at binding
  have installed := stock_bindResults_fresh_tuple mapped (stock_lower_record_results_nodup run scope ssa events slot clif) binding
  have code := receipt.code
  rw [installed.2.1,emission,scan_empty,Array.empty_append,installed.1,Array.append_empty] at code
  rw [shape,scan_frontier] at code
  rw [scan_frontier] at targetEq
  exact ⟨ns,locs,bytes,stack,target,mapping,byteRun,locations,targetEq,by rw [code,Array.toList_push,Array.toList_push,List.toList_toArray]; simp only [List.append_assoc,List.cons_append,List.nil_append]⟩

end Backend.Stock.Proof.GotRecordCodeDraft
