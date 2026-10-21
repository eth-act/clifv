import FV.Backend.Proof.StockCallStoreSem
import FV.Backend.Proof.StockCallRecordEmission
import FV.Backend.Proof.StockCallResultValues
import FV.Backend.Proof.StockSourceRecordStatement
namespace Backend.Stock.Proof.CallRecordSourceDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open CallRecordCallsDraft CallEmissionDraft TupleBindingDraft TupleRecordBindingDraft CallResultBindingDraft CallResultValuesDraft
open CallStoreSemDraft ExplicitCallSemDraft SourceRecordStatementDraft
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
theorem stock_lower_direct_call_record_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (colocated : ext.colocated = true)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ (ns : List Nat) (locs : List ArgLoc) (bytes : List Nat) (stack : Nat),
      args.mapM event.ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int) ∧
      sigParamBytes ext.sig = .ok bytes ∧ sigArgLocs ext.sig = .ok (locs,stack) ∧
      record.output.emitted.toList = ((stackEnts ((locs.zip ns).zip bytes)).map argStore) ++
        [.call ⟨.sym ext.name,retPairs (regPairsOf ((locs.zip ns).zip bytes)),
          callDefs (outDefs record.input.base.nextVreg ext.sig.returns.length)⟩] := by
  obtain ⟨receipt,chosen,last,environment,state,trace,calls⟩ := stock_lower_direct_call_record_calls
    run scope events records slot clif external colocated recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨ns,locs,bytes,stack,call,mapping,byteRun,locations,shape,output,emission,static,fresh⟩ :=
    stock_direct_call_protocol_emission data_program mapped (extern_sigAbiOk abi external) calls
  have bindings := stock_lower_call_result_binding run scope ssa abi events records slot clif external recorded emitted
  have vector : receipt.results = freshVectors record.input.base.nextVreg info.results.length := receipt.resultRegs.symm.trans bindings.2.1
  have binding := receipt.binding
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,slot]
  rw [bang,vector] at binding
  have installed := stock_bindResults_fresh_tuple mapped (stock_lower_record_results_nodup run scope ssa events slot clif) binding
  have code := receipt.code
  rw [installed.2.1,emission,scan_empty,Array.empty_append,installed.1,Array.append_empty] at code
  rw [shape,scan_frontier] at code
  exact ⟨ns,locs,bytes,stack,mapping,byteRun,locations,by rw [code,Array.toList_push,List.toList_toArray]⟩

/-- Actual successful source continuation, real selected emission, ABI stack
stores, original external effects and every bound source result compose for
an actual complete direct-call record. No output/value/alias certificate is
assumed: source execution and the original contracts derive those facts. -/
theorem stock_lower_direct_call_record_source_run {Rd F : BitVec 64 → Prop} {asm : FnCtx} {X : ExtSem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memory : MemRefinesR Rd F sb syms (csem F asm X)) {outB : Nat} (outgoing : OutArgsOk F outB MR)
    (stack : CallsStack f outB) (external : XCallsOk env (f.externs.map (·.2)) MR X)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (declared : f.extern? fn = some ext) (colocated : ext.colocated = true)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {fr fr' : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (frame : fr.func = f) (held : ValuesHeld (fun x => x ∈ args) event.ctx fr ρ)
    (related : MR fr.slots cm w) (source : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (ρ' : Nat → CV) (w' : Arm.ArmState),
      seqRun (explicitCallSem (csem F asm X)) record.output.emitted.toList ρ w = some (.fall ρ' w') ∧
      MR fr'.slots cm' w' ∧
      ValuesHeld (fun x => x ∈ info.results) result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  obtain ⟨b,j,stm,block,statement,current,inst⟩ := stock_lower_source_record_statement run scope events records slot clif
  have stackOk := stack b (List.mem_of_getElem? block) stm (List.mem_of_getElem? statement) fn args ext inst declared
  obtain ⟨ns,locs,bytes,stackBytes,mapping,byteRun,locations,code⟩ := stock_lower_direct_call_record_code
    run scope ssa abi events records slot clif declared colocated recorded emitted
  obtain ⟨info',inst',vals,regs,rest,slot',clif',body,evaluation,set,updated⟩ := source
  have same := Option.some.inj (slot'.symm.trans slot)
  subst info'
  have instruction := Option.some.inj (clif'.symm.trans clif)
  subst inst'
  obtain ⟨outs,w',executed,length,returnedValues,results,relatedAfter⟩ := stock_source_call_stores_execution
    (base := record.input.base.nextVreg) stable memory outgoing external declared stackOk byteRun locations mapping frame held related evaluation
  dsimp only at updated
  have values := stock_lower_call_result_values (fr' := fr') (ρ := ρ) (outs := outs) run scope ssa abi events records slot clif declared recorded emitted set
    (by rw [updated]) returnedValues.prefixHold
  have count := (stock_lower_call_result_binding run scope ssa abi events records slot clif declared recorded emitted).1
  rw [count] at values
  refine ⟨writeV ρ ((callDefOps (outDefs record.input.base.nextVreg ext.sig.returns.length)).zip outs),w',?_,?_,values⟩
  · rw [code]; exact executed
  · simpa only [updated] using relatedAfter
end Backend.Stock.Proof.CallRecordSourceDraft
