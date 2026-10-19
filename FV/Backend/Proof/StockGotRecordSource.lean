import FV.Backend.Proof.StockGotRecordCode
import FV.Backend.Proof.StockGotStoreSem
namespace Backend.Stock.Proof.GotRecordSourceDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open GotRecordCodeDraft GotStoreSemDraft CallResultBindingDraft CallResultValuesDraft ExplicitCallSemDraft SourceRecordStatementDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Actual successful source continuation, real selected emission, ABI stack
stores, original external effects and every bound source result compose for
an actual complete direct-call record. No output/value/alias certificate is
assumed: source execution and the original contracts derive those facts. -/
theorem stock_lower_got_call_record_source_run {Rd F : BitVec 64 → Prop} {asm : FnCtx} {X : ExtSem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memory : MemRefinesR Rd F sb syms (csem F asm X)) {outB : Nat} (outgoing : OutArgsOk F outB MR)
    (stack : CallsStack f outB) (external : XCallsOk env (f.externs.map (·.2)) MR X)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (declared : f.extern? fn = some ext) (far : ext.colocated = false)
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
  obtain ⟨ns,locs,bytes,stackBytes,target,mapping,byteRun,locations,targetEq,code⟩ := stock_lower_got_call_record_code
    run scope ssa abi events records slot clif declared far recorded emitted
  obtain ⟨info',inst',vals,regs,rest,slot',clif',body,evaluation,set,updated⟩ := source
  have same := Option.some.inj (slot'.symm.trans slot)
  subst info'
  have instruction := Option.some.inj (clif'.symm.trans clif)
  subst inst'
  have fresh : ∀ n ∈ ns,n ≠ target := by
    intro n member
    obtain ⟨x,present,mapped⟩ := Backend.Proof.Flow.mapM_mem mapping (.vreg n .int) (List.mem_map_of_mem member)
    have global : result.ctx.valueReg? x = some (.vreg n .int) := by
      rw [← (stock_lower_record_context run scope events).2.1]; exact mapped
    obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,rest⟩ := stock_lower_blockScanOrigin run events
    have below := (buildCtx_allocated build).1 x n global
    have initial := stock_lower_blockScanInitialFrontier run event events record records
    omega
  obtain ⟨outs,w',executed,length,returnedValues,results,relatedAfter⟩ := stock_source_got_stores_execution
    (base := record.input.base.nextVreg) stable memory outgoing external declared stackOk byteRun locations mapping far fresh frame held related evaluation
  dsimp only at updated
  have values := stock_lower_call_result_values (fr' := fr') (ρ := upd ρ target (ofX (X.sym ext.name 0))) (outs := outs) run scope ssa abi events records slot clif declared recorded emitted set
    (by rw [updated]) returnedValues.prefixHold
  have count := (stock_lower_call_result_binding run scope ssa abi events records slot clif declared recorded emitted).1
  rw [count] at values
  refine ⟨writeV (upd ρ target (ofX (X.sym ext.name 0))) ((callDefOps (outDefs record.input.base.nextVreg ext.sig.returns.length)).zip outs),w',?_,?_,values⟩
  · rw [code]; exact executed
  · simpa only [updated] using relatedAfter
end Backend.Stock.Proof.GotRecordSourceDraft
