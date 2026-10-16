import FV.Backend.Proof.StockIndirectRecordCode
import FV.Backend.Proof.StockExplicitCallExecution
import FV.Backend.Proof.StockDemand
namespace Backend.Stock.Proof.IndirectRecordSourceDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open IndirectRecordCodeDraft ExplicitCallSemDraft ExplicitCallExecutionDraft SourceRecordStatementDraft CallResultBindingDraft CallResultValuesDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem registers (ps ns bytes : List Nat) (hn : ns.length = ps.length) (hb : bytes.length = ps.length) :
    stackEnts (((ps.map fun n => ArgLoc.reg (.x n)).zip ns).zip bytes) = [] ∧
      regPairsOf (((ps.map fun n => ArgLoc.reg (.x n)).zip ns).zip bytes) = ns.zip (ps.map Reg.x) := by
  induction ps generalizing ns bytes with
  | nil => have a := List.length_eq_zero_iff.mp hn; subst ns; simp [stackEnts,regPairsOf]
  | cons p ps ih =>
    cases ns with
    | nil => simp at hn
    | cons n ns =>
      cases bytes with
      | nil => simp at hb
      | cons b bytes =>
        have rest := ih ns bytes (by simpa using hn) (by simpa using hb)
        simpa [stackEnts,regPairsOf] using rest

/-- Successful original indirect source execution supplies its declared ABI,
callee address, actual arguments, result types and memory effects. Original ABI
bounds prove the real record's argument layout is register-only. Original
XCallsIndOk then executes that SAME copy-free record and binds every result. -/
theorem stock_lower_indirect_call_record_source_run {F : BitVec 64 → Prop} {asm : FnCtx} {X : ExtSem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {syms : String → Option Nat} (symbolAddresses : ∀ n b,syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (symbolMemory : ∀ sl cm w,MR sl cm w → cm.symbols = syms)
    (external : XCallsIndOk env (indSigs f) MR X)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {fr fr' : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (frame : fr.func = f) (held : ValuesHeld (fun x => x ∈ callee :: args) event.ctx fr ρ)
    (related : MR fr.slots cm w) (source : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (ρ' : Nat → CV) (w' : Arm.ArmState),
      seqRun (explicitCallSem (csem F asm X)) record.output.emitted.toList ρ w = some (.fall ρ' w') ∧
      MR fr'.slots cm' w' ∧
      ValuesHeld (fun x => x ∈ info.results) result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  obtain ⟨sig,declared,params8,abiSig,target,ns,locs,bytes,stack,targetMap,mapping,byteRun,locations,code⟩ :=
    stock_lower_indirect_call_record_code run scope ssa abi events records slot clif recorded emitted
  obtain ⟨b,j,stm,block,statement,current,inst⟩ := stock_lower_source_record_statement run scope events records slot clif
  have member : sig ∈ indSigs f := mem_indSigs
    ⟨b,List.mem_of_getElem? block,stm,List.mem_of_getElem? statement,inst⟩ declared
  obtain ⟨info',inst',vals,regs,rest,slot',clif',body,evaluation,set,updated⟩ := source
  have same := Option.some.inj (slot'.symm.trans slot)
  subst info'
  have instruction := Option.some.inj (clif'.symm.trans clif)
  subst inst'
  obtain ⟨actualSig,x,argsVals,name,g,sourceDecl,pointer,read,symbol,implementation,signature,typed,returned,resultTypes⟩ := instOutcome_callIndirect_ok evaluation
  have same : actualSig = sig := Option.some.inj (sourceDecl.symm.trans (by rw [frame]; exact declared))
  subst actualSig
  have all := requested_values_hold (held.mono (fun x hx => List.mem_cons_of_mem _ hx)) read mapping
  simp only [List.map_map,Function.comp_def,registerView] at all
  have valuesCount : argsVals.length = sig.params.length := by
    have h := congrArg List.length typed
    simpa [Clif.AbiParam.tys] using h
  have nsCount : ns.length = sig.params.length := by have h := all.1; simp only [List.length_map] at h; omega
  have bytesCount := sigParamBytes_length byteRun
  have regLocations := sigArgLocs_regs byteRun (by omega)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (locations.symm.trans regLocations))
  have layout := registers (abiArgIdx sig.params 0) ns bytes
    (by rw [abiArgIdx_length]; exact nsCount) (by rw [abiArgIdx_length]; exact bytesCount)
  rw [layout.1,List.map_nil,List.nil_append] at code
  have useValues : (regPairsOf ((((abiArgIdx sig.params 0).map fun n => ArgLoc.reg (.x n)).zip ns).zip bytes)).map (ρ ·.1) = ns.map ρ := by
    rw [layout.2]
    rw [show (fun q : Nat × Reg => ρ q.1) = ρ ∘ Prod.fst from rfl,← List.map_map,
      List.map_fst_zip (by simp [abiArgIdx_length,nsCount])]
  have addressHeld := held.read (by simp) (frame_get_regs pointer) targetMap
  have address : lo64 (ρ target) = X.sym name 0 := by
    rw [symbolMemory _ _ _ related] at symbol
    rw [symbolAddresses name _ symbol]
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using lo64_of_vholds addressHeld
  have resultCount : vals.length = sig.returns.length := by
    have h := congrArg List.length resultTypes
    simpa [Clif.AbiParam.tys] using h
  obtain ⟨outs,w',executed,length,returnedValues,results,relatedAfter⟩ := stock_explicit_indirect_call_execution
    (F := F) (ctx := asm) (target := target) (base := record.input.base.nextVreg) (ρ := ρ)
    (L := regPairsOf ((((abiArgIdx sig.params 0).map fun n => ArgLoc.reg (.x n)).zip ns).zip bytes))
    external member fr implementation signature address (by omega) (by rw [useValues]; exact all) related returned resultCount typed
  dsimp only at updated
  have values := stock_lower_indirect_call_result_values (fr' := fr') (ρ := ρ) (outs := outs)
    run scope ssa abi events records slot clif recorded emitted set (by rw [updated]) returnedValues.prefixHold
  obtain ⟨sig2,declared2,resultLength,vectors,bindings⟩ := stock_lower_indirect_call_result_binding run scope ssa abi events records slot clif recorded emitted
  have same := Option.some.inj (declared2.symm.trans declared)
  subst sig2
  rw [resultLength] at values
  refine ⟨writeV ρ ((callDefOps (outDefs record.input.base.nextVreg sig.returns.length)).zip outs),w',?_,?_,values⟩
  · rw [code]; exact executed
  · simpa only [updated] using relatedAfter
end Backend.Stock.Proof.IndirectRecordSourceDraft
