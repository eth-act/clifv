import FV.Backend.Proof.StockIndirectCallEmission
import FV.Backend.Proof.StockSourceRecordStatement
import FV.Backend.Proof.StockBlockCode
namespace Backend.Stock.Proof.IndirectCallRecordEmissionDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open IndirectCallRhsDraft IndirectCallEmissionDraft SourceRecordStatementDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem setAlias_base {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : next.base = st.base := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h; rfl) | (solve | cases h) | split at h
private theorem fold_base {α β : Type} (field : α → LState)
    (step : α → β → Except String α)
    (preserves : ∀ a b next,step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (run : xs.foldlM step a = .ok next) : field next = field a := by
  induction xs generalizing a with
  | nil => cases run; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    cases call : step a x with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle => simp only [call,bind,Except.bind] at run; exact (ih run).trans (preserves _ _ _ call)
private theorem binding_base {ctx : Ctx} {pairs : List (Nat × List Reg)} {st next : State} {copies : Array MInst}
    (run : bindResults ctx pairs st = .ok (next,copies)) : next.base = st.base := by
  unfold bindResults at run
  apply fold_base (fun a : State × Array MInst => a.1.base) _ ?_ pairs run
  intro acc pair next call
  rcases acc with ⟨s,code⟩
  rcases pair with ⟨v,rs⟩
  dsimp only at call
  cases mapped : ctx.valueReg? v with
  | none => simp only [mapped] at call; cases call
  | some r =>
    simp only [mapped] at call
    split at call
    · rename_i _ n cls
      cases alias : s.setAlias r (.vreg n cls) with
      | error e => simp only [alias,bind,Except.bind] at call; cases call
      | ok q => simp only [alias,bind,Except.bind,pure,Except.pure] at call; cases call; exact setAlias_base alias
    · cases call; rfl
    · cases call
private theorem scan_empty (st : State) (i : Nat) : (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> rfl
private theorem scan_frontier (st : State) (i : Nat) : (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState; dsimp only; split <;> rfl

/-- The actual record's stack stores, call, and binder copies. Static validity
is stated for the actual raw call and the actual final-resolved instruction.
Copies remain the real binder output; no empty-copy certificate is assumed. -/
def IndirectRecordEmission (ctx : Ctx) (record : ScanRecord) (sig : Clif.Signature)
    (callee : Nat) (args : List Nat) (aliases : Array (Option Nat)) : Prop :=
  ∃ (target : Nat) (ns : List Nat) (locs : List ArgLoc) (bytes : List Nat) (stack : Nat)
      (call : CallInfo) (copies : Array MInst),
    ctx.valueReg? callee = some (.vreg target .int) ∧
    args.mapM ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int) ∧
    sigParamBytes sig = .ok bytes ∧ sigArgLocs sig = .ok (locs,stack) ∧
    call = ⟨.reg (.vreg target .int),retPairs (regPairsOf ((locs.zip ns).zip bytes)),
      callDefs (outDefs record.input.base.nextVreg sig.returns.length)⟩ ∧
    record.output.emitted = (((stackEnts ((locs.zip ns).zip bytes)).map argStore).toArray.push (.call call)) ++ copies ∧
    (.call call : MInst) ∈ record.output.emitted.toList ∧ SpillInstOk (.call call) ∧
    SpillInstOk ((MInst.call call).mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) ∧
    (MInst.call call).mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)) ∈
      (record.output.emitted.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))).toList

private theorem call_data {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {ti ref callee : Nat} {info : IInfo} {args : List Nat}
    (slot : ctx.insts[ti]? = some info) (clif : info.clif = some (.callIndirect ref callee args)) :
    ∃ sig,f.sigDecls.lookup ref = some sig ∧
      info.data = .data 152 7 [.data 151 9 [],.values (callee :: args),.op (.sig sig)] := by
  have data := mapped.data ti info _ slot clif
  simp only [instData] at data
  cases declared : f.sigDecls.lookup ref with
  | none => simp only [declared] at data; cases data
  | some sig =>
    simp only [declared] at data
    unfold instDataV opcodeV mkVariant variantIdx variantNames Isle.Aarch64.program at data
    change Except.ok (V.data 152 7 [.data 151 9 [],.values (callee :: args),.op (.sig sig)]) = .ok info.data at data
    exact ⟨sig,rfl,(Except.ok.inj data).symm⟩

/-- The actual retained indirect-call source record derives its signature,
selected rule and complete real RHS protocol; no caller signature/rule/helper
certificate is supplied. -/
theorem stock_lower_indirect_call_record_protocol {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ sig,f.sigDecls.lookup ref = some sig ∧ ∃ receipt : RecordSelection event record step,
      receipt.selected.rule = rule_lower_2529 ∧
      IndirectRootCalls program event.ctx callee args sig
        (scanState record.input record.inst) receipt.next #[] receipt.selected.rhsTrace receipt.out := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨sig,declared,data⟩ := call_data mapped slot clif
  obtain ⟨chosen,environment,state,trace,calls⟩ := stock_selected_indirect_call_rhs_calls slot data receipt.selected
  exact ⟨sig,declared,receipt,chosen,calls⟩

/-- Original whole-function scope and ABI conditions derive actual indirect
call emission, final-alias static validity and real binder copies. Original
source-body membership supplies the ABI fact internally. -/
theorem stock_lower_indirect_call_record_emission {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ sig,f.sigDecls.lookup ref = some sig ∧
      IndirectRecordEmission event.ctx record sig callee args result.final.alias := by
  obtain ⟨sig,declared,receipt,chosen,calls⟩ :=
    stock_lower_indirect_call_record_protocol run scope events records slot clif recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨b,j,stm,block,statement,current,inst⟩ :=
    stock_lower_source_record_statement run scope events records slot clif
  have member : ∃ B ∈ f.blocks,∃ st ∈ B.body,st.inst = .callIndirect ref callee args :=
    ⟨b,List.mem_of_getElem? block,stm,List.mem_of_getElem? statement,inst⟩
  have signatureOk := (abi.2 sig (mem_indSigs member declared)).2
  obtain ⟨target,ns,locs,bytes,stack,call,targetMap,mapping,byteRun,locations,shape,output,code,static,freshDefs⟩ :=
    stock_indirect_call_protocol_emission data_program mapped signatureOk calls
  have actualCode : record.output.emitted =
      (((stackEnts ((locs.zip ns).zip bytes)).map argStore).toArray.push (.call call)) ++ receipt.copies := by
    rw [receipt.code,binding_base receipt.binding,code,scan_empty,Array.empty_append]
  have rawMember : (.call call : MInst) ∈ record.output.emitted.toList := by
    rw [actualCode,Array.toList_append,Array.toList_push]
    simp
  have rename : VRenaming (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
      (aliasNum result.final.alias) := by
    refine ⟨fun n c => resolve_vreg _ _ n c,?_⟩
    intro r notVirtual
    cases r with
    | vreg n c => exact False.elim (notVirtual n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  have resolved : SpillInstOk ((MInst.call call).mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
    apply spillInstOk_mapRegs rename static
    intro ops operands o member defined
    have fresh := freshDefs ops operands o member defined
    rw [scan_frontier] at fresh
    exact (stock_lower_freshAlias_terminal run
      (Nat.le_trans (stock_lower_blockScanInitialFrontier run event events record records) fresh)).2
  refine ⟨sig,declared,target,ns,locs,bytes,stack,call,receipt.copies,targetMap,mapping,byteRun,locations,
    ?_,actualCode,rawMember,static,resolved,?_⟩
  · simpa only [scan_frontier] using shape
  · rw [Array.toList_map]
    exact List.mem_map_of_mem rawMember

/-- The same actual indirect call has a real returned instruction lookup and
retains SpillInstOk after whole-driver alias resolution. -/
theorem stock_lower_indirect_call_instruction_static {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ (label : Nat) (vb : VBlock) (k : Nat) (call : CallInfo),
      result.code.blocks[label]? = some vb ∧
      vb.insts[k]? = some ((MInst.call call).mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ∧
      SpillInstOk ((MInst.call call).mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
  obtain ⟨sig,declared,target,ns,locs,bytes,stack,call,copies,targetMap,mapping,byteRun,locations,shape,code,rawMember,raw,static,member⟩ :=
    stock_lower_indirect_call_record_emission run scope abi events records slot clif recorded emitted
  obtain ⟨label,vb,start,placed,segment⟩ := stock_lower_record_segment run events records
  rw [Array.toList_map] at member
  obtain ⟨j,bound,equal⟩ := List.getElem_of_mem member
  refine ⟨label,vb,start+j,call,placed,?_,static⟩
  simpa only [equal] using segment j bound
end Backend.Stock.Proof.IndirectCallRecordEmissionDraft
