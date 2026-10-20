import FV.Backend.Proof.StockGotCallEmission
import FV.Backend.Proof.StockBlockCode
namespace Backend.Stock.Proof.GotCallRecordEmissionDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open GotCallRhsDraft GotCallEmissionDraft
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

private theorem call_data {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {ti fn : Nat} {info : IInfo} {args : List Nat}
    (slot : ctx.insts[ti]? = some info) (clif : info.clif = some (.call fn args)) :
    info.data = .data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)] := by
  have data := mapped.data ti info _ slot clif
  simp only [instData] at data
  cases external : f.extern? fn with
  | none => simp only [external] at data; cases data
  | some ext =>
    simp only [external] at data
    split at data
    · unfold instDataV opcodeV mkVariant variantIdx variantNames Isle.Aarch64.program at data
      change Except.ok (V.data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)]) = .ok info.data at data
      exact (Except.ok.inj data).symm
    · cases data

def GotRecordEmission (ctx : Ctx) (record : ScanRecord) (sig : Clif.Signature)
    (name : String) (args : List Nat) (aliases : Array (Option Nat)) : Prop :=
  ∃ (ns : List Nat) (locs : List ArgLoc) (bytes : List Nat) (stack target : Nat)
      (call : CallInfo) (copies : Array MInst),
    args.mapM ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int) ∧
    sigParamBytes sig = .ok bytes ∧ sigArgLocs sig = .ok (locs,stack) ∧
    target = record.input.base.nextVreg + sig.returns.length ∧
    call = ⟨.reg (.vreg target .int),retPairs (regPairsOf ((locs.zip ns).zip bytes)),
      callDefs (outDefs record.input.base.nextVreg sig.returns.length)⟩ ∧
    record.output.emitted = ((((stackEnts ((locs.zip ns).zip bytes)).map argStore).toArray.push
      (.loadExtNameGot (.vreg target .int) name)).push (.call call)) ++ copies ∧
    ∀ i ∈ [MInst.loadExtNameGot (.vreg target .int) name,MInst.call call],
      SpillInstOk i ∧ SpillInstOk (i.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) ∧
      i ∈ record.output.emitted.toList

/-- Actual non-colocated emitted source records derive the selected GOT rule
and complete real RHS protocol, retaining the same result binder and copies. -/
theorem stock_lower_got_call_record_protocol {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (far : ext.colocated = false)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ receipt : RecordSelection event record step,receipt.selected.rule = rule_lower_2518 ∧
      GotRootCalls program event.ctx args ext.sig ext.name
        (scanState record.input record.inst) receipt.next #[] receipt.selected.rhsTrace receipt.out := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  have data := call_data mapped slot clif
  have extCtx : event.ctx.func.extern? fn = some ext := by rw [mapped.func]; exact external
  obtain ⟨chosen,environment,state,trace,calls⟩ := stock_selected_got_call_rhs_calls slot data extCtx far receipt.selected
  exact ⟨receipt,chosen,calls⟩

/-- Original whole-function scope and ABI conditions derive exact actual GOT
load/call/copy emission and raw/final-resolved SpillInstOk for BOTH instructions.
Fresh target and result definitions supply final def-fixing internally. -/
theorem stock_lower_got_call_record_emission {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (far : ext.colocated = false)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    GotRecordEmission event.ctx record ext.sig ext.name args result.final.alias := by
  obtain ⟨receipt,chosen,calls⟩ := stock_lower_got_call_record_protocol run scope events records slot clif external far recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨ns,locs,bytes,stack,target,call,mapping,byteRun,locations,targetEq,shape,output,code,gotControl,callControl⟩ :=
    stock_got_call_protocol_emission data_program mapped (extern_sigAbiOk abi external) calls
  have actualCode : record.output.emitted =
      ((((stackEnts ((locs.zip ns).zip bytes)).map argStore).toArray.push
        (.loadExtNameGot (.vreg target .int) ext.name)).push (.call call)) ++ receipt.copies := by
    rw [receipt.code,binding_base receipt.binding,code,scan_empty,Array.empty_append]
  have rename : VRenaming (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
      (aliasNum result.final.alias) := by
    refine ⟨fun n c => resolve_vreg _ _ n c,?_⟩
    intro r notVirtual
    cases r with
    | vreg n c => exact False.elim (notVirtual n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  refine ⟨ns,locs,bytes,stack,target,call,receipt.copies,mapping,byteRun,locations,?_,?_,actualCode,?_⟩
  · simpa only [scan_frontier] using targetEq
  · simpa only [scan_frontier] using shape
  · intro i member
    have control : CtlShape (scanState record.input record.inst).base.nextVreg i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact gotControl
      · exact callControl
    have raw := spillInstOk_of_ctlShape control
    refine ⟨raw,?_,?_⟩
    · apply spillInstOk_mapRegs rename raw
      intro ops operands o present defined
      have fresh := ctlShape_defs control ops operands o present defined
      rw [scan_frontier] at fresh
      exact (stock_lower_freshAlias_terminal run
        (Nat.le_trans (stock_lower_blockScanInitialFrontier run event events record records) fresh)).2
    · rw [actualCode,Array.toList_append,Array.toList_push,Array.toList_push]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> simp

/-- Both the real GOT load and its real indirect call have actual returned
instruction lookups with final-alias SpillInstOk. -/
theorem stock_lower_got_call_instructions_static {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (far : ext.colocated = false)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ (target : Nat) (call : CallInfo),∀ i ∈ [MInst.loadExtNameGot (.vreg target .int) ext.name,MInst.call call],
      ∃ (label : Nat) (vb : VBlock) (k : Nat),result.code.blocks[label]? = some vb ∧
        vb.insts[k]? = some (i.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ∧
        SpillInstOk (i.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
  obtain ⟨ns,locs,bytes,stack,target,call,copies,mapping,byteRun,locations,targetEq,shape,code,valid⟩ :=
    stock_lower_got_call_record_emission run scope abi events records slot clif external far recorded emitted
  refine ⟨target,call,?_⟩
  intro i member
  obtain ⟨raw,static,present⟩ := valid i member
  obtain ⟨label,vb,start,placed,segment⟩ := stock_lower_record_segment run events records
  have mappedMember := List.mem_map_of_mem (f := fun i => i.mapRegs
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) present
  obtain ⟨j,bound,equal⟩ := List.getElem_of_mem mappedMember
  refine ⟨label,vb,start+j,placed,?_,static⟩
  simpa only [equal] using segment j bound
end Backend.Stock.Proof.GotCallRecordEmissionDraft
