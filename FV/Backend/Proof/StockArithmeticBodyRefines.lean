module

public import FV.Backend.Proof.StockPureRecordCoverage
public import FV.Backend.Proof.StockAddSubScanRefines

@[expose] public section

namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Successful actual binding supplies its result register; this is derived,
not a new input-side map certificate. -/
theorem emission_result_mapped {ctx : Ctx} {i z : Nat} {before : State} {emission : Emission}
    (run : emitInstruction ctx i before = .ok emission)
    (results : ctx.insts[i]!.results = [z]) : ∃ r, ctx.valueReg? z = some r := by
  unfold emitInstruction at run
  cases root : Stock.runTerm ctx "lower" [.inst i] before with
  | error e => simp only [root,bind,Except.bind] at run; cases run
  | ok value =>
    rcases value with ⟨out,next,rules⟩
    simp only [root,bind,Except.bind] at run
    cases out with
    | none => cases run
    | some out =>
      cases out <;> try (cases run)
      rename_i rss
      rw [results] at run
      cases rss with
      | nil => simp at run
      | cons regs rest =>
        simp only [List.zip_cons_cons,List.zip_nil_left] at run
        split at run
        · cases run
        · cases binding : bindResults ctx [(z,regs)] next with
          | error e => simp only [binding] at run; cases run
          | ok pair =>
            unfold bindResults at binding
            simp only [List.foldlM_cons,List.foldlM_nil] at binding
            cases mapped : ctx.valueReg? z with
            | none => simp [mapped] at binding
            | some r => exact ⟨r,rfl⟩

/-- Original ordinary statement information survives the real term override. -/
theorem body_source_info {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord} {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block + j) :
    ∃ info, event.ctx.insts[record.inst]? = some info ∧
      info.clif = some stm.inst ∧ info.results = stm.results := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,bi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨info,found,clif,results⟩ := spec.facts.stmt event.block b j stm split.block statement
  have rootFound : result.ctx.insts[record.inst]? = some info := by
    rw [current,view.insts]
    exact found
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  have table : event.ctx.insts = result.ctx.insts.set! event.termInst ⟨data,[],[],none⟩ := by
    rw [eventEq,origin.2.1,origin.2.2.2.1]
    rfl
  have bound := (List.getElem?_eq_some_iff.mp statement).1
  have different : event.termInst ≠ record.inst := by
    rw [split.termIndex,current]
    omega
  refine ⟨info,?_,clif,results⟩
  rw [table]
  simpa only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne different] using rootFound

/-- Every retained scan has its actual execution equation. -/
private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- Successful original construction supplies singleton results for this source
family; no arity or register-map certificate is required from the caller. -/
theorem arithmetic_result {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {ty : Clif.Ty} {x y : Nat} (subtract : Bool)
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y)) :
    ∃ z, info.results = [z] := by
  obtain ⟨tys,result,typed,arity⟩ := inv.resTys i info _ source clif
  have result' : tys = [ty] := by
    cases subtract <;> simpa [Clif.Inst.resultTypes] using result.symm
  rw [result'] at arity
  cases values : info.results with
  | nil => simp [values] at arity
  | cons z rest =>
    cases rest with
    | nil => exact ⟨z,rfl⟩
    | cons a tail => simp [values] at arity

/-- Family coverage follows from original syntax and actual successful lowering.
This is the bridge from the whole-driver frame to existing body value simulation. -/
theorem actual_arithmetic_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, SelectAddSubOrOmittedRecord f event.ctx event.block record := by
  have quiet : ∀ stm ∈ b.body, colored stm.inst = false := by
    intro stm member
    obtain ⟨subtract,ty,x,y,shape⟩ := family stm member
    rw [shape]
    cases subtract <;> rfl
  obtain ⟨term,body,split,decisions⟩ := stock_lower_pure_body_decisions run scope blocks quiet events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  obtain ⟨step,recorded,decision⟩ := decisions record member
  rcases decision with omitted | emitted
  · exact Or.inl ⟨j,b,stm,split.block,statement,current,step,recorded,Or.inl omitted⟩
  · obtain ⟨subtract,ty,x,y,shape⟩ := family stm (List.mem_of_getElem? statement)
    obtain ⟨info,source,clif,results⟩ := body_source_info run events split statement current
    have clif' : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y) := by
      rw [clif,shape]
    have inv := (stock_lower_record_context run scope events).1
    obtain ⟨z,one⟩ := arithmetic_result inv subtract source clif'
    obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan
      (scans_execute split.scanned record member) recorded emitted
    have atInst : event.ctx.insts[record.inst]! = info := by
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,source,Option.getD_some]
    obtain ⟨r,mapped⟩ := emission_result_mapped emissionRun (by rw [atInst]; exact one)
    obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
    exact Or.inr ⟨j,b,stm,split.block,statement,current,step,recorded,emitted,
      subtract,info,ty,x,y,z,a,source,clif',one,results.symm.trans one,mapped⟩

/-- Actual pure arithmetic body simulation with all record-family, result-map,
scan and source-position certificates derived internally from the original input. -/
theorem actual_arithmetic_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,body,split,families⟩ := actual_arithmetic_families run scope blocks family events
  refine ⟨term,body,split,?_⟩
  intro s s' source ρ w held
  apply stock_lower_select_addsub_omitted_body_fall_refines run scope dominated events
    split.scanned split.retained families refines stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held

end Backend.Stock.Proof.ArithmeticBody
