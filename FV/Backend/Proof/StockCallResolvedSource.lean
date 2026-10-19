import FV.Backend.Proof.StockCallRecordFootprint
import FV.Backend.Proof.StockExplicitCallFrames
namespace Backend.Stock.Proof.CallResolvedSourceDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open CallStoreSemDraft CallRecordSourceDraft CallRecordFootprintDraft ExplicitCallSemDraft ExplicitCallFramesDraft SourceRecordStatementDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem alias_renaming (a : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve a (a.size+1)) (aliasNum a) := by
  refine ⟨fun n c => resolve_vreg _ _ n c,?_⟩
  intro r hr
  cases r with
  | vreg n c => exact False.elim (hr n c rfl)
  | _ => rfl
private theorem renamed_defs (a : Array (Option Nat)) (i : MInst) :
    vdefs (i.mapRegs (Backend.lowerFunction.resolve a (a.size+1))) = (vdefs i).map (aliasNum a) := by
  unfold vdefs
  rw [operands_mapRegs (alias_renaming a)]
  cases operands : i.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map,Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl
private theorem statement_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    {info : IInfo} {inst : Clif.Inst} (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst) :
    info.results = stm.results := by
  have global := (stock_lower_record_context run scope events).2.2 _ _ _ slot clif
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,rest⟩ := stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,old,spec,view⟩ := buildCtx_source build
  obtain ⟨other,found,originalClif,results⟩ := spec.facts.stmt bi b j stm block statement
  have actual : original.insts[blockStart f bi+j]? = some info := by rw [← view.insts,← current]; exact global
  cases Option.some.inj (found.symm.trans actual)
  exact results

/-- Every definition of an actual direct-call record lies inside that record's
allocation interval. Stack stores have none and the call's real explicit result
bounds follow from the actual helper allocation, without a caller certificate. -/
theorem stock_lower_direct_call_record_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (colocated : ext.colocated = true)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∀ m ∈ record.output.emitted.toList,∀ d ∈ vdefs m,
      record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg := by
  obtain ⟨ns,locs,bytes,stack,mapping,byteRun,locations,code⟩ := stock_lower_direct_call_record_code run scope ssa abi events records slot clif external colocated recorded emitted
  have upper := (stock_lower_direct_call_record_footprint run scope ssa abi events records slot clif external colocated recorded emitted).1
  intro m member d defined
  rw [code] at member
  rcases List.mem_append.mp member with store | call
  · obtain ⟨e,present,rfl⟩ := List.mem_map.mp store
    rw [vdefs_argStore] at defined
    cases defined
  · have same := List.mem_singleton.mp call
    subst m
    rw [vdefs_call_sym] at defined
    simp only [outDefs,List.map_map,Function.comp_def,List.mem_map,List.mem_range] at defined
    obtain ⟨j,bound,rfl⟩ := defined
    constructor <;> omega

/-- A complete actual direct-call record simulates successful ORIGINAL source
execution through its final alias-resolved code and external memory effects.
Real helper requests derive argument demand; original dominance derives source
availability. Tuple results and every other demanded/available source value
hold afterwards, without caller alias, output, frame or helper certificates. -/
theorem stock_lower_direct_call_guarded_source_run {Rd F : BitVec 64 → Prop} {asm : FnCtx} {X : ExtSem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (abi : AbiSigsOk f)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memory : MemRefinesR Rd F sb syms (csem F asm X)) {outB : Nat} (outgoing : OutArgsOk F outB MR)
    (stack : CallsStack f outB) (external : XCallsOk env (f.externs.map (·.2)) MR X)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (declared : f.extern? fn = some ext) (colocated : ext.colocated = true)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {fr fr' : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (frame : fr.func = f)
    (held : ValuesHeld (fun x => Demanded record.output.state x ∧ x ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    (related : MR fr.slots cm w) (source : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (ρ' : Nat → CV) (w' : Arm.ArmState),
      seqRun (explicitCallSem (csem F asm X)) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') ∧
      MR fr'.slots cm' w' ∧
      ValuesHeld (fun x => Demanded record.input x ∧ x ∈ availOf f (availIn f result.ctx) bi (j+1))
        result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) ∧
      ValuesHeld (fun x => x ∈ info.results) result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  let gn := aliasNum result.final.alias
  let g := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  let D : Nat → Prop := fun n => record.input.base.nextVreg ≤ n ∧ n < record.output.state.base.nextVreg
  have coverage := stock_lower_direct_call_operand_coverage run scope dominated abi events records block statement current slot clif declared colocated recorded emitted
  have argsHeld := held.mono coverage
  obtain ⟨raw,w',executed,relatedAfter,returned⟩ := stock_lower_direct_call_record_source_run
    run scope dominated.ssa abi stable memory outgoing stack external events records slot clif declared colocated recorded emitted frame argsHeld related source
  have defs := stock_lower_direct_call_record_defs run scope dominated.ssa abi events records slot clif declared colocated recorded emitted
  have fix : ∀ n,D n → gn n = n := by
    intro n inside
    exact (stock_lower_freshAlias_terminal run (Nat.le_trans
      (stock_lower_blockScanInitialFrontier run event events record records) inside.1)).2
  obtain ⟨ns,locs,bytes,stackBytes,mapping,byteRun,locations,code⟩ := stock_lower_direct_call_record_code run scope dominated.ssa abi events records slot clif declared colocated recorded emitted
  have uses : ∀ m ∈ record.output.emitted.toList,∀ u ∈ vuseNums m,D u ∨ ¬ D (gn u) := by
    intro m member u used
    have argument : u ∈ ns := by
      rw [code] at member
      rcases List.mem_append.mp member with store | call
      · obtain ⟨e,present,rfl⟩ := List.mem_map.mp store
        rw [vuseNums_argStore,List.mem_singleton] at used
        subst u
        exact map_zip_args (mem_args_of_stackEnts present)
      · have same := List.mem_singleton.mp call
        subst m
        rw [vuseNums_call_sym] at used
        exact map_zip_args (mem_args_of_regPairs used)
    obtain ⟨x,present,mapped⟩ := Backend.Proof.Flow.mapM_mem mapping (.vreg u .int) (List.mem_map_of_mem argument)
    have outside := stock_lower_available_alias_outside_record run scope dominated events records block statement current (coverage x present).2
      (by rw [← (stock_lower_record_context run scope events).2.1]; exact mapped)
    exact .inr (by dsimp [D,gn]; omega)
  have driver := stock_explicit_call_sem_driver (driverSem_csem F asm X)
  obtain ⟨next,renamed,agree⟩ := (seqRun_rename (alias_renaming result.final.alias)
    (driver.rename g gn (alias_renaming result.final.alias)) fix defs uses (fun _ _ => rfl)).1 executed
  have idem := stock_lower_alias_idempotent run scope dominated
  have resolvedAgree : ∀ key,raw (gn key) = next (gn key) := by
    intro key
    have decision : D (gn key) ∨ ¬ D (gn (gn key)) := by
      by_cases inside : D (gn key)
      · exact .inl inside
      · exact .inr (by simpa only [gn,idem] using inside)
    have same := agree (gn key) decision
    simpa only [gn,idem] using same
  have allResults : ValuesHeld (fun x => x ∈ info.results) result.ctx fr' (fun key => next (gn key)) := by
    intro x member v lookup
    obtain ⟨key,map,value⟩ := returned x member v lookup
    exact ⟨key,map,by change VHolds v (next (gn key)); rw [← resolvedAgree]; exact value⟩
  have renamedDefs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs g),∀ n ∈ vdefs m,D n := by
    intro m member n defined
    obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
    rw [renamed_defs] at defined
    obtain ⟨d,rawDefined,rfl⟩ := List.mem_map.mp defined
    change D (gn d)
    rw [fix d (defs raw rawMember d rawDefined)]
    exact defs raw rawMember d rawDefined
  have sameResults := statement_results run scope events block statement current slot clif
  obtain ⟨info',inst',vals,regs,rest,slot',clif',body,evaluation,set,updated⟩ := source
  have same := Option.some.inj (slot'.symm.trans slot)
  subst info'
  dsimp only at updated set
  refine ⟨next,w',renamed,relatedAfter,?_,allResults⟩
  intro x required v lookup
  by_cases fresh : x ∈ info.results
  · obtain ⟨key,map,value⟩ := returned x fresh v lookup
    exact ⟨key,map,by change VHolds v (next (gn key)); rw [← resolvedAgree]; exact value⟩
  · have before := available_before_of_after_not_result block statement required.2 (by rwa [← sameResults])
    have demanded : Demanded record.output.state x := by
      intro zero
      have grows := stock_lower_record_demand_mono run events records recorded emitted x
      change record.output.state.demand[x]! = 0 at zero
      rw [zero] at grows
      exact required.1 (Nat.eq_zero_of_le_zero grows)
    have previous : fr.regs x = some v := by
      rw [updated] at lookup
      change regs x = some v at lookup
      rw [setMany_other set fresh] at lookup
      exact lookup
    obtain ⟨key,map,value⟩ := held x ⟨demanded,before⟩ v previous
    have global : result.ctx.valueReg? x = some (.vreg key .int) := by rw [← (stock_lower_record_context run scope events).2.1]; exact map
    have kept := stock_lower_available_fresh_frame run scope dominated events records block statement current before global renamedDefs renamed
    exact ⟨key,global,by change VHolds v (next (gn key)); rw [kept]; exact value⟩
end Backend.Stock.Proof.CallResolvedSourceDraft
