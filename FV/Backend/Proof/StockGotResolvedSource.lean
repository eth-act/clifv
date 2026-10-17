import FV.Backend.Proof.StockGotRecordSource
import FV.Backend.Proof.StockGotRecordFootprint
import FV.Backend.Proof.StockCallFreshResolvedFrame
namespace Backend.Stock.Proof.GotResolvedSourceDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open GotRecordCodeDraft GotRecordSourceDraft GotRecordFootprintDraft CallFreshResolvedFrameDraft ExplicitCallSemDraft ExplicitCallFramesDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Every definition of an actual direct-call record lies inside that record's
allocation interval. Stack stores have none and the call's real explicit result
bounds follow from the actual helper allocation, without a caller certificate. -/
theorem stock_lower_got_call_record_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (far : ext.colocated = false)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∀ m ∈ record.output.emitted.toList,∀ d ∈ vdefs m,
      record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg := by
  obtain ⟨ns,locs,bytes,stack,target,mapping,byteRun,locations,targetEq,code⟩ := stock_lower_got_call_record_code run scope ssa abi events records slot clif external far recorded emitted
  have upper := (stock_lower_got_call_record_footprint run scope ssa abi events records slot clif external far recorded emitted).1
  intro m member d defined
  rw [code] at member
  rcases List.mem_append.mp member with store | call
  · obtain ⟨e,present,rfl⟩ := List.mem_map.mp store
    rw [vdefs_argStore] at defined
    cases defined
  · rcases List.mem_cons.mp call with rfl | call
    · rw [vdefs_got_ctl,List.mem_singleton] at defined
      subst d
      constructor <;> omega
    have same := List.mem_singleton.mp call
    subst m
    rw [vdefs_call_reg] at defined
    simp only [outDefs,List.map_map,Function.comp_def,List.mem_map,List.mem_range] at defined
    obtain ⟨j,bound,rfl⟩ := defined
    constructor <;> omega

/-- A complete actual direct-call record simulates successful ORIGINAL source
execution through its final alias-resolved code and external memory effects.
Real helper requests derive argument demand; original dominance derives source
availability. Tuple results and every other demanded/available source value
hold afterwards, without caller alias, output, frame or helper certificates. -/
theorem stock_lower_got_call_guarded_source_run {Rd F : BitVec 64 → Prop} {asm : FnCtx} {X : ExtSem}
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
    (declared : f.extern? fn = some ext) (far : ext.colocated = false)
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
  have coverage := stock_lower_got_call_operand_coverage run scope dominated abi events records block statement current slot clif declared far recorded emitted
  have raw := stock_lower_got_call_record_source_run (F := F) (asm := asm) run scope dominated.ssa abi stable memory outgoing stack external
    events records slot clif declared far recorded emitted frame (held.mono coverage) related source
  have defs := stock_lower_got_call_record_defs run scope dominated.ssa abi events records slot clif declared far recorded emitted
  obtain ⟨ns,locs,bytes,stackBytes,target,mapping,byteRun,locations,targetEq,code⟩ :=
    stock_lower_got_call_record_code run scope dominated.ssa abi events records slot clif declared far recorded emitted
  have upper := (stock_lower_got_call_record_footprint run scope dominated.ssa abi events records slot clif declared far recorded emitted).1
  apply stock_lower_record_resolved_source_frame_with_fresh_uses (stock_explicit_call_sem_driver (driverSem_csem F asm X))
    run scope dominated events records block statement current slot clif recorded emitted held source defs ?_ raw
  intro m member u used
  have argument : u = target ∨ u ∈ ns := by
    rw [code] at member
    rcases List.mem_append.mp member with store | call
    · obtain ⟨e,present,rfl⟩ := List.mem_map.mp store
      rw [vuseNums_argStore,List.mem_singleton] at used
      subst u
      exact .inr (map_zip_args (mem_args_of_stackEnts present))
    · rcases List.mem_cons.mp call with rfl | call
      · simp only [vuseNums_got_ctl,List.not_mem_nil] at used
      have same := List.mem_singleton.mp call
      subst m
      rw [vuseNums_call_reg] at used
      rcases List.mem_cons.mp used with rfl | member
      · exact .inl rfl
      · exact .inr (map_zip_args (mem_args_of_regPairs member))
  rcases argument with rfl | member
  · exact .inl ⟨by omega,by omega⟩
  · obtain ⟨x,present,mapped⟩ := Backend.Proof.Flow.mapM_mem mapping (.vreg u .int) (List.mem_map_of_mem member)
    exact .inr ⟨x,(coverage x present).2,mapped⟩
end Backend.Stock.Proof.GotResolvedSourceDraft
