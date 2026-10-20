import FV.Backend.Proof.StockIndirectRecordSource
import FV.Backend.Proof.StockIndirectRecordFootprint
import FV.Backend.Proof.StockCallResolvedFrame
namespace Backend.Stock.Proof.IndirectResolvedSourceDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open IndirectRecordCodeDraft IndirectRecordSourceDraft IndirectRecordFootprintDraft CallResolvedFrameDraft ExplicitCallSemDraft ExplicitCallFramesDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual indirect-call records define only their actual fresh explicit result
interval. Original source metadata supplies the signature and every bound. -/
theorem stock_lower_indirect_call_record_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∀ m ∈ record.output.emitted.toList,∀ d ∈ vdefs m,
      record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg := by
  obtain ⟨sig,declared,params8,abiSig,target,ns,locs,bytes,stack,targetMap,mapping,byteRun,locations,code⟩ :=
    stock_lower_indirect_call_record_code run scope ssa abi events records slot clif recorded emitted
  obtain ⟨sig2,declared2,upper,demand⟩ := stock_lower_indirect_call_record_footprint run scope ssa abi events records slot clif recorded emitted
  have same := Option.some.inj (declared2.symm.trans declared)
  subst sig2
  intro m member d defined
  rw [code] at member
  rcases List.mem_append.mp member with store | call
  · obtain ⟨e,present,rfl⟩ := List.mem_map.mp store
    rw [vdefs_argStore] at defined
    cases defined
  · have same := List.mem_singleton.mp call
    subst m
    rw [vdefs_call_reg] at defined
    simp only [outDefs,List.map_map,Function.comp_def,List.mem_map,List.mem_range] at defined
    obtain ⟨j,bound,rfl⟩ := defined
    constructor <;> omega

/-- The complete actual indirect-call record simulates successful ORIGINAL
source execution through final alias-resolved code and returned memory. Real
callee/argument requests derive the original demanded-and-available guard;
actual signature/address/result binding and all other-value framing are internal. -/
theorem stock_lower_indirect_call_guarded_source_run {F : BitVec 64 → Prop} {asm : FnCtx} {X : ExtSem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (abi : AbiSigsOk f)
    {syms : String → Option Nat} (symbolAddresses : ∀ n b,syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (symbolMemory : ∀ sl cm w,MR sl cm w → cm.symbols = syms)
    (external : XCallsIndOk env (indSigs f) MR X)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
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
  have coverage := stock_lower_indirect_call_operand_coverage run scope dominated abi events records block statement current slot clif recorded emitted
  have argsHeld := held.mono coverage
  have raw := stock_lower_indirect_call_record_source_run (F := F) (asm := asm) run scope dominated.ssa abi symbolAddresses symbolMemory external
    events records slot clif recorded emitted frame argsHeld related source
  have defs := stock_lower_indirect_call_record_defs run scope dominated.ssa abi events records slot clif recorded emitted
  obtain ⟨sig,declared,params8,abiSig,target,ns,locs,bytes,stack,targetMap,mapping,byteRun,locations,code⟩ :=
    stock_lower_indirect_call_record_code run scope dominated.ssa abi events records slot clif recorded emitted
  apply stock_lower_record_resolved_source_frame (stock_explicit_call_sem_driver (driverSem_csem F asm X))
    run scope dominated events records block statement current slot clif recorded emitted held source defs ?_ raw
  intro m member u used
  have argument : u = target ∨ u ∈ ns := by
    rw [code] at member
    rcases List.mem_append.mp member with store | call
    · obtain ⟨e,present,rfl⟩ := List.mem_map.mp store
      rw [vuseNums_argStore,List.mem_singleton] at used
      subst u
      exact .inr (map_zip_args (mem_args_of_stackEnts present))
    · have same := List.mem_singleton.mp call
      subst m
      rw [vuseNums_call_reg] at used
      rcases List.mem_cons.mp used with rfl | member
      · exact .inl rfl
      · exact .inr (map_zip_args (mem_args_of_regPairs member))
  rcases argument with rfl | member
  · exact ⟨callee,(coverage callee (List.mem_cons_self ..)).2,targetMap⟩
  · obtain ⟨x,present,mapped⟩ := Backend.Proof.Flow.mapM_mem mapping (.vreg u .int) (List.mem_map_of_mem member)
    exact ⟨x,(coverage x (List.mem_cons_of_mem _ present)).2,mapped⟩
end Backend.Stock.Proof.IndirectResolvedSourceDraft
