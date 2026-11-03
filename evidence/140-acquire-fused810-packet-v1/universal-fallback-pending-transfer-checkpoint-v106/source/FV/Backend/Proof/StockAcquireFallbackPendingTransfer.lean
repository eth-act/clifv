import FV.Backend.Proof.StockAcquireFallbackOperandValues
import FV.Backend.Proof.StockAcquireConsumerSourceUpdate

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Retained source metadata keeps the original statement's complete result list. -/
theorem stock_lower_original_statement_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {i : Nat} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {block : Clif.Block} {statement : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statementAt : block.body[j]? = some statement)
    (current : i = blockStart f bi+j) {info : IInfo} {inst : Clif.Inst}
    (installed : event.ctx.insts[i]? = some info) (source : info.clif = some inst) :
    info.results = statement.results := by
  have globalSource := (stock_lower_record_context run scope events).2.2 _ _ _ installed source
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,ordered,
    initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨other,found,originalSource,results⟩ := spec.facts.stmt bi block j statement blockAt statementAt
  have actual : original.insts[blockStart f bi+j]? = some info := by
    rw [← view.insts,← current]
    exact globalSource
  cases Option.some.inj (found.symm.trans actual)
  exact results

/-- The successful current fallback binds its new result and preserves every other required binding.
The proof recovers its operand from actual selection and the general pending invariant. -/
theorem stock_lower_fallback_pending_transfer {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id)
    {j : Nat} {block : Clif.Block} {statement : Clif.Stmt}
    (blockAt : f.blocks[event.block]? = some block) (statementAt : block.body[j]? = some statement)
    (current : record.inst = blockStart f event.block+j)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {program : Clif.Program}
    {before after : Clif.Frame × Clif.Mem}
    (sourceStep : SourceInstResult env program event.ctx record.inst before after)
    {frontier : ReadEffectFrontier event.ctx env program}
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier record.output.state) (retired : RetiredUndemanded frontier record.output.state)
    {regs : Nat → CV} {world : Arm.ArmState}
    (prior : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history
      record.output.state (j,before) regs world) :
    ∃ nextRegs nextWorld,seqRun isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
        some (.fall nextRegs nextWorld) ∧ SameWorld F nextWorld world ∧
      PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history
        record.input (j+1,after) nextRegs nextWorld := by
  obtain ⟨sourceType,pointer,resultId,key,dest,typed,accepted,mapped,results,resultMap,fresh,output,chunk⟩ :=
    stock_lower_fallback_extend_record run scope dominated events records signed installed source recorded emitted selectedId
  have operand := stock_lower_fallback_extend_pending_operand run scope dominated events records signed installed source
    recorded emitted selectedId blockAt statementAt current retained marked retired prior
  obtain ⟨actual,inst,vals,sourceRegs,rest,actualAt,actualSource,body,evaluated,written,frame⟩ := sourceStep
  have infoEq := Option.some.inj (actualAt.symm.trans installed)
  subst actual
  have instEq := Option.some.inj (actualSource.symm.trans source)
  subst inst
  have evaluatedPlain : Clif.evalInst before.1 before.2 (.extend (ScalarCast.extendOp signed) target x) =
      .ok (vals,after.2) := evaluated
  obtain ⟨value,lookup,grows,memoryEq,valsEq⟩ := evalInst_extend_ok evaluatedPlain
  have available := stock_lower_record_args_available run scope dominated events blockAt statementAt current installed source
    x (by cases signed <;> simp [Driver.instArgs])
  have restrictedLookup : (restrict before.1 (availOf f (availIn f result.ctx) event.block j)).regs x = some value := by
    rw [restrict_regs_of_mem available]
    exact lookup
  have restrictedHeld : ValueHeld event.ctx (restrict before.1 (availOf f (availIn f result.ctx) event.block j))
      (fun k => regs (aliasNum result.final.alias k)) x := by
    intro val found
    rw [restrict_regs_of_mem available] at found
    exact operand val found
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some (ScalarCast.extendRule signed).id := by rw [← receipt.rules];exact selectedId
  have chosen := fallback_extend_selected_rule signed receipt.selected last
  obtain ⟨actualType,actualPointer,nextRegs,actualTyped,actualMapped,actualOutput,nextEq,execution,valueHeld,kept⟩ :=
    fallback_extend_selected_operand_values (stock_lower_record_context run scope events).1 signed installed source
      receipt.selected chosen refines prior.2.1 restrictedLookup grows
      (stock_lower_blockScanAliasBounds run event events record records) restrictedHeld
  have typeEq := Option.some.inj (actualTyped.symm.trans typed)
  subst actualType
  have pointerEq := (Reg.vreg.inj (Option.some.inj (actualMapped.symm.trans mapped))).1
  subst actualPointer
  have scanFresh : (scanState record.input record.inst).base.nextVreg = dest := by
    rw [fresh]
    unfold scanState
    dsimp only
    split <;> rfl
  have actualCode : record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [(MInst.extend (.vreg (scanState record.input record.inst).base.nextVreg .int) (.vreg pointer .int)
        signed sourceType.bits target.width).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))] := by
    rw [chunk,scanFresh]
    rfl
  obtain ⟨nextWorld,executed,same⟩ := execution world
  have actualExecution : seqRun isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
        some (.fall nextRegs nextWorld) := by rw [actualCode];exact executed
  have statementResults : statement.results = [resultId] := by
    rw [← stock_lower_original_statement_results run scope events blockAt statementAt current installed source]
    exact results
  have actualValue : VHolds ⟨target,ScalarCast.extendBits signed target.width value.bits⟩ (nextRegs dest) := by
    rw [← scanFresh]
    exact valueHeld
  have postValues := stock_lower_pending_fresh_record_values run scope dominated events records blockAt statementAt current
    installed source results statementResults resultMap recorded emitted output (by omega) prior.2.2.2
    (stock_lower_fallback_extend_resolved_defs run scope dominated events records signed installed source recorded emitted selectedId)
    actualExecution actualValue
  have sourceOutcome : instOutcome env program before.1 before.2 (.extend (ScalarCast.extendOp signed) target x) =
      .ok ([⟨target,ScalarCast.extendBits signed target.width value.bits⟩],before.2) := by
    rw [valsEq,memoryEq] at evaluatedPlain
    cases signed <;> exact evaluatedPlain
  have originalStep : SourceInstResult env program event.ctx record.inst before after :=
    ⟨info,_,vals,sourceRegs,rest,actualAt,actualSource,body,evaluated,written,frame⟩
  obtain ⟨sourceMemory,updated⟩ := source_single_result_update installed source results originalStep sourceOutcome
  have postDFG := stock_lower_source_step_dfg run scope dominated events blockAt statementAt current prior.1 prior.2.1 originalStep
  have slots := source_steps_slots_frame (SourceSteps.cons originalStep (.nil after))
  refine ⟨nextRegs,nextWorld,actualExecution,same,(source_inst_result_function originalStep).trans prior.1,postDFG,?_,?_⟩
  · rw [slots,sourceMemory]
    exact stable _ _ _ _ same.toNF prior.2.2.1
  · exact pending_values_frame_regs updated postValues

end Backend.Stock.Proof.Acquire810
