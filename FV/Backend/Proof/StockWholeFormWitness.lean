import FV.Backend.Proof.StockPreparedFormContracts
import FV.Backend.Proof.StockWholeFormObservation
import FV.Backend.Proof.StockOrdinaryCfg
import FV.Backend.Proof.StockEntryOrder

namespace Backend.Stock.Proof.Coverage.WholeFormsWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.Coverage.CoreDraft Backend.Stock.Proof.Coverage.EntryDraft
open Backend.Stock.Proof.Coverage.WholeFormsDraft Backend.Stock.Proof.Coverage.PreparedFormsDraft
open Backend.Stock.Proof.Coverage.WholeFormsFixture
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore assembleOriginalBlock

/-- Complete original source conditions and actual raw/checked/physical stages
inhabit whole Stock/prepared coverage and the real entry assembly contract.
The returned entry contains both ABI argument materialization and a genuine
non-control stack load; core/assembly calls are extracted from that same run. -/
theorem stock_whole_forms_entry_witness :
    ∃ (result : Backend.Stock.Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (bytes : List Nat) (input : State) (data : V)
      (core : LoweredBlockCore) (assembled final : VBlock) (preludeCode : Array MInst) (args load : MInst),
      Stock.lower entryFunction = .ok result ∧ LowerScope entryFunction ∧
      Dominated entryFunction ∧ ArityOk entryFunction ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx entryFunction = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order entryFunction entryFunction.blocks[0]! 0 0 1 data
        result.order.successors[0]! input = .ok core ∧
      assembleOriginalBlock result.ctx entryFunction entryFunction.blocks[0]! 0 0 result.order.successors[0]!
        core.outgoing bytes core.state.uses core.code = .ok assembled ∧
      assembled.insts = preludeCode ++ core.code ∧
      (∀ i ∈ core.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i)) ∧
      (∀ i ∈ assembled.insts.toList,Covered i = true) ∧
      result.code.blocks[0]? = some final ∧
      final = {assembled with
        insts := assembled.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := assembled.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := assembled.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} ∧
      (∀ b ∈ result.code.blocks.toList,∀ i ∈ b.insts.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i)) ∧
      FormsCovered default result.code ∧
      (∀ b ∈ p.code.blocks.toList,∀ i ∈ b.insts.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i)) ∧
      FormsCovered default p.code ∧
      args ∈ final.insts.toList ∧ isArgs args = true ∧ load ∈ final.insts.toList ∧
      isFrameLoad load = true ∧ load.isCtl = false ∧ Covered load = true ∧ SpillInstOk load := by
  have actual := observed
  unfold Observed at actual
  cases run : pipeline with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq] at actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    cases h
    have accepted := PerEdge.allocResultAt_checked selected
    have fallback : rf = spillAllocAt prepared.code prepared.edges := by
      unfold allocResultAt checkedSpillAt at selected
      simp only [bind,Except.bind] at selected
      split at selected <;> cases selected
      rfl
    cases finalAt : result.code.blocks[0]? with
    | none => simp [finalAt] at actual
    | some final =>
      rw [finalAt] at actual
      simp only [Option.map_some,Option.some.injEq,Bool.and_eq_true] at actual
      obtain ⟨args,argMember,argTag⟩ := Array.any_eq_true'.mp actual.1
      obtain ⟨load,loadMember,loadTag⟩ := Array.any_eq_true'.mp actual.2
      have argMember : args ∈ final.insts.toList := Array.mem_toList_iff.mpr argMember
      have loadMember : load ∈ final.insts.toList := Array.mem_toList_iff.mpr loadMember
      have nonControl : load.isCtl = false := by
        cases load <;> simp only [isFrameLoad] at loadTag
        all_goals try contradiction
        all_goals rfl
      have covered := stock_lower_form_coverage lowered source_scope
      have preparedForms := stock_prepared_form_coverage lowered source_scope prepare
      have form := covered final (Array.mem_toList_iff.mpr (Array.mem_of_getElem? finalAt)) load loadMember
      have entry := stock_blockOrder_entry (stock_lower_order lowered) source_scope.nonempty
      obtain ⟨ranges,bytes,input,data,core,assembled,preludeCode,coreRun,assemblyRun,build,dataRun,placed,code⟩ :=
        OrdinaryCfg.stock_lower_original_code_origin lowered entry
      obtain ⟨original,oldState,legacy,spec,view⟩ := buildCtx_source build
      have block : entryFunction.blocks[0]? = some entryFunction.blocks[0]! := rfl
      have rangeRun : ranges[0]? = some (0,1) := spec.ranges 0 _ block
      have range : ranges[0]! = (0,1) := by simp only [getElem!_def,rangeRun,Option.getD_some]
      rw [range] at coreRun
      have coreForms := stock_blockCore_form_coverage build source_scope block rangeRun dataRun coreRun
      have assemblyForms := stock_assemble_form_coverage (buildCtx_mappedInv source_scope build).valueReg
        (fun i member => (coreForms i member).1) assemblyRun
      have finalEq := Option.some.inj (finalAt.symm.trans placed)
      exact ⟨result,prepared,rf,af,ranges,bytes,input,data,core,assembled,final,preludeCode,args,load,
        lowered,source_scope,source_dominated,source_arity,prepare,fallback,accepted,physical,build,coreRun,assemblyRun,
        code,coreForms,assemblyForms,finalAt,finalEq,covered,stock_lower_formsCovered lowered source_scope default,
        preparedForms,stock_prepared_formsCovered lowered source_scope prepare default,
        argMember,argTag,loadMember,loadTag,nonControl,form.1,form.2 nonControl⟩

end Backend.Stock.Proof.Coverage.WholeFormsWitness
