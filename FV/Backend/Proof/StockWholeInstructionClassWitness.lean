import FV.Backend.Proof.StockPreparedInstructionClasses
import FV.Backend.Proof.StockWholeFormWitness
import FV.Backend.Proof.StockDriverAliasWitness
namespace Backend.Stock.Proof.WholeInstructionClassWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.Coverage Backend.Stock.Proof.Coverage.WholeFormsFixture
open Backend.Stock.Proof.EntryClassDraft Backend.Stock.Proof.CoreClassDraft Backend.Stock.Proof.ClassGrowthDraft
open Backend.Stock.Proof.WholeInstructionClassDraft Backend.Stock.Proof.PreparedInstructionClassDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower lowerBlockCore assembleOriginalBlock

private theorem singleton_entry {result : Result} (run : Stock.lower entryFunction = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (bytes : List Nat) (data : V) (core : LoweredBlockCore) (assembled : VBlock),
      Stock.buildCtx entryFunction = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order entryFunction entryFunction.blocks[0]! 0 0 1 data
        result.order.successors[0]! result.initial = .ok core ∧
      blockData entryFunction entryFunction.blocks[0]!.term = .ok data ∧
      assembleOriginalBlock result.ctx entryFunction entryFunction.blocks[0]! 0 0 result.order.successors[0]!
        core.outgoing bytes core.state.uses core.code = .ok assembled := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built build _ order ordered _ driver folded
  have computed : blockOrder entryFunction = .ok ⟨#[.original 0],#[#[]]⟩ := by cbv
  have same : order = ⟨#[.original 0],#[#[]]⟩ := Except.ok.inj (ordered.symm.trans computed)
  subst order
  change [0].foldlM (fun d k => lowerNode built.1 built.2.1 ⟨#[.original 0],#[#[]]⟩ entryFunction _ k d) _ = Except.ok driver at folded
  rw [List.foldlM_cons] at folded
  obtain ⟨after,nodeRun,rest⟩ := Except.bind_ok folded
  rw [List.foldlM_nil] at rest
  cases rest
  obtain ⟨original,old,legacy,spec,view⟩ := buildCtx_source build
  have source : entryFunction.blocks[0]? = some entryFunction.blocks[0]! := rfl
  have rangeRun : built.2.1[0]? = some (0,1) := spec.ranges 0 _ source
  have range : built.2.1[0]! = (0,1) := by simp only [getElem!_def,rangeRun,Option.getD_some]
  unfold lowerNode at nodeRun
  dsimp only at nodeRun
  simp only [show (#[Node.original 0] : Array Node)[0]! = .original 0 from rfl] at nodeRun
  rw [range] at nodeRun
  repeat' first
    | (solve | cases nodeRun)
    | simp only [bind,Except.bind,pure,Except.pure] at nodeRun
    | split at nodeRun
  all_goals
    cases nodeRun
    exact ⟨_,_,_,_,_,build,by assumption,by assumption,by assumption⟩

/-- Complete nine-parameter source exercises actual ABI argument materialization
and a real non-control stack load. The same successful whole run and preparation
have instruction classes internally; the actual entry assembly contract has
construction-derived mapped classes and actual core-derived body classes. -/
theorem stock_complete_entry_instruction_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (bytes : List Nat) (data : V) (core : LoweredBlockCore)
      (assembled final : VBlock) (args load : MInst),
      Stock.lower entryFunction = .ok result ∧ LowerScope entryFunction ∧ Dominated entryFunction ∧ ArityOk entryFunction ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx entryFunction = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order entryFunction entryFunction.blocks[0]! 0 0 1 data
        result.order.successors[0]! result.initial = .ok core ∧
      assembleOriginalBlock result.ctx entryFunction entryFunction.blocks[0]! 0 0 result.order.successors[0]!
        core.outgoing bytes core.state.uses core.code = .ok assembled ∧
      (∀ v r,result.ctx.valueReg? v = some r → RegCls core.state.base.classes r) ∧
      (∀ i ∈ core.code.toList,RegsFrom (RegCls core.state.base.classes) i) ∧
      (∀ i ∈ assembled.insts.toList,RegsFrom (RegCls core.state.base.classes) i ∧ InstCls core.state.base.classes i) ∧
      (∀ b ∈ result.code.blocks.toList,∀ i ∈ b.insts.toList,InstCls result.code.classes i) ∧
      (∀ b ∈ p.code.blocks.toList,∀ i ∈ b.insts.toList,InstCls p.code.classes i) ∧
      result.code.blocks[0]? = some final ∧ args ∈ final.insts.toList ∧ isArgs args = true ∧
      load ∈ final.insts.toList ∧ isFrameLoad load = true ∧ load.isCtl = false ∧
      InstCls result.code.classes args ∧ InstCls result.code.classes load := by
  rcases Coverage.WholeFormsWitness.stock_whole_forms_entry_witness with
    ⟨result,p,rf,af,oldRanges,oldBytes,input,oldData,oldCore,oldAssembled,final,prelude,args,load,
      lowered,scope,dominated,arity,prepared,fallback,checked,physical,oldBuild,oldCoreRun,oldAssemblyRun,
      suffix,coreForms,assemblyForms,placed,finalEq,forms,formsCovered,prepForms,prepFormsCovered,
      argsMember,argsTag,loadMember,loadTag,ordinary,loadCovered,loadStatic⟩
  obtain ⟨ranges,bytes,data,core,assembled,build,coreRun,dataRun,assemblyRun⟩ := singleton_entry lowered
  obtain ⟨original,old,legacy,spec,view⟩ := buildCtx_source build
  have source : entryFunction.blocks[0]? = some entryFunction.blocks[0]! := rfl
  have rangeRun : ranges[0]? = some (0,1) := spec.ranges 0 _ source
  have bodyClasses := stock_built_core_classes build scope source rangeRun dataRun (clsStep_refl _) rfl coreRun
  have initial := InitialClassesDraft.stock_build_classes build
  have mapped : ∀ v r,result.ctx.valueReg? v = some r → RegCls core.state.base.classes r :=
    fun v r found => regCls_step bodyClasses.1 (initial.2.1 v r found)
  have body : ∀ i ∈ core.code.toList,RegsFrom (RegCls core.state.base.classes) i := fun i member => (bodyClasses.2 i member).1
  have assembly := stock_assemble_classes mapped body assemblyRun
  have whole := stock_lower_instruction_classes scope lowered
  have prep := stock_prepared_instruction_classes scope lowered prepared
  have finalMember := Array.mem_toList_iff.mpr (Array.mem_of_getElem? placed)
  exact ⟨result,p,rf,af,ranges,bytes,data,core,assembled,final,args,load,lowered,scope,dominated,arity,
    prepared,fallback,checked,physical,build,coreRun,assemblyRun,mapped,body,
    fun i member => ⟨assembly i member,instCls_of (assembly i member)⟩,whole,prep,placed,
    argsMember,argsTag,loadMember,loadTag,ordinary,whole final finalMember args argsMember,
    whole final finalMember load loadMember⟩
end Backend.Stock.Proof.WholeInstructionClassWitnessDraft
