import FV.Backend.Proof.StockCoreClassContracts
import FV.Backend.Proof.StockCoreFormWitness
namespace Backend.Stock.Proof.CoreClassWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BranchClassDraft Backend.Stock.Proof.CoreClassDraft Backend.Stock.Proof.OperandClassDraft Backend.Stock.Proof.ClassGrowthDraft
open Backend.Stock.Proof.Coverage
open Backend.Stock.Proof.EmissionCoverageFixture Backend.Stock.Proof.Coverage.CoreDraftObservation
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower emitBranch lowerBlockCore

/-- A complete original comparing-branch source exercises both real branch and
built-core class theorems. Nonempty ordinary instructions occur in both outputs. -/
theorem stock_complete_branch_core_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (core : LoweredBlockCore) (emission : BranchEmission) (i j : MInst),
      Stock.lower (function true) = .ok result ∧ LowerScope (function true) ∧
      Dominated (function true) ∧ ArityOk (function true) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function true) = .ok (result.ctx,ranges,result.initial) ∧
      (function true).blocks[0]? = some (sourceBlock true) ∧ ranges[0]? = some (0,2) ∧
      blockData (function true) (sourceBlock true).term = .ok (data true) ∧
      Clean (context true result) ∧ ClsIs (context true result) result.initial.base result.initial.base ∧
      emitBranch (context true result) (function true) (sourceBlock true).term 0 1
        result.order.successors[0]! result.initial = .ok emission ∧
      ClassGrowth result.initial emission.state ∧
      (∀ m ∈ emission.code.toList,RegsFrom (RegCls emission.state.base.classes) m ∧ InstCls emission.state.base.classes m) ∧
      j ∈ emission.code.toList ∧ j.isCtl = false ∧ InstCls emission.state.base.classes j ∧
      lowerBlockCore result.ctx result.order (function true) (sourceBlock true) 0 0 2
        (data true) result.order.successors[0]! result.initial = .ok core ∧
      ClassGrowth result.initial core.state ∧
      (∀ m ∈ core.code.toList,RegsFrom (RegCls core.state.base.classes) m ∧ InstCls core.state.base.classes m) ∧
      i ∈ core.code.toList ∧ i.isCtl = false ∧ InstCls core.state.base.classes i := by
  rcases Coverage.CoreDraftWitness.stock_complete_core_form_witness true with
    ⟨result,p,rf,af,ranges,core,br,i,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
      build,block,rangeRun,dataRun,mapped,clean,coreRun,coreForms,member,ordinary,form,static,
      branchShape,branches,nonempty⟩
  obtain ⟨emission,j,selected,jmember,jordinary,jform,jstatic⟩ := nonempty rfl
  have branchRun := (branches emission selected).1
  have initial : ClsIs (context true result) result.initial.base result.initial.base :=
    stock_build_term_classInvariant build 1 (data true)
  have branchClasses := stock_emitBranch_classes (ctx := context true result) clean initial branchRun
  have coreClasses := stock_built_core_classes build scope block rangeRun dataRun (clsStep_refl _) rfl coreRun
  exact ⟨result,p,rf,af,ranges,core,emission,i,j,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    build,block,rangeRun,dataRun,clean,initial,branchRun,branchClasses.1,branchClasses.2.2,
    jmember,jordinary,(branchClasses.2.2 j jmember).2,coreRun,coreClasses.1,coreClasses.2,
    member,ordinary,(coreClasses.2 i member).2⟩
end Backend.Stock.Proof.CoreClassWitnessDraft
