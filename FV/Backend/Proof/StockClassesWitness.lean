import FV.Backend.Proof.StockPreparedClasses
import FV.Backend.Proof.StockWholeFormWitness
namespace Backend.Stock.Proof.ClassesWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.Coverage Backend.Stock.Proof.Coverage.WholeFormsFixture
open Backend.Stock.Proof.WholeClassesDraft Backend.Stock.Proof.PreparedClassesDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

/-- Complete nine-parameter entry exercises actual argument materialization
and a real stack load with both full class interfaces and every indexed vector
classed in the actual returned and prepared programs. -/
theorem stock_complete_entry_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (final : VBlock) (args load : MInst),
      Stock.lower entryFunction = .ok result ∧ LowerScope entryFunction ∧ Dominated entryFunction ∧ ArityOk entryFunction ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      entryFunction.sig.params.length = 9 ∧
      ClassesOkM result.code ∧ ClassesOk result.code ∧
      (∀ b ∈ result.code.blocks.toList,∀ r ∈ b.params.toList ++ b.branchArgs.toList,IntCls result.code.classes r) ∧
      (∀ row ∈ result.edgeArgs.toList,∀ args ∈ row.toList,∀ r ∈ args.toList,IntCls result.code.classes r) ∧
      ClassesOkM p.code ∧ ClassesOk p.code ∧
      (∀ row ∈ p.edges.toList,∀ args ∈ row.toList,∀ r ∈ args.toList,IntCls p.code.classes r) ∧
      result.code.blocks[0]? = some final ∧ args ∈ final.insts.toList ∧ isArgs args = true ∧
      load ∈ final.insts.toList ∧ isFrameLoad load = true ∧ load.isCtl = false ∧
      InstCls result.code.classes args ∧ InstCls result.code.classes load := by
  rcases Coverage.WholeFormsWitness.stock_whole_forms_entry_witness with
    ⟨result,p,rf,af,ranges,bytes,input,data,core,assembled,final,prelude,args,load,
      lowered,scope,dominated,arity,prepared,fallback,checked,physical,build,coreRun,assemblyRun,
      suffix,coreForms,assemblyForms,placed,finalEq,forms,formsCovered,prepForms,prepFormsCovered,
      argsMember,argsTag,loadMember,loadTag,ordinary,loadCovered,loadStatic⟩
  have raw := stock_lower_classes scope lowered
  have prep := stock_prepared_classes scope lowered prepared
  have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? placed)
  exact ⟨result,p,rf,af,final,args,load,lowered,scope,dominated,arity,prepared,fallback,checked,physical,rfl,
    raw.1,raw.2.1,stock_lower_integer_block_classes scope lowered,raw.2.2,prep.1,prep.2.1,prep.2.2,
    placed,argsMember,argsTag,loadMember,loadTag,ordinary,raw.1.1 final member args argsMember,
    raw.1.1 final member load loadMember⟩

end Backend.Stock.Proof.ClassesWitnessDraft
