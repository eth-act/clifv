import FV.Backend.Proof.StockPreparedClasses
import FV.Backend.Proof.StockCriticalInstructionClassWitness
import FV.Backend.Proof.StockCriticalEdgeArity
namespace Backend.Stock.Proof.CriticalClassesWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.Coverage
open Backend.Stock.Proof.WholeClassesDraft Backend.Stock.Proof.PreparedClassesDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

/-- Direct and indirect original try-call sources exercise real nonempty
critical-edge arguments, source parameters and both complete class consumers.
The original unreachable predecessor stays in the source and forces splitting. -/
theorem stock_complete_critical_classes_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (args : Array Reg) (r : Reg),
      Stock.lower (CriticalSplitFixture.function indirect) = .ok result ∧
      LowerScope (CriticalSplitFixture.function indirect) ∧ Dominated (CriticalSplitFixture.function indirect) ∧
      ArityOk (CriticalSplitFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      (CriticalSplitFixture.function indirect).blocks.length = 3 ∧
      Node.original 2 ∉ result.order.nodes.toList ∧ result.order.nodes[1]? = some (.edge 0 0 1) ∧
      ClassesOkM result.code ∧ ClassesOk result.code ∧
      (∀ b ∈ result.code.blocks.toList,∀ r ∈ b.params.toList ++ b.branchArgs.toList,IntCls result.code.classes r) ∧
      (∀ row ∈ result.edgeArgs.toList,∀ args ∈ row.toList,∀ r ∈ args.toList,IntCls result.code.classes r) ∧
      ClassesOkM p.code ∧ ClassesOk p.code ∧
      (∀ row ∈ p.edges.toList,∀ args ∈ row.toList,∀ r ∈ args.toList,IntCls p.code.classes r) ∧
      result.edgeArgs[1]? = some #[args] ∧ args.size = 1 ∧ args[0]? = some r ∧ IntCls result.code.classes r := by
  rcases CriticalInstructionClassWitnessDraft.stock_complete_critical_instruction_classes_witness indirect with
    ⟨result,p,rf,af,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
      sourceBlocks,unreachable,edge,rawInsts,preparedInsts⟩
  have raw := stock_lower_classes scope lowered
  have prep := stock_prepared_classes scope lowered prepared
  obtain ⟨label,tb,args,successor,target,atTarget,outgoing,count⟩ :=
    stock_lower_critical_edge_arity lowered scope dominated.ssa edge
  have source : (CriticalSplitFixture.function indirect).blocks[1]? =
      some (CriticalSplitFixture.function indirect).blocks[1]! := by cases indirect <;> rfl
  obtain ⟨actual,atActual,labelled,parameters⟩ := stock_lower_original_block_params lowered scope dominated.ssa target source (by decide)
  have same := Option.some.inj (atTarget.symm.trans atActual)
  subst actual
  have one : args.size = 1 := by
    rw [count,parameters]
    simp only [List.size_toArray,List.length_map,edgeParamNumbers]
    cases indirect <;> rfl
  have bound : 0 < args.size := by rw [one]; decide
  let r := args[0]
  have atReg : args[0]? = some r := Array.getElem?_eq_getElem bound
  have classed := raw.2.2 #[args] (Array.mem_toList_iff.mpr (Array.mem_of_getElem? outgoing)) args
    (by simp) r (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atReg))
  exact ⟨result,p,rf,af,args,r,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    sourceBlocks,unreachable,edge,raw.1,raw.2.1,stock_lower_integer_block_classes scope lowered,raw.2.2,
    prep.1,prep.2.1,prep.2.2,outgoing,one,atReg,classed⟩
end Backend.Stock.Proof.CriticalClassesWitnessDraft
