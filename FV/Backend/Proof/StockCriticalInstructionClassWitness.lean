import FV.Backend.Proof.StockPreparedInstructionClasses
import FV.Backend.Proof.StockDriverAliasWitness
namespace Backend.Stock.Proof.CriticalInstructionClassWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.WholeInstructionClassDraft Backend.Stock.Proof.PreparedInstructionClassDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

/-- Both direct and indirect actual try-call pipelines retain the source's
unreachable predecessor, exercise a forced critical-edge node and have derived
operand classes in every actual returned and prepared instruction. -/
theorem stock_complete_critical_instruction_classes_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc),
      Stock.lower (CriticalSplitFixture.function indirect) = .ok result ∧
      LowerScope (CriticalSplitFixture.function indirect) ∧ Dominated (CriticalSplitFixture.function indirect) ∧
      ArityOk (CriticalSplitFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      (CriticalSplitFixture.function indirect).blocks.length = 3 ∧
      Node.original 2 ∉ result.order.nodes.toList ∧ result.order.nodes[1]? = some (.edge 0 0 1) ∧
      (∀ b ∈ result.code.blocks.toList,∀ i ∈ b.insts.toList,InstCls result.code.classes i) ∧
      (∀ b ∈ p.code.blocks.toList,∀ i ∈ b.insts.toList,InstCls p.code.classes i) := by
  rcases DriverAliasWitnessDraft.stock_complete_critical_driver_alias_classes_witness indirect with
    ⟨result,p,rf,af,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
      sourceBlocks,unreachable,edge,aliases,growth,table,empty,resolver⟩
  exact ⟨result,p,rf,af,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    sourceBlocks,unreachable,edge,stock_lower_instruction_classes scope lowered,
    stock_prepared_instruction_classes scope lowered prepared⟩
end Backend.Stock.Proof.CriticalInstructionClassWitnessDraft
