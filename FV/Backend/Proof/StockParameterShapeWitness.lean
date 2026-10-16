import FV.Backend.Proof.PerEdgeParameterShape
import FV.Backend.Proof.PerEdgeSpillCycleFixture

namespace Backend.Stock.Proof.ParameterShapeWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.IndexedSpillFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A complete actual cyclic Stock source inhabits universal parameter shape
before and after indexed preparation. Its real loop parameters are nonempty,
the two actual parameter numbers are distinct, the indexed checker accepts the
fallback and physical lowering succeeds. All new metadata roots are instantiated
under original scope/dominance, without an added source checker. -/
theorem stock_parameter_shape_witness :
    ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      (∀ (b : Nat) (vb : VBlock),result.code.blocks[b]? = some vb → ParameterShape vb.params) ∧
      (edgeParamNumbers result function.blocks[1]!).Nodup ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true ∧
      (∀ (b : Nat) (vb : VBlock),prepared.code.blocks[b]? = some vb → ParameterShape vb.params) ∧
      (prepared.code.blocks[1]!).params = #[.vreg 194 .int,.vreg 195 .int] ∧
      rf = spillAllocAt prepared.code prepared.edges ∧
      checkAllocAt prepared.code prepared.edges rf = .ok () ∧ lowerRFunc prepared.code rf = .ok af := by
  obtain ⟨f⟩ := cycle_fixture
  rcases f with ⟨result,prepared,rf,af,run,scope,dominated,raw,fallback,accepted,physical,
    count,edgeRow,params,codeSize,installed,first,second⟩
  have original := stock_lower_parameter_shape run scope dominated.ssa
  have numbers := stock_parameter_numbers_nodup run scope dominated.ssa
    (tl := 1) (b := function.blocks[1]!) (by rfl)
  obtain ⟨p,raw',checked,prepAccepted,shaped⟩ := stock_prepare_parameter_shape run scope dominated.ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst p
  exact ⟨result,prepared,rf,af,run,scope,dominated,original,numbers,raw,checked,prepAccepted,
    shaped,params,fallback,accepted,physical⟩

end Backend.Stock.Proof.ParameterShapeWitness
