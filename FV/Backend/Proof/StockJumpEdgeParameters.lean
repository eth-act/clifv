import FV.Backend.Proof.StockJumpDemand
import FV.Backend.Proof.StockPerEdgeValues
import FV.Backend.Proof.LowerShapeOkFacts

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual post-body argument values execute the real per-successor copies and
establish every target parameter. This discharges parameter binding; inherited
nonparameter values remain a separate cross-block invariant. -/
theorem stock_jump_body_direct_parameter_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc) {tl : Nat} {targetBlock : Clif.Block}
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (target : f.block? bc.block = some targetBlock)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ w) :
    ∃ ρ',edgeEnvAt result.code result.edgeArgs label spec.target 0 ρ = some ρ' ∧
      ValuesHeld (fun x => x ∈ targetBlock.params.map (·.1)) result.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have arguments := stock_jump_body_argument_values run scope dominated spec jump targetTag held
  have targetSource := blockIdx_block targetIndex target
  have available : ∀ x,x ∈ targetBlock.params.map (·.1) →
      x ∈ availOf f (availIn f result.ctx) tl 0 := by
    intro x member
    apply (mem_av targetSource).mpr
    refine ⟨Or.inl member,?_⟩
    rintro ⟨j,stm,_,found,result⟩
    exact param_not_result dominated.ssa (List.mem_of_getElem? targetSource)
      (List.mem_of_getElem? targetSource) member
      (List.mem_flatMap.mpr ⟨stm,List.mem_of_getElem? found,result⟩)
  have successor : result.order.successors[label]![0]? = some spec.target := by
    have same : result.order.successors[label]! = #[spec.target] := Array.toList_inj.mp spec.targets
    rw [same]
    rfl
  apply stock_lower_direct_per_edge_values run scope dominated tag source
    (by rw [jump]; rfl) successor targetTag targetIndex held.1 target entered available
  intro x needed
  rcases needed with argument | ⟨parameter,notParameter⟩
  · exact arguments x argument
  · exact False.elim (notParameter parameter)

end Backend.Stock.Proof.Control
