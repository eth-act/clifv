import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.StockEdgeCode

/-! Compose actual returned VCode edge fields with source successor binding.
The direct-original jump shape is a control-flow case; source scope/dominance
and successful executions retain their original meaning. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A jump to a directly lowered original successor transfers held values
through the actual VCode edgeEnv. Parameter/argument vectors and register-map
certificates are derived from whole lowering, rather than supplied by callers.
General CFG classification and world/DFG composition remain separate obligations. -/
theorem stock_lower_jump_edge_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {label bi targetLabel tl : Nat} {b targetBlock : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (term : b.term = .jump bc) (successors : result.order.successors[label]! = #[targetLabel])
    (targetTag : result.order.nodes[targetLabel]? = some (.original tl))
    (targetSource : f.blocks[tl]? = some targetBlock) (entry : tl ≠ 0)
    {fr fr' : Clif.Frame} (func : fr.func = f) (target : f.block? bc.block = some targetBlock)
    (entered : Clif.enterBlock fr bc = .ok fr') {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) tl 0)
    {ρ : Nat → CV} (held : ValuesHeld
      (fun x => x ∈ bc.args ∨ (needed x ∧ x ∉ targetBlock.params.map (·.1))) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ ρ',edgeEnv result.code label targetLabel ρ = some ρ' ∧
      ValuesHeld needed result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  obtain ⟨vb,placed,_,arguments⟩ := stock_lower_original_jump_args run scope tag source term successors targetTag
  obtain ⟨tb,targetPlaced,_,parameters⟩ := stock_lower_original_block_params run scope dominated.ssa
    targetTag targetSource entry
  obtain ⟨original,vals,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
  rw [func] at found
  cases Option.some.inj (found.symm.trans target)
  have sourceLength := (getMany_spec read).1
  have targetLength := setMany_length set
  have length : (edgeParamNumbers result targetBlock).length = (edgeArgumentNumbers result bc).length := by
    simp only [edgeParamNumbers,edgeArgumentNumbers,List.length_map]
    simp only [List.length_map] at targetLength
    omega
  exact ⟨parCopyEnv ρ (edgeParamNumbers result targetBlock) (edgeArgumentNumbers result bc),
    edgeEnv_eq placed targetPlaced arguments parameters length ρ,
    stock_lower_edge_values run scope dominated targetSource func target entered available held⟩
end Backend.Stock.Proof
