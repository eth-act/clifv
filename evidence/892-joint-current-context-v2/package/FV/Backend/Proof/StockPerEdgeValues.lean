import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.LowerCert
import FV.Backend.Proof.StockOrderGraph
import FV.Backend.Proof.StockOutgoingVectors
import FV.Backend.Proof.PerEdgeVCodeSem

/-! Original source binding and actual Stock per-successor copy semantics. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A directly lowered original target uses its actual selected Result.edgeArgs
vector, including multi-successor conditionals/tables that legacy branchArgs
cannot represent. Map, parameter and nonentry facts are derived internally. -/
theorem stock_lower_direct_per_edge_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {label bi index targetLabel tl : Nat} {b targetBlock : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (selected : (dests b.term)[index]? = some bc)
    (successor : result.order.successors[label]![index]? = some targetLabel)
    (targetTag : result.order.nodes[targetLabel]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    {fr fr' : Clif.Frame} (func : fr.func = f) (target : f.block? bc.block = some targetBlock)
    (entered : Clif.enterBlock fr bc = .ok fr') {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) tl 0)
    {ρ : Nat → CV} (held : ValuesHeld
      (fun x => x ∈ bc.args ∨ (needed x ∧ x ∉ targetBlock.params.map (·.1))) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ ρ',edgeEnvAt result.code result.edgeArgs label targetLabel index ρ = some ρ' ∧
      ValuesHeld needed result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  have arguments := stock_lower_selected_outgoing run scope tag source selected successor targetTag
  have targetSource := blockIdx_block targetIndex target
  have entry : tl ≠ 0 := by
    intro zero
    subst tl
    exact scope.noEntryPred b (List.mem_of_getElem? source) bc.block
      (edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))) targetIndex
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
    edgeEnvAt_eq targetPlaced arguments parameters length ρ,
    stock_lower_edge_values run scope dominated targetSource func target entered available held⟩

/-- A real synthetic node uses the same per-successor semantics, its actual
single outgoing vector, and the actual original target's parameters. -/
theorem stock_lower_critical_per_edge_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {label pred index tl : Nat} {b targetBlock : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.edge pred index tl))
    (source : f.blocks[pred]? = some b) (selected : (dests b.term)[index]? = some bc)
    (targetIndex : blockIdx? f bc.block = some tl)
    {fr fr' : Clif.Frame} (func : fr.func = f) (target : f.block? bc.block = some targetBlock)
    (entered : Clif.enterBlock fr bc = .ok fr') {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) tl 0)
    {ρ : Nat → CV} (held : ValuesHeld
      (fun x => x ∈ bc.args ∨ (needed x ∧ x ∉ targetBlock.params.map (·.1))) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ targetLabel ρ',result.order.nodes[targetLabel]? = some (.original tl) ∧
      result.order.successors[label]? = some #[targetLabel] ∧
      edgeEnvAt result.code result.edgeArgs label targetLabel 0 ρ = some ρ' ∧
      ValuesHeld needed result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  have arguments := stock_lower_critical_argument_vector run scope tag source selected
  obtain ⟨targetLabel,successors,targetTag⟩ := stock_lower_edge_successor run tag
  have targetSource := blockIdx_block targetIndex target
  have entry : tl ≠ 0 := by
    intro zero
    subst tl
    exact scope.noEntryPred b (List.mem_of_getElem? source) bc.block
      (edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))) targetIndex
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
  exact ⟨targetLabel,parCopyEnv ρ (edgeParamNumbers result targetBlock) (edgeArgumentNumbers result bc),
    targetTag,successors,edgeEnvAt_eq targetPlaced arguments parameters length ρ,
    stock_lower_edge_values run scope dominated targetSource func target entered available held⟩
end Backend.Stock.Proof
