import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.LowerCert
import FV.Backend.Proof.StockCriticalCode
import FV.Backend.Proof.StockSelectedArguments

/-! Actual synthetic successor copies and source successor binding. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A real synthetic edge's actual VCode edgeEnv transfers the selected normal
source successor's values. Actual branchArgs/code/vector facts, destination
mapping and nonentry exclusion are derived; no numeric copy certificate. -/
theorem stock_lower_critical_edge_values {f : Clif.Function} {result : Result}
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
      edgeEnv result.code label targetLabel ρ = some ρ' ∧
      ValuesHeld needed result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  obtain ⟨input,next,args,targetLabel,call,successors,targetTag,placed⟩ := stock_lower_critical_code run tag
  have arguments := stock_branchArgs_selected_numbers run scope source selected call
  have targetSource := blockIdx_block targetIndex target
  have edge := edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))
  have entry : tl ≠ 0 := by
    intro zero
    subst tl
    exact scope.noEntryPred b (List.mem_of_getElem? source) bc.block edge targetIndex
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
    targetTag,successors,edgeEnv_eq placed targetPlaced arguments parameters length ρ,
    stock_lower_edge_values run scope dominated targetSource func target entered available held⟩
end Backend.Stock.Proof
