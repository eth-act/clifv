import FV.Backend.Proof.StockForwardSourceOrder
import FV.Backend.Proof.StockCriticalCode
import FV.Backend.Proof.StockSelectedGraph
import FV.Backend.Proof.StockConditionalValues

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Every selected ordinary original successor occurs in the computed source graph. -/
theorem selected_source_edge {f : Clif.Function} {source : Array (Array Nat)}
    (computed : stockSourceTable f = .ok source) {bi ti index : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (block : f.blocks[bi]? = some b) (selected : (dests b.term)[index]? = some bc)
    (lookup : blockIdx? f bc.block = some ti) : ti ∈ source[bi]!.toList := by
  have destination : (destinations b.term)[index]? = some (bc.block,bc.args.map Clif.TryArg.val) := by
    have same : destinations b.term = (dests b.term).map (fun bc => (bc.block,bc.args.map Clif.TryArg.val)) := by
      cases term : b.term <;> simp_all [dests,destinations,List.map_map,Function.comp_def]
    simp only [same,List.getElem?_map,selected,Option.map_some]
  obtain ⟨row,mapped,found⟩ := (Prep.amapM_ok computed).2 bi b (by simpa only [List.getElem?_toArray] using block)
  obtain ⟨value,call,present⟩ := (Prep.amapM_ok mapped).2 index _
    (by simpa only [List.getElem?_toArray] using destination)
  have identified : f.blocks.findIdx? (·.id == bc.block) = some ti := lookup
  have equal : ti = value := by simpa only [identified,pure,Except.pure,Except.ok.injEq] using call
  subst value
  have member : ti ∈ row.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? present)
  simpa only [getElem!_def,found,Option.getD_some] using member

/-- Selected successors of any ranked original block have later actual Stock labels. -/
theorem selected_ranked_target {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ranked : Ranked f rank)
    {label bi index : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (block : f.blocks[bi]? = some b)
    (selected : (dests b.term)[index]? = some bc) :
    ∃ tl targetLabel target,blockIdx? f bc.block = some tl ∧ f.block? bc.block = some target ∧
      f.blocks[tl]? = some target ∧ result.order.nodes[targetLabel]? = some (.original tl) ∧
      tl ≠ 0 ∧ label < targetLabel := by
  obtain ⟨tl,middle,lookup,nonentry,successor,node⟩ := stock_lower_selected_successor run scope tag block selected
  have target : ∃ (targetLabel : Nat),result.order.nodes[targetLabel]? = some (.original tl) := by
    rcases node with original | synthetic
    · exact ⟨middle,original⟩
    · obtain ⟨input,next,args,targetLabel,call,successors,tag,placed⟩ := stock_lower_critical_code run synthetic
      exact ⟨targetLabel,tag⟩
  obtain ⟨targetLabel,targetTag⟩ := target
  obtain ⟨targetBlock,found,sourceBlock⟩ := block?_of_idx lookup
  obtain ⟨source,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have edge := selected_source_edge computed block selected lookup
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have later := successor_labels (stock_lower_order run) nonempty ranked computed tag targetTag edge
  exact ⟨tl,targetLabel,targetBlock,lookup,found,sourceBlock,targetTag,nonentry,later⟩


end Backend.Stock.Proof.ParameterCfg
