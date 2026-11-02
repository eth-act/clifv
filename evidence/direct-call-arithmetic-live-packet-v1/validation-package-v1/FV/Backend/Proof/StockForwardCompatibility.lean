import FV.Backend.Proof.StockGraphEdges
import FV.Backend.Proof.StockForwardReturn
import FV.Backend.Proof.StockForwardLeaf
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockGraphBounds
import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockOutgoingVectors
import FV.Backend.Proof.PerEdgeLegacyCompatible

namespace Backend.Stock.Proof.ForwardSource
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Arbitrary jump/return/trap source graphs retain exactly the argument vectors
consumed by the existing compiler/checker/linker/generated-proof contract. -/
theorem legacy_compatible_of_leaf {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (terms : JumpLeafBlocks f) :
    EdgeLegacyCompatible result.code result.edgeArgs := by
  obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
  have sizes := (stock_lower_graph_bounds run).1
  have nodes : result.code.blocks.size = result.order.nodes.size :=
    (stock_prepare_dimensions run).1.symm.trans (stock_prepare_dimensions run).2.1
  intro label index target selected
  simp only [succOf,cfg] at selected
  cases row : result.order.successors[label]? with
  | none => simp only [row,Option.bind_none] at selected; cases selected
  | some ss =>
    simp only [row,Option.bind_some] at selected
    have labelBound : label < result.order.nodes.size := by
      have bound := (Array.getElem?_eq_some_iff.mp row).1
      omega
    cases tag : result.order.nodes[label]? with
    | none => have absent := Array.getElem?_eq_none_iff.mp tag; omega
    | some node =>
      cases node with
      | edge pred k ti =>
        obtain ⟨b,id,args,source,destination,found⟩ := stock_lower_critical_source run tag
        rcases terms b (List.mem_of_getElem? source) with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,trap⟩
        · exact False.elim (CriticalOwners.jump_no_edge (stock_lower_order run) source jump k ti
            (Array.mem_toList_iff.mpr (Array.mem_of_getElem? tag)))
        · simp only [ret,destinations,List.getElem?_nil] at destination; cases destination
        · simp only [trap,destinations,List.getElem?_nil] at destination; cases destination
      | original bi =>
        obtain ⟨b,id,args,ti,source,destination,found,targetNode⟩ :=
          stock_lower_indexed_successor_origin run tag row selected
        rcases terms b (List.mem_of_getElem? source) with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,trap⟩
        · have only : index = 0 := by
            cases index with
            | zero => rfl
            | succ index => simp [jump,destinations] at destination
          subst index
          obtain ⟨tl,targetLabel,identified,nonentry,successors,targetTag⟩ :=
            CriticalOwners.jump_successor run scope tag source jump
          have sameRow : ss = #[targetLabel] := Option.some.inj (row.symm.trans successors)
          have sameTarget : targetLabel = target := by simpa [sameRow] using selected
          subst targetLabel
          have successorsBang : result.order.successors[label]! = #[target] := by
            simp only [getElem!_def,successors,Option.getD_some]
          obtain ⟨vb,placed,labelled,arguments⟩ := stock_lower_original_jump_args run scope tag source jump successorsBang targetTag
          have vector := stock_lower_selected_outgoing run scope tag source
            (bc := bc) (index := 0) (by simp [jump,dests])
            (by simpa only [getElem!_def,row,Option.getD_some] using selected) targetTag
          exact ⟨vb,placed,by simpa only [outgoingAt,arguments] using vector⟩
        · simp only [ret,destinations,List.getElem?_nil] at destination; cases destination
        · simp only [trap,destinations,List.getElem?_nil] at destination; cases destination

/-- Arbitrary jump/return source graphs retain exactly the argument vectors
consumed by the existing compiler/checker/linker/generated-proof contract. -/
theorem legacy_compatible {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (terms : JumpReturnBlocks f) :
    EdgeLegacyCompatible result.code result.edgeArgs :=
  legacy_compatible_of_leaf run scope terms.toLeaf

end Backend.Stock.Proof.ForwardSource
