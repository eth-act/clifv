import FV.Backend.Proof.StockConditionalRankedShape
import FV.Backend.Proof.StockConditionalBodyCalls
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockGraphEdges
import FV.Backend.Proof.StockGraphBounds
import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockBranchArgumentDemand
import FV.Backend.Proof.StockOutgoingVectors
import FV.Backend.Proof.PerEdgeLegacyCompatible

namespace Backend.Stock.ConditionalCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem selected_empty {f : Clif.Function} (shape : RankedLeafShape f)
    {bi index id : Nat} {b : Clif.Block} {args : List Clif.TryArg}
    (source : f.blocks[bi]? = some b) (selected : (destinations b.term)[index]? = some (id,args)) (entry : bi = 0) :
    bi = 0 ∧ b = shape.entry ∧ ∃ bc,(dests b.term)[index]? = some bc ∧ bc.args = [] := by
  subst bi
  have same : b = shape.entry := Option.some.inj (source.symm.trans shape.source)
  subst b
  refine ⟨rfl,rfl,?_⟩
  cases index with
  | zero => exact ⟨shape.yes,by simp [shape.term,dests],(shape.targets shape.yes (Or.inl rfl)).1⟩
  | succ index =>
    cases index with
    | zero => exact ⟨shape.no,by simp [shape.term,dests],(shape.targets shape.no (Or.inr rfl)).1⟩
    | succ index => simp [shape.term,destinations] at selected

private theorem assembled_arguments {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.branchArgs = (if targets.size == 1 then outgoing[0]! else #[]) := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; simp_all

/-- The compatible source class derives exact agreement with the existing
single-vector edge interface, including actual synthetic critical-edge blocks.
Tail blocks may also end in `trap`, which has no outgoing edge. -/
theorem RankedLeafShape.legacy_compatible {f : Clif.Function} {result : Result}
    (shape : RankedLeafShape f) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result shape.entry 0 0 shape.condition shape.yes shape.no isem MR env cp) :
    EdgeLegacyCompatible result.code result.edgeArgs := by
  have inv := buildCtx_mappedInv scope spec.build
  have metadata := shape.condition_metadata dominated spec.build
  obtain ⟨calls,condition⟩ := spec.parameter_calls shape.source shape.term metadata.1
  have targetCount : result.order.successors[0]!.size = 2 := by
    have size := congrArg List.length calls.labels_eq
    simpa only [Array.length_toList,List.length_cons,List.length_nil] using size
  have rawArgs : spec.raw.branchArgs = #[] := by
    have args := assembled_arguments spec.assembled
    simpa only [targetCount,show (2 == 1) = false from rfl,Bool.false_eq_true,if_false] using args
  obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
  have sizes := (stock_lower_graph_bounds run).1
  have nodes : result.code.blocks.size = result.order.nodes.size :=
    (stock_prepare_dimensions run).1.symm.trans (stock_prepare_dimensions run).2.1
  have entryTag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
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
      | original bi =>
        obtain ⟨b,id,args,ti,source,destination,found,targetNode⟩ :=
          stock_lower_indexed_successor_origin run tag row selected
        by_cases isEntry : bi = 0
        ·
          obtain ⟨rfl,rfl,bc,selectedBc,empty⟩ := selected_empty shape source destination isEntry
          have labelEq := stock_blockOrder_original_unique (stock_lower_order run)
            (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) tag entryTag
          subst label
          have successor : result.order.successors[0]![index]? = some target := by
            simpa only [getElem!_def,row,Option.getD_some] using selected
          have vector : outgoingAt result 0 index = some #[] := by
            rcases targetNode with original | synthetic
            · have actual := stock_lower_selected_outgoing run scope tag shape.source selectedBc successor original
              simpa only [edgeArgumentNumbers,empty,List.map_nil] using actual
            · exact stock_lower_deferred_outgoing run tag successor synthetic
          refine ⟨_,spec.placed,?_⟩
          simpa only [outgoingAt,rawArgs,Array.map_empty] using vector
        · rcases shape.tails bi b source isEntry with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,trap⟩
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
      | edge pred k ti =>
        obtain ⟨b,id,args,source,destination,found⟩ := stock_lower_critical_source run tag
        have isEntry : pred = 0 := by
          apply Classical.byContradiction
          intro nonentry
          rcases shape.tails pred b source nonentry with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,trap⟩
          · exact CriticalOwners.jump_no_edge (stock_lower_order run) source jump k ti
              (Array.mem_toList_iff.mpr (Array.mem_of_getElem? tag))
          · simp only [ret,destinations,List.getElem?_nil] at destination; cases destination
          · simp only [trap,destinations,List.getElem?_nil] at destination; cases destination
        obtain ⟨rfl,rfl,bc,selectedBc,empty⟩ := selected_empty shape source destination isEntry
        obtain ⟨input,next,registers,targetLabel,call,successors,targetTag,placed⟩ :=
          stock_lower_critical_code run tag
        have sameRow : ss = #[targetLabel] := Option.some.inj (row.symm.trans successors)
        have zero : index = 0 := by
          cases index with
          | zero => rfl
          | succ index => simp [sameRow] at selected
        subst index
        have mapping := stock_branchArgs_selected_mapping inv.func shape.source selectedBc call
        have noRegisters : registers = #[] := by
          rw [empty] at mapping
          simp only [List.mapM_nil,Option.pure_def,Option.some.injEq] at mapping
          exact Array.toList_inj.mp mapping.symm
        have vector := stock_lower_critical_argument_vector run scope tag shape.source selectedBc
        refine ⟨_,placed,?_⟩
        simpa only [outgoingAt,edgeArgumentNumbers,empty,List.map_nil,
          noRegisters,Array.map_empty] using vector

/-- The compatible source class derives exact agreement with the existing
single-vector edge interface, including actual synthetic critical-edge blocks. -/
theorem RankedShape.legacy_compatible {f : Clif.Function} {result : Result}
    (shape : RankedShape f) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result shape.entry 0 0 shape.condition shape.yes shape.no isem MR env cp) :
    EdgeLegacyCompatible result.code result.edgeArgs :=
  shape.toLeaf.legacy_compatible run scope dominated spec

end Backend.Stock.ConditionalCfg
