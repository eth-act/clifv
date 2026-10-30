import FV.Backend.Proof.StockPrepareComplete
import FV.Backend.Proof.StockEntryCode
import FV.Backend.Proof.StockEntryGraph
import FV.Backend.Proof.StockPrepareInputs
import FV.Backend.Proof.PerEdgePrepareInputTotal

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

private theorem cfgSpec_unique {V : Array VBlock} {ss ss' : Array (Array Nat)}
    (left : Prep.CfgSpec V ss) (right : Prep.CfgSpec V ss') : ss = ss' := by
  apply Array.ext
  · rw [left.size,right.size]
  · intro b hb hb'
    have hV : b < V.size := by rw [← left.size]; exact hb
    obtain ⟨t,sb,back,_,atRow,count,targets⟩ := left.blk b V[b] (Array.getElem?_eq_getElem hV)
    obtain ⟨t',sb',back',_,atRow',count',targets'⟩ := right.blk b V[b] (Array.getElem?_eq_getElem hV)
    rw [back] at back'
    cases back'
    have row : ss[b] = sb := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb]; exact atRow)
    have row' : ss'[b] = sb' := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb']; exact atRow')
    rw [row,row']
    apply Array.ext
    · rw [count,count']
    · intro j hj hj'
      obtain ⟨l,hl⟩ : ∃ l,t.targets[j]? = some l :=
        ⟨_,List.getElem?_eq_getElem (by rw [← count]; exact hj)⟩
      obtain ⟨s,hs,find⟩ := targets j l hl
      obtain ⟨s',hs',find'⟩ := targets' j l hl
      rw [find] at find'
      cases find'
      rw [Array.getElem?_eq_getElem hj] at hs
      rw [Array.getElem?_eq_getElem hj'] at hs'
      exact (Option.some.inj hs).trans (Option.some.inj hs').symm

private theorem cfg_of_spec {vc : VCode} {ss : Array (Array Nat)}
    (spec : Prep.CfgSpec vc.blocks ss) : ∃ ps,vc.cfg = .ok (ss,ps) := by
  have existsCfg : ∃ ss' ps',vc.cfg = .ok (ss',ps') := by
    apply Prep.cfg_of
    intro b vb lookup
    obtain ⟨t,sb,back,term,_,_,targets⟩ := spec.blk b vb lookup
    refine ⟨t,back,term,?_⟩
    intro l hl
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hl
    obtain ⟨s,_,find⟩ := targets j _ (List.getElem?_eq_getElem hj)
    exact ⟨s,find⟩
  obtain ⟨ss',ps',cfg⟩ := existsCfg
  have same := cfgSpec_unique (Prep.cfg_spec cfg) spec
  rw [same] at cfg
  exact ⟨ps',cfg⟩

/-- Internal composition for Stock raw/checked preparation: all entry, label,
no-entry and row obligations are derived from actual original-scope lowering.
The remaining obligation is correspondence between actual emitted terminators
and the already-computed graph; it must be proved, not supplied as a new source
program certificate at production cutover. -/
theorem stock_prepare_total_of_graph {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (graph : Prep.CfgSpec result.code.blocks result.order.successors) :
    ∃ prepared,prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨count,_,arity⟩ := stock_prepare_dimensions run
  obtain ⟨_,entry,atEntry,_,params⟩ := stock_lower_entry_code run scope
  have entryEq : result.code.blocks[0] = entry :=
    Option.some.inj (by rw [← Array.getElem?_eq_getElem nonempty]; exact atEntry)
  have parameterless : result.code.blocks[0].params = #[] := by rw [entryEq,params]
  have noTargets : ∀ b ∈ result.code.blocks.toList,∀ t,
      b.insts.back? = some t → result.code.blocks[0].label ∉ t.targets := by
    intro b member t back target
    obtain ⟨bi,hbi,equal⟩ := List.getElem_of_mem member
    have bound : bi < result.code.blocks.size := by simpa only [Array.length_toList] using hbi
    have lookup : result.code.blocks[bi]? = some b := by
      rw [Array.getElem?_eq_getElem bound]
      exact congrArg some (by simpa only [Array.getElem_toList] using equal)
    obtain ⟨t0,sb,back0,_,row,_,targets⟩ := graph.blk bi b lookup
    rw [back] at back0
    cases back0
    obtain ⟨j,hj,atLabel⟩ := List.getElem_of_mem target
    have atTarget : t.targets[j]? = some result.code.blocks[0].label := by
      rw [List.getElem?_eq_getElem hj,atLabel]
    obtain ⟨s,atS,find⟩ := targets j _ atTarget
    rw [Prep.lab_zero nonempty rfl] at find
    cases find
    exact stock_lower_graph_nonentry run scope bi sb row (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atS))
  obtain ⟨ps,cfg⟩ := cfg_of_spec graph
  exact PerEdgePrep.prepareCheckedAt_total cfg nonempty labels count arity parameterless noTargets

end Backend.Stock.Proof
