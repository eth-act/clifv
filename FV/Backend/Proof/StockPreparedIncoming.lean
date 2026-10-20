import FV.Backend.Proof.ReorderedGraphIncoming
import FV.Backend.Proof.StockPrepareNoSplit

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

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

/-- Every prepared block comes from a live actual Stock block, with the same
label. Distinct prepared indices have distinct origins; every actual prepared
incoming occurrence reflects to the same selected index in the actual emitted
graph. No block-kind or graph correspondence certificate is supplied. -/
theorem stock_prepared_incoming {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {p : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok p)
    {ss3 ps3 : Array (Array Nat)} (cfg3 : p.code.cfg = .ok (ss3,ps3)) :
    ∃ (ss0 ps0 : Array (Array Nat)) (origin : Nat → Nat),
      result.code.cfg = .ok (ss0,ps0) ∧
      (∀ (q : Nat),q < p.code.blocks.size →
        origin q < result.code.blocks.size ∧
        result.code.blocks[origin q]!.label = p.code.blocks[q]!.label ∧
        Prep.mk (reachable ss0) (origin q)) ∧
      (∀ (q r : Nat),q < p.code.blocks.size → r < p.code.blocks.size → origin q = origin r → q = r) ∧
      (∀ (q j target : Nat) (row : Array Nat),ss3[q]? = some row → row[j]? = some target →
        ∃ oldRow,result.order.successors[origin q]? = some oldRow ∧
          oldRow[j]? = some (origin target) ∧ oldRow.size = row.size) := by
  obtain ⟨ss0,ps0,cfg0,noCritical,ss1,ps1,ss2,ps2,st,cfg1,loop,empty,emptyRows,next,cfg2,sameGraph,resultEq⟩ :=
    stock_prepare_no_new_edges run scope raw
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨count,_⟩ := prepareAt_input_facts raw
  have keptBlocks := keptAt_blocks (ss := ss0) count
  have keptSpec : Prep.CfgSpec ((keptAt result.code result.edgeArgs ss0).map Prod.fst) ss1 := by
    rw [keptBlocks]
    exact Prep.cfg_spec cfg1
  have outer := outerLoopAt_inv keptSpec loop
  rw [keptBlocks] at outer
  have cs0 := Prep.cfg_spec cfg0
  have entry := (Prep.reachable_spec (Prep.succsIn_of cs0) (by rw [cs0.size]; omega)).2.1
  have keptNonempty := (Prep.keep_zero nonempty entry).1
  have keptLabels := Prep.keep_lbls labels (reachable ss0)
  have cfg2full : Prep.CfgSpec (st.2.1 ++ st.2.2.2.1) ss2 := by
    rw [empty,Array.append_empty]
    exact Prep.cfg_spec cfg2
  obtain ⟨labelsB,bounds,distinct,rest⟩ := outer_order_facts outer (Prep.cfg_spec cfg1) cfg2full keptLabels keptNonempty
  rw [empty,Array.append_empty] at labelsB bounds
  have sizeB : st.2.1.size = (Prep.keep result.code.blocks (reachable ss0)).size := outer.graph.size
  have preparedBlocks : p.code.blocks = (rpo ss2).map fun i => st.2.1[i]! := by rw [resultEq]
  let origin : Nat → Nat := fun q => keepOrigin result.code.blocks (reachable ss0) (rpo ss2)[q]!
  have orderBound : ∀ q,q < p.code.blocks.size → q < (rpo ss2).size := by
    intro q bound
    rw [preparedBlocks,Array.size_map] at bound
    exact bound
  have keptBound : ∀ q,q < p.code.blocks.size → (rpo ss2)[q]! < (Prep.keep result.code.blocks (reachable ss0)).size := by
    intro q bound
    rw [getElem!_pos (rpo ss2) q (orderBound q bound),← sizeB]
    exact bounds _ (Array.getElem_mem_toList (orderBound q bound))
  have provenance : ∀ q,q < p.code.blocks.size →
      origin q < result.code.blocks.size ∧ result.code.blocks[origin q]!.label = p.code.blocks[q]!.label ∧
      Prep.mk (reachable ss0) (origin q) := by
    intro q bound
    have hb := keptBound q bound
    obtain ⟨oldBound,source⟩ := keepOrigin_spec labels hb
    have atB : (rpo ss2)[q]! < st.2.1.size := by rw [sizeB]; exact hb
    have label := (Prep.rw_fields (outer.graph.rw (rpo ss2)[q]! hb atB)).1
    have block : p.code.blocks[q]! = st.2.1[(rpo ss2)[q]!] := by
      rw [preparedBlocks,getElem!_pos _ q (by simpa using orderBound q bound),Array.getElem_map]
      simpa only [getElem!_pos (rpo ss2) q (orderBound q bound)] using getElem!_pos st.2.1 ((rpo ss2)[q]!) atB
    obtain ⟨old,hOld,oldBlock,live⟩ := Prep.keep_src hb
    have same : old = origin q := by
      apply Prep.lbl_inj labels hOld oldBound
      change result.code.blocks[old].label = result.code.blocks[keepOrigin result.code.blocks (reachable ss0) (rpo ss2)[q]!].label
      rw [← oldBlock,source]
    refine ⟨oldBound,?_,by simpa only [same] using live⟩
    change result.code.blocks[keepOrigin result.code.blocks (reachable ss0) (rpo ss2)[q]!]!.label = _
    rw [getElem!_pos result.code.blocks (keepOrigin result.code.blocks (reachable ss0) (rpo ss2)[q]!) oldBound,← source,block,label]
  refine ⟨ss0,ps0,origin,cfg0,provenance,?_,?_⟩
  · intro q r qBound rBound same
    have keptSame := keepOrigin_injective labels (keptBound q qBound) (keptBound r rBound) same
    exact reorder_index_injective distinct (orderBound q qBound) (orderBound r rBound) keptSame
  · intro q j target row atRow edge
    have cfg3' : ({result.code with blocks := (rpo ss2).map fun i => st.2.1[i]!} : VCode).cfg = .ok (ss3,ps3) := by
      rw [← preparedBlocks]
      have fields : ({result.code with blocks := p.code.blocks} : VCode) = p.code := by
        rw [resultEq]
      rw [fields]
      exact cfg3
    obtain ⟨midRow,midAt,midEdge,midSize⟩ := reorder_cfg_edge bounds labelsB cfg2 cfg3' atRow edge
    have midAt' : ss1[(rpo ss2)[q]!]? = some midRow := by
      rw [← sameGraph]
      exact midAt
    have cfg1' : ({result.code with blocks := Prep.keep result.code.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1) := cfg1
    obtain ⟨oldRow,oldAt,oldEdge,oldSize⟩ := keep_cfg_edge cfg0 cfg1' labels midAt' midEdge
    have actual := cfgSpec_unique cs0 (stock_lower_cfg run scope)
    have oldAt' : result.order.successors[origin q]? = some oldRow := by
      rw [← actual]
      exact oldAt
    exact ⟨oldRow,oldAt',oldEdge,oldSize.trans midSize⟩

end Backend.Stock.Proof
