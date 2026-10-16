import FV.Backend.Proof.PerEdgePrepareUnsplitGraph
import FV.Backend.Proof.StockNoCriticalEdges

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual Stock has already split critical edges. Successful indexed
preparation therefore adds no further synthetic blocks, rows or fresh labels.
The graph property and label domain follow from the original source scope;
no additional source filter or preparation certificate is required. -/
theorem stock_prepare_no_new_edges {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {p : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok p) :
    ∃ (ss0 ps0 : Array (Array Nat)), result.code.cfg = .ok (ss0,ps0) ∧
      NoCriticalEdges ss0 ps0 ∧
    ∃ (ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
      ({result.code with blocks := Prep.keep result.code.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1) ∧
      forIn ((keptAt result.code result.edgeArgs ss0).map Prod.fst).zipIdx
        (Prep.next0Of ((keptAt result.code result.edgeArgs ss0).map Prod.fst),#[],#[],#[],#[])
        (outerStepAt ss1 ps1 ((keptAt result.code result.edgeArgs ss0).map Prod.snd)) = .ok st ∧
      st.2.2.2.1 = #[] ∧ st.2.2.2.2 = #[] ∧ st.1 = Prep.next0Of (Prep.keep result.code.blocks (reachable ss0)) ∧
      ({result.code with blocks := st.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
      ss2 = ss1 ∧
      p = ⟨{result.code with blocks := (rpo ss2).map fun i => st.2.1[i]!},(rpo ss2).map fun i => st.2.2.1[i]!⟩ := by
  obtain ⟨_,ss0,ps0,cfg0,_⟩ := prepareAt_input_facts raw
  obtain ⟨_,labels⟩ := stock_prepare_domain run scope
  have graph := stock_lower_no_critical_edges run scope cfg0
  obtain ⟨ss1,ps1,ss2,ps2,st,cfg1,loop,empty,emptyRows,next,cfg2,resultEq⟩ :=
    prepareAt_no_new_edges raw labels cfg0 graph
  obtain ⟨count,_⟩ := prepareAt_input_facts raw
  have keptBlocks := keptAt_blocks (ss := ss0) count
  have keptSpec : Prep.CfgSpec ((keptAt result.code result.edgeArgs ss0).map Prod.fst) ss1 := by
    rw [keptBlocks]
    exact Prep.cfg_spec cfg1
  have inv := (outerLoopAt_inv keptSpec loop).graph
  rw [keptBlocks,empty,Array.map_empty] at inv
  have unchanged := unsplit_cfg_eq (Prep.keep_lbls labels _) inv (Prep.cfg_spec cfg1) (Prep.cfg_spec cfg2)
  exact ⟨ss0,ps0,cfg0,graph,ss1,ps1,ss2,ps2,st,cfg1,loop,empty,emptyRows,next,cfg2,unchanged.symm,resultEq⟩

end Backend.Stock.Proof
