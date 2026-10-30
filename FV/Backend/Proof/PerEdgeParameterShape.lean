import FV.Backend.Proof.StockCfgTotal
import FV.Backend.Proof.StockParameterShape
import FV.Backend.Proof.PerEdgePrepareOrderFacts

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual indexed preparation preserves parameter class and distinctness
through filtering, terminator retargeting, synthetic edge insertion and RPO.
Only original block metadata is needed; no prepared-code certificate. -/
theorem prepareAt_parameter_shape {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p)
    (original : ∀ (b : Nat) (vb : VBlock),vc.blocks[b]? = some vb → ParameterShape vb.params) :
    ∀ (b : Nat) (vb : VBlock),p.code.blocks[b]? = some vb → ParameterShape vb.params := by
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,inv,cfg2,result⟩ := prepareAt_outer_facts run
  have kept : ∀ (j : Nat) (hj : j < ((keptAt vc edges ss0).map Prod.fst).size),
      ParameterShape (((keptAt vc edges ss0).map Prod.fst)[j]).params := by
    intro j hj
    have bound : j < (keptAt vc edges ss0).size := by simpa only [Array.size_map] using hj
    obtain ⟨b,source,_,_⟩ := keptAt_source (vc := vc) (edges := edges) (ss := ss0) bound
    simpa only [Array.getElem_map] using original b _ source
  have all : ∀ (i : Nat),ParameterShape ((st.2.1 ++ st.2.2.2.1)[i]!).params := by
    intro i
    by_cases inBody : i < st.2.1.size
    · have inKept : i < ((keptAt vc edges ss0).map Prod.fst).size := by rw [← inv.graph.size]; exact inBody
      have same := (Prep.rw_fields (inv.graph.rw i inKept inBody)).2.1
      have blockAt : (st.2.1 ++ st.2.2.2.1)[i]? = some st.2.1[i] := by
        rw [Array.getElem?_append,if_pos inBody,Array.getElem?_eq_getElem inBody]
      rw [getElem!_def,blockAt]
      change ParameterShape (st.2.1[i]).params
      rw [same]
      exact kept i inKept
    · by_cases inEdge : i - st.2.1.size < st.2.2.2.1.size
      · have shadowBound : i-st.2.1.size < (st.2.2.2.1.map graphBlock).size := by simpa only [Array.size_map] using inEdge
        obtain ⟨l,shadow⟩ := inv.graph.edges (i-st.2.1.size) shadowBound
        have params : (st.2.2.2.1[i-st.2.1.size]).params = #[] := by
          have same := congrArg VBlock.params shadow
          simpa only [Array.getElem_map,graphBlock] using same
        have blockAt : (st.2.1 ++ st.2.2.2.1)[i]? = some st.2.2.2.1[i-st.2.1.size] := by
          rw [Array.getElem?_append,if_neg inBody,Array.getElem?_eq_getElem inEdge]
        rw [getElem!_def,blockAt]
        change ParameterShape (st.2.2.2.1[i-st.2.1.size]).params
        rw [params]
        exact ⟨by simp,by simp⟩
      · have outside : (st.2.1 ++ st.2.2.2.1).size ≤ i := by simp only [Array.size_append]; omega
        rw [getElem!_def,Array.getElem?_eq_none outside]
        change ParameterShape (#[] : Array Reg)
        exact ⟨by simp,by simp⟩
  intro b vb block
  rw [result] at block
  dsimp only at block
  rw [Array.getElem?_map] at block
  cases selected : (rpo ss2)[b]? with
  | none => rw [selected] at block; cases block
  | some i =>
    rw [selected] at block
    simp only [Option.map_some,Option.some.injEq] at block
    subst vb
    exact all i

end Backend.Proof.PerEdgePrep

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

/-- Actual original-scope/SSA Stock lowering produces checked prepared code
with the allocator's parameter shape on every real block. All preparation and
parameter metadata are derived internally, preserving the original inputs. -/
theorem stock_prepare_parameter_shape {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) :
    ∃ prepared,prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true ∧
      ∀ (b : Nat) (vb : VBlock),prepared.code.blocks[b]? = some vb → ParameterShape vb.params := by
  obtain ⟨prepared,raw,checked,accepted⟩ := stock_prepare_total run scope
  exact ⟨prepared,raw,checked,accepted,
    PerEdgePrep.prepareAt_parameter_shape raw (stock_lower_parameter_shape run scope ssa)⟩

end Backend.Stock.Proof
