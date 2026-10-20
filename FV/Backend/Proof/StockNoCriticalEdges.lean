import FV.Backend.Proof.FilteredGraphIncoming
import FV.Backend.Proof.StockSharedJumpCfg
import FV.Backend.Proof.StockCfgTotal

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
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

/-- Actual Stock output has already split every critical edge, including
forced single-successor TryCall/brTable cases. This property follows from
original scope and actual shared-predecessor jump correctness; it is not an
additional source acceptance test. -/
theorem stock_lower_no_critical_edges {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {ss ps : Array (Array Nat)} (cfg : result.code.cfg = .ok (ss,ps)) : NoCriticalEdges ss ps := by
  have actual := cfgSpec_unique (Prep.cfg_spec cfg) (stock_lower_cfg run scope)
  intro b row atRow multiple j target edge
  apply Classical.byContradiction
  intro notSmall
  have shared : 1 < (ps[target]!).size := by omega
  obtain ⟨other,index,otherRow,otherAt,otherEdge,distinct⟩ := cfg_multiple_preds_other cfg atRow edge shared
  rw [actual] at atRow otherAt
  obtain ⟨block,placed,back,single,zero⟩ := stock_lower_shared_jump_cfg run scope atRow edge otherAt otherEdge
    (by rcases distinct with different | different; exact .inl (Ne.symm different); exact .inr (Ne.symm different))
  have same := Option.some.inj (atRow.symm.trans single)
  have length := congrArg Array.size same
  simp only [Array.size_singleton] at length
  omega

/-- The actual reachability-filtered Stock graph remains critical-edge free.
The original domain derives distinct labels; filtering and real predecessor
multiplicity reflection supply the rest. -/
theorem stock_kept_no_critical_edges {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {ss0 ps0 ss1 ps1 : Array (Array Nat)} (cfg0 : result.code.cfg = .ok (ss0,ps0))
    (cfg1 : ({result.code with blocks := Prep.keep result.code.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1)) :
    NoCriticalEdges ss1 ps1 := by
  obtain ⟨_,labels⟩ := stock_prepare_domain run scope
  exact keep_no_critical cfg0 cfg1 labels (stock_lower_no_critical_edges run scope cfg0)

end Backend.Stock.Proof
