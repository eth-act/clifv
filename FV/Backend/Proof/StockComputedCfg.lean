module

public import FV.Backend.Proof.StockCfgTotal

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

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

/-- The computed machine CFG has exactly the actual Stock order's successor
rows, under the original scope. No supplied graph certificate is required. -/
theorem stock_lower_computed_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    ∃ ps,result.code.cfg = .ok (result.order.successors,ps) := by
  exact cfg_of_spec (stock_lower_cfg run scope)

end Backend.Stock.Proof
