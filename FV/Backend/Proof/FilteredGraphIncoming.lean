import FV.Backend.Proof.IndexedPredMultiplicity

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- No edge out of a multi-successor block enters a multiply reached target.
This is an internal graph property, derived for Stock rather than a source filter. -/
def NoCriticalEdges (ss ps : Array (Array Nat)) : Prop :=
  ∀ (b : Nat) (row : Array Nat),ss[b]? = some row → 2 ≤ row.size →
    ∀ (j target : Nat),row[j]? = some target → (ps[target]!).size ≤ 1

/-- Original index selected by the executable label lookup after filtering. -/
def keepOrigin (V : Array VBlock) (live : Array Bool) (q : Nat) : Nat :=
  (Prep.lab V (Prep.keep V live)[q]!.label).getD 0

/-- Every actual kept block has its real original index and exact block body. -/
theorem keepOrigin_spec {V : Array VBlock} {live : Array Bool} (labels : Prep.Lbls V)
    {q : Nat} (bound : q < (Prep.keep V live).size) :
    ∃ originalBound : keepOrigin V live q < V.size, (Prep.keep V live)[q] = V[keepOrigin V live q]
       := by
  obtain ⟨b,hb,same,_⟩ := Prep.keep_src bound
  have origin : keepOrigin V live q = b := by
    unfold keepOrigin
    rw [getElem!_pos (Prep.keep V live) q bound,same,Prep.lab_of labels hb rfl]
    rfl
  simp only [origin]
  exact ⟨hb,same⟩

/-- Filtering's label-selected original-index mapping is injective. It cannot
merge two kept predecessor occurrences into one original source block. -/
theorem keepOrigin_injective {V : Array VBlock} {live : Array Bool} (labels : Prep.Lbls V)
    {q r : Nat} (qBound : q < (Prep.keep V live).size) (rBound : r < (Prep.keep V live).size)
    (same : keepOrigin V live q = keepOrigin V live r) : q = r := by
  obtain ⟨_,qSource⟩ := keepOrigin_spec labels qBound
  obtain ⟨_,rSource⟩ := keepOrigin_spec labels rBound
  apply Prep.lbl_inj (Prep.keep_lbls labels live) qBound rBound
  rw [qSource,rSource]
  simp only [same]

/-- Every actual kept CFG edge reflects to the same successor index in its
real original source row. Targets reflect through the same injective mapping,
and source successor counts are preserved, including duplicate destinations. -/
theorem keep_cfg_edge {vc : VCode} {live : Array Bool} {ss0 ps0 ss1 ps1 : Array (Array Nat)}
    (cfg0 : vc.cfg = .ok (ss0,ps0))
    (cfg1 : ({vc with blocks := Prep.keep vc.blocks live} : VCode).cfg = .ok (ss1,ps1))
    (labels : Prep.Lbls vc.blocks) {q j target : Nat} {row : Array Nat}
    (atRow : ss1[q]? = some row) (edge : row[j]? = some target) :
    ∃ oldRow,ss0[keepOrigin vc.blocks live q]? = some oldRow ∧
      oldRow[j]? = some (keepOrigin vc.blocks live target) ∧ oldRow.size = row.size := by
  have cs0 := Prep.cfg_spec cfg0
  have cs1 := Prep.cfg_spec cfg1
  have qBound : q < (Prep.keep vc.blocks live).size := by rw [← cs1.size]; exact (Array.getElem?_eq_some_iff.mp atRow).1
  have targetBound := cfg_succ_lt cfg1 atRow (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  obtain ⟨oldBound,source⟩ := keepOrigin_spec labels qBound
  obtain ⟨oldTargetBound,targetSource⟩ := keepOrigin_spec labels targetBound
  have atSource : (Prep.keep vc.blocks live)[q]? = some vc.blocks[keepOrigin vc.blocks live q] := by
    rw [Array.getElem?_eq_getElem qBound,source]
  obtain ⟨t,oldRow,back,_,oldAt,oldCount,oldTargets⟩ := cs0.blk _ _ (Array.getElem?_eq_getElem oldBound)
  obtain ⟨t',newRow,back',_,newAt,newCount,newTargets⟩ := cs1.blk q _ atSource
  rw [back] at back'
  cases back'
  rw [atRow] at newAt
  cases newAt
  have jBound := (Array.getElem?_eq_some_iff.mp edge).1
  obtain ⟨label,selected⟩ : ∃ label,t.targets[j]? = some label :=
    ⟨_,List.getElem?_eq_getElem (by rw [← newCount]; exact jBound)⟩
  obtain ⟨newTarget,newEdge,newLab⟩ := newTargets j label selected
  rw [edge] at newEdge
  cases newEdge
  obtain ⟨_,labelAtTarget⟩ := Prep.lab_some newLab
  have oldLab : Prep.lab vc.blocks label = some (keepOrigin vc.blocks live target) := by
    apply Prep.lab_of labels oldTargetBound
    rw [← targetSource]
    exact labelAtTarget
  obtain ⟨oldTarget,oldEdge,oldFind⟩ := oldTargets j label selected
  rw [oldLab] at oldFind
  cases oldFind
  exact ⟨oldRow,oldAt,oldEdge,oldCount.trans newCount.symm⟩

/-- Reachability filtering preserves the no-critical-edge graph property.
Every pair of kept incoming occurrences reflects to distinct original
occurrences; neither predecessor counts nor selected indices are collapsed. -/
theorem keep_no_critical {vc : VCode} {live : Array Bool} {ss0 ps0 ss1 ps1 : Array (Array Nat)}
    (cfg0 : vc.cfg = .ok (ss0,ps0))
    (cfg1 : ({vc with blocks := Prep.keep vc.blocks live} : VCode).cfg = .ok (ss1,ps1))
    (labels : Prep.Lbls vc.blocks) (original : NoCriticalEdges ss0 ps0) : NoCriticalEdges ss1 ps1 := by
  intro q row atRow multiple j target edge
  apply Classical.byContradiction
  intro notSmall
  have shared : 1 < (ps1[target]!).size := by omega
  obtain ⟨other,index,otherRow,otherAt,otherEdge,distinct⟩ := cfg_multiple_preds_other cfg1 atRow edge shared
  obtain ⟨oldRow,oldAt,oldEdge,count⟩ := keep_cfg_edge cfg0 cfg1 labels atRow edge
  obtain ⟨oldOther,oldOtherAt,oldOtherEdge,_⟩ := keep_cfg_edge cfg0 cfg1 labels otherAt otherEdge
  have small := original _ oldRow oldAt (by rw [count]; exact multiple) j _ oldEdge
  obtain ⟨sameOrigin,sameIndex⟩ := cfg_pred_size_le_one_unique cfg0 oldAt oldEdge small oldOtherAt oldOtherEdge
  have qBound : q < (Prep.keep vc.blocks live).size := by
    rw [← (Prep.cfg_spec cfg1).size]; exact (Array.getElem?_eq_some_iff.mp atRow).1
  have otherBound : other < (Prep.keep vc.blocks live).size := by
    rw [← (Prep.cfg_spec cfg1).size]; exact (Array.getElem?_eq_some_iff.mp otherAt).1
  have sameBlock := keepOrigin_injective labels otherBound qBound sameOrigin
  rcases distinct with different | different
  · exact different sameBlock
  · exact different sameIndex

end Backend.Proof.PerEdgePrep
