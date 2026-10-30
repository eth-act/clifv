import FV.Backend.Proof.SpillStep4Cfg

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Reordering by distinct indices does not identify distinct source blocks. -/
theorem reorder_index_injective {R : Array Nat} (distinct : R.toList.Nodup)
    {q r : Nat} (qBound : q < R.size) (rBound : r < R.size)
    (same : R[q]! = R[r]!) : q = r := by
  rw [getElem!_pos R q qBound,getElem!_pos R r rBound] at same
  exact distinct.eq_of_getElem_eq (by simpa using qBound) (by simpa using rBound) same

/-- Each actual reordered CFG edge reflects to its original selected edge
index and exact original source/target block indices. Duplicate destinations
are retained. This applies to the executable reorder, not a graph surrogate. -/
theorem reorder_cfg_edge {vc : VCode} {R : Array Nat} {ss0 ps0 ss1 ps1 : Array (Array Nat)}
    (bounds : ∀ i ∈ R.toList,i < vc.blocks.size) (labels : Prep.Lbls vc.blocks) (cfg0 : vc.cfg = .ok (ss0,ps0))
    (cfg1 : ({vc with blocks := R.map fun i => vc.blocks[i]!} : VCode).cfg = .ok (ss1,ps1))
    {q j target : Nat} {row : Array Nat} (atRow : ss1[q]? = some row) (edge : row[j]? = some target) :
    ∃ oldRow,ss0[R[q]!]? = some oldRow ∧ oldRow[j]? = some R[target]! ∧ oldRow.size = row.size := by
  have cs0 := Prep.cfg_spec cfg0
  have cs1 := Prep.cfg_spec cfg1
  have qBound : q < R.size := by
    have h := (Array.getElem?_eq_some_iff.mp atRow).1
    rw [cs1.size,Array.size_map] at h
    exact h
  have targetBound : target < R.size := by
    have h := cfg_succ_lt cfg1 atRow (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
    simpa using h
  obtain ⟨oldBound,source⟩ := Prep.v3_get bounds qBound
  obtain ⟨targetOldBound,targetSource⟩ := Prep.v3_get bounds targetBound
  obtain ⟨t,oldRow,back,_,oldAt,oldCount,oldTargets⟩ := cs0.blk _ _ (Array.getElem?_eq_getElem oldBound)
  obtain ⟨t',newRow,back',_,newAt,newCount,newTargets⟩ := cs1.blk q _ source
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
  obtain ⟨_,newLabel⟩ := Prep.lab_some newLab
  have oldLabel : vc.blocks[R[target]].label = label := by
    have h := Option.some.inj ((Array.getElem?_eq_getElem (by simpa using targetBound)).symm.trans targetSource)
    rw [← h]
    exact newLabel
  obtain ⟨oldTarget,oldEdge,oldFind⟩ := oldTargets j label selected
  have targetFind : Prep.lab vc.blocks label = some R[target] :=
    Prep.lab_of labels targetOldBound oldLabel
  rw [targetFind] at oldFind
  cases oldFind
  refine ⟨oldRow,?_,?_,oldCount.trans newCount.symm⟩
  · simpa only [getElem!_pos R q qBound] using oldAt
  · simpa only [getElem!_pos R target targetBound] using oldEdge

end Backend.Proof.PerEdgePrep
