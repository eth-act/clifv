import FV.Backend.Proof.PrepareComplete
import FV.Backend.Proof.PerEdgePrepareOrderFacts

namespace Backend.Proof.Prep
open Backend
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private def SearchReach (ss : Array (Array Nat)) (st : DState) : Prop :=
  (∀ p ∈ st.2.2,Reach ss p.1) ∧ ∀ b ∈ st.2.1.toList,Reach ss b
private theorem step_reach {ss : Array (Array Nat)} {st : DState} {p : Nat × Nat} {rest : List (Nat × Nat)}
    (before : SearchReach ss st) (stack : st.2.2 = p :: rest) : SearchReach ss (dStep ss st p rest) := by
  have current := before.1 p (by rw [stack]; simp)
  have tails : ∀ q ∈ rest,Reach ss q.1 := fun q member => before.1 q (by rw [stack]; simp [member])
  unfold dStep
  cases selected : ss[p.1]![p.2]? with
  | none =>
    dsimp only
    refine ⟨tails,?_⟩
    intro b member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with old | same
    · exact before.2 b old
    · subst b; exact current
  | some target =>
    dsimp only
    have reached : Reach ss target := .step current (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selected))
    split
    · refine ⟨?_,before.2⟩
      intro q member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | old
      · exact reached
      · exact current
      · exact tails q old
    · refine ⟨?_,before.2⟩
      intro q member
      rcases List.mem_cons.mp member with rfl | old
      · exact current
      · exact tails q old
private theorem iter_reach (ss : Array (Array Nat)) (fuel : Nat) (st : DState)
    (before : SearchReach ss st) : SearchReach ss (iterW (fun st : DState => st.2.2) (dStep ss) fuel st) := by
  induction fuel generalizing st with
  | zero => exact before
  | succ fuel ih =>
    unfold iterW
    cases stack : st.2.2 with
    | nil => exact before
    | cons p rest => exact ih _ (step_reach before stack)

/-- Every block actually selected by the executable RPO search is reachable
from entry. This is the converse direction to RPO's existing coverage theorem,
proved for the actual finite-fuel search without a graph-validity assumption. -/
theorem rpo_selected_reachable (ss : Array (Array Nat)) (b : Nat) (member : b ∈ (rpo ss).toList) : Reach ss b := by
  by_cases empty : ss.size = 0
  · unfold rpo at member
    simp [empty] at member
  · rw [rpo_eq ss empty,Array.toList_reverse,List.mem_reverse] at member
    have initial : SearchReach ss ((Array.replicate ss.size false).set! 0 true,#[],[(0,0)]) := by
      constructor
      · intro p member
        simp only [List.mem_singleton] at member
        subst p
        exact .entry
      · intro b member; cases member
    exact (iter_reach ss (dFuel ss) _ initial).2 b member

private theorem reorder_reaches {V : Array VBlock} {R : Array Nat} {ss ss' : Array (Array Nat)}
    (cfg : CfgSpec V ss) (cfg' : CfgSpec (R.map fun i => V[i]!) ss')
    (bounds : ∀ i ∈ R.toList,i < V.size) (labels : Lbls V) (distinct : R.toList.Nodup)
    (entry : R[0]? = some 0) (complete : ∀ b,Reach ss b → b ∈ R.toList)
    {b : Nat} (reached : Reach ss b) {q : Nat} (selected : R[q]? = some b) : Reach ss' q := by
  have labels' := lbls3 bounds labels distinct
  induction reached generalizing q with
  | entry =>
    obtain ⟨qBound,qValue⟩ := Array.getElem?_eq_some_iff.mp selected
    obtain ⟨zeroBound,zeroValue⟩ := Array.getElem?_eq_some_iff.mp entry
    have same : q = 0 := distinct.eq_of_getElem_eq (by simpa using qBound) (by simpa using zeroBound)
      (by simpa only [Array.getElem_toList,qValue,zeroValue])
    subst q
    exact .entry
  | @step b target reached edge ih =>
    obtain ⟨sourceIndex,sourceBound,sourceValue⟩ := List.getElem_of_mem (complete b reached)
    have sourceIndexBound : sourceIndex < R.size := by simpa using sourceBound
    have atSource : R[sourceIndex]? = some b := by
      rw [Array.getElem?_eq_getElem sourceIndexBound]
      exact congrArg some (by simpa only [Array.getElem_toList] using sourceValue)
    have before := ih atSource
    obtain ⟨bBound,T,j,label,last,atLabel,targetLabel⟩ := succ_of cfg edge
    obtain ⟨targetBound,targetValue⟩ := lab_some targetLabel
    have atSourceBlock : (R.map fun i => V[i]!)[sourceIndex]? = some V[b] := by
      simp only [Array.getElem?_map,atSource,Option.map_some,getElem!_pos V b bBound]
    have sourceInNew : sourceIndex < (R.map fun i => V[i]!).size := by simpa only [Array.size_map] using sourceIndexBound
    have sourceEq := (Array.getElem?_eq_some_iff.mp atSourceBlock).2
    have targetIndexBound := (Array.getElem?_eq_some_iff.mp selected).1
    have targetInNew : q < (R.map fun i => V[i]!).size := by simpa only [Array.size_map] using targetIndexBound
    have atTargetBlock : (R.map fun i => V[i]!)[q]? = some V[target] := by
      simp only [Array.getElem?_map,selected,Option.map_some,getElem!_pos V target targetBound]
    have targetEq := (Array.getElem?_eq_some_iff.mp atTargetBlock).2
    have labNew : lab (R.map fun i => V[i]!) label = some q := lab_of labels' targetInNew (by rw [targetEq]; exact targetValue)
    exact .step before (succ_mem cfg' sourceInNew (by rw [sourceEq]; exact last) atLabel labNew)

private theorem reordered_all_reachable {V : Array VBlock} {ss ss' : Array (Array Nat)}
    (cfg : CfgSpec V ss) (labels : Lbls V) (nonzero : ss.size ≠ 0)
    (cfg' : CfgSpec ((rpo ss).map fun i => V[i]!) ss') :
    ∀ (q : Nat),q < (rpo ss).size → Reach ss' q := by
  obtain ⟨bounds,distinct,entry,closed,complete⟩ := rpo_spec (succsIn_of cfg) nonzero
  intro q qBound
  have member : (rpo ss)[q] ∈ (rpo ss).toList := Array.getElem_mem_toList qBound
  exact reorder_reaches cfg cfg' (fun i hi => cfg.size ▸ bounds i hi) labels distinct entry complete
    (rpo_selected_reachable ss _ member) (Array.getElem?_eq_getElem qBound)

end Backend.Proof.Prep

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof

/-- Every actual output block of successful indexed preparation is reachable
in its actual CFG. The proof follows the executable RPO and transports its
real input paths through reorder; unreachable extra blocks are not assumed away. -/
theorem prepareAt_all_reachable {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {ss3 ps3 : Array (Array Nat)} (cfg3 : p.code.cfg = .ok (ss3,ps3)) :
    ∀ (b : Nat),b < p.code.blocks.size → Prep.Reach ss3 b := by
  obtain ⟨count,ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,_,cfg1,inv,cfg2,result⟩ := prepareAt_kept_facts run
  have cs0 := Prep.cfg_spec cfg0
  have nonzero0 : ss0.size ≠ 0 := by rw [cs0.size]; omega
  have entry := (Prep.reachable_spec (Prep.succsIn_of cs0) nonzero0).2.1
  obtain ⟨keptNonempty,_⟩ := Prep.keep_zero nonempty entry
  have keptLabels := Prep.keep_lbls labels (reachable ss0)
  have cs1 := Prep.cfg_spec cfg1
  have cs2 := Prep.cfg_spec cfg2
  obtain ⟨labels2,_⟩ := outer_order_facts inv cs1 cs2 keptLabels keptNonempty
  have nonzero2 : ss2.size ≠ 0 := by
    have keptSize := inv.graph.size
    rw [cs2.size,Array.size_append,keptSize]
    omega
  cases result
  have all := Prep.reordered_all_reachable cs2 labels2 nonzero2 (Prep.cfg_spec cfg3)
  intro b bound
  exact all b (by simpa only [Array.size_map] using bound)

end Backend.Proof.PerEdgePrep
