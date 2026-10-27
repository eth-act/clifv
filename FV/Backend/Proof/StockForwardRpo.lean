import FV.Backend.Proof.PrepareComplete

namespace Backend.Stock.Proof.ForwardRpo
open Backend.Proof Backend.Proof.Prep
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Every successor of a finished DFS node was finished earlier. -/
private def PostBefore (succs : Array (Array Nat)) (post : List Nat) : Prop :=
  ∀ b ∈ post,∀ s ∈ succs[b]!.toList,
    ∃ earlier later,post = earlier ++ b :: later ∧ s ∈ earlier

private def SearchOrdered (rank : Nat → Nat) (succs : Array (Array Nat)) (st : Prep.DState) : Prop :=
  st.2.2.Pairwise (fun p q => rank q.1 < rank p.1) ∧ PostBefore succs st.2.1.toList

private theorem post_push {succs : Array (Array Nat)} {post : List Nat} {b : Nat}
    (ordered : PostBefore succs post) (closed : ∀ s ∈ succs[b]!.toList,s ∈ post) :
    PostBefore succs (post ++ [b]) := by
  intro x member s edge
  rcases List.mem_append.mp member with old | last
  · obtain ⟨earlier,later,parts,present⟩ := ordered x old s edge
    exact ⟨earlier,later ++ [b],by simp only [parts,List.append_assoc,List.cons_append],present⟩
  · have same : x = b := List.mem_singleton.mp last
    subst x
    exact ⟨post,[],rfl,closed s edge⟩

private theorem step_ordered {succs : Array (Array Nat)} {rank : Nat → Nat}
    (forward : ∀ b s,s ∈ succs[b]!.toList → rank b < rank s)
    {st : Prep.DState} (inv : DInv succs st) (ordered : SearchOrdered rank succs st)
    {p : Nat × Nat} {rest : List (Nat × Nat)} (stack : st.2.2 = p :: rest) :
    SearchOrdered rank succs (dStep succs st p rest) := by
  rcases st with ⟨seen,post,work⟩
  rcases p with ⟨b,i⟩
  simp only at stack
  subst work
  obtain ⟨descending,finished⟩ := ordered
  have restRanks := List.pairwise_cons.mp descending
  unfold SearchOrdered dStep
  dsimp only
  cases edge : succs[b]![i]? with
  | some s =>
    simp only [edge]
    have member : s ∈ succs[b]!.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge)
    have rises := forward b s member
    split
    · refine ⟨?_,finished⟩
      apply List.pairwise_cons.mpr
      refine ⟨?_,?_⟩
      · intro q present
        rcases List.mem_cons.mp present with rfl | present
        · exact rises
        · exact Nat.lt_trans (restRanks.1 q present) rises
      · simpa only [List.pairwise_cons] using restRanks
    · refine ⟨?_,finished⟩
      simpa only [List.pairwise_cons] using restRanks
  | none =>
    simp only [edge,Array.toList_push]
    refine ⟨restRanks.2,?_⟩
    change PostBefore succs (post.toList ++ [b])
    apply post_push finished
    intro s member
    obtain ⟨j,bounded,value⟩ := List.getElem_of_mem member
    have lookup : succs[b]![j]? = some s := by
      rw [← Array.getElem?_toList]
      exact List.getElem?_eq_some_iff.mpr ⟨bounded,value⟩
    have exhausted : succs[b]!.size ≤ i := Array.getElem?_eq_none_iff.mp edge
    have boundedIndex : j < succs[b]!.size := by simpa only [Array.length_toList] using bounded
    have visited := inv.frame (b,i) (by simp) j (by omega) s lookup
    rcases inv.cover s visited with present | active
    · exact present
    · simp only [List.map_cons,List.mem_cons,List.mem_map] at active
      have rises := forward b s member
      rcases active with rfl | ⟨q,present,same⟩
      · exact False.elim (Nat.lt_irrefl _ rises)
      · have smaller := restRanks.1 q present
        rw [same] at smaller
        change rank s < rank b at smaller
        exact False.elim (Nat.lt_asymm rises smaller)

private theorem iter_ordered {succs : Array (Array Nat)} {rank : Nat → Nat}
    (bounded : SuccsIn succs)
    (forward : ∀ b s,s ∈ succs[b]!.toList → rank b < rank s) :
    ∀ fuel st,DInv succs st → SearchOrdered rank succs st →
      SearchOrdered rank succs (iterW (fun st : Prep.DState => st.2.2) (dStep succs) fuel st)
  | 0,st,inv,ordered => ordered
  | fuel+1,st,inv,ordered => by
    simp only [iterW]
    split
    · exact ordered
    · rename_i p rest stack
      exact iter_ordered bounded forward fuel _ (dStep_inv bounded inv stack).1
        (step_ordered forward inv ordered stack)

/-- A strict source ranking makes the actual DFS reverse-postorder topological.
This is derived from the compiler's real fuel-bounded traversal, rather than an
order certificate supplied by an accepted program. Unreachable nodes are allowed. -/
theorem successor_after {succs : Array (Array Nat)} {rank : Nat → Nat}
    (bounded : SuccsIn succs) (nonempty : succs.size ≠ 0)
    (forward : ∀ b s,s ∈ succs[b]!.toList → rank b < rank s) :
    ∀ b ∈ (rpo succs).toList,∀ s ∈ succs[b]!.toList,
      ∃ earlier later,(rpo succs).toList = earlier ++ b :: later ∧ s ∈ later := by
  have positive : 0 < succs.size := Nat.pos_of_ne_zero nonempty
  have marked : mk ((Array.replicate succs.size false).set! 0 true) 0 :=
    mk_set.mpr (.inl ⟨rfl,by simp; omega⟩)
  have initial : DInv succs ((Array.replicate succs.size false).set! 0 true,#[],[(0,0)]) := by
    refine ⟨by simp,?_,by simp,?_,?_,by simp,by simp,by simp,by simp⟩
    · intro q present; simp only [List.mem_singleton] at present; subst q; exact marked
    · intro q present j less; simp only [List.mem_singleton] at present; subst q; simp at less
    · intro b present
      rcases mk_set.mp present with ⟨rfl,_⟩ | old
      · right; simp
      · exact False.elim (not_mk_replicate _ _ old)
  have ordered : SearchOrdered rank succs ((Array.replicate succs.size false).set! 0 true,#[],[(0,0)]) := by
    constructor <;> simp [PostBefore]
  have finished := (iter_ordered bounded forward (dFuel succs) _ initial ordered).2
  rw [rpo_eq succs nonempty]
  intro b present s edge
  simp only [Array.toList_reverse,List.mem_reverse] at present
  obtain ⟨earlier,later,parts,member⟩ := finished b present s edge
  refine ⟨later.reverse,earlier.reverse,?_,?_⟩
  · simp only [Array.toList_reverse,parts,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.append_assoc,List.singleton_append]
  · exact List.mem_reverse.mpr member

private def diamond : Array (Array Nat) := #[#[1,2],#[3],#[3],#[],#[5],#[]]

private theorem diamond_checks : ∀ b : Fin diamond.size,
    diamond[b.val]!.toList.all (fun s => decide (b.val < s ∧ s < diamond.size)) = true := by
  decide +kernel

private theorem diamond_edge {b s : Nat} (member : s ∈ diamond[b]!.toList) :
    b < s ∧ s < diamond.size := by
  by_cases bounded : b < diamond.size
  · exact of_decide_eq_true ((List.all_eq_true.mp (diamond_checks ⟨b,bounded⟩)) s member)
  · simp only [getElem!_def,Array.getElem?_eq_none (Nat.le_of_not_lt bounded),Option.getD_none] at member
    cases member

/-- The real DFS orders a diamond correctly even with a shared join and an
unreachable additional edge. The universal edge result is kernel-only. -/
theorem diamond_unreachable_witness :
    rpo diamond = #[0,2,1,3] ∧
    (∀ b ∈ (rpo diamond).toList,∀ s ∈ diamond[b]!.toList,
      ∃ earlier later,(rpo diamond).toList = earlier ++ b :: later ∧ s ∈ later) := by
  refine ⟨by decide +kernel,?_⟩
  exact successor_after (fun b s member => (diamond_edge member).2) (by decide +kernel)
    (rank := fun b => b) (fun b s member => (diamond_edge member).1)

end Backend.Stock.Proof.ForwardRpo
