import FV.Backend.Proof.SpillInvariant

/-!
# The spill allocator's homes and argument-area facts (V4 (a), step 4)

`spillHomes` assigns distinct homes below its size to every vreg of every block, and
`spillAlloc`'s `maxArgs` bounds every block's branch-argument count.
-/

namespace Backend.Proof.Spill

open Backend

/-- One step of `spillHomes`'s inner fold. -/
private def homeStep (h : Homes) (k : Nat × RegClass) : Homes :=
  if h.contains k then h else h.insert k h.size

/-- One block step of `spillHomes`'s outer fold. -/
private def blockStep (h : Homes) (b : VBlock) : Homes :=
  (blockVregs b).foldl homeStep h

private theorem spillHomes_eq (vc : VCode) :
    spillHomes vc = vc.blocks.toList.foldl blockStep {} := by
  rw [Array.foldl_toList]; rfl

/-- The homes are below the size and pairwise distinct. -/
private def HInv (h : Homes) : Prop :=
  (∀ (k : Nat × RegClass) (n : Nat), h[k]? = some n → n < h.size) ∧
  (∀ (k k' : Nat × RegClass) (n : Nat), h[k]? = some n → h[k']? = some n → k = k')

private theorem homeStep_inv {h : Homes} (hi : HInv h) (k : Nat × RegClass) :
    HInv (homeStep h k) := by
  unfold homeStep
  split
  · exact hi
  · rename_i hc
    have hs : (h.insert k h.size).size = h.size + 1 := by
      simp [Std.HashMap.size_insert, Std.HashMap.mem_iff_contains, hc]
    refine ⟨fun j n hj => ?_, fun j j' n hj hj' => ?_⟩
    · rw [hs]
      rw [Std.HashMap.getElem?_insert] at hj
      split at hj
      · cases hj; omega
      · have := hi.1 _ _ hj; omega
    · rw [Std.HashMap.getElem?_insert] at hj hj'
      split at hj <;> split at hj'
      · rename_i e e'
        have := eq_of_beq e; have := eq_of_beq e'; subst_vars; rfl
      · cases hj; have := hi.1 _ _ hj'; omega
      · cases hj'; have := hi.1 _ _ hj; omega
      · exact hi.2 _ _ _ hj hj'

private theorem homeFold_inv (l : List (Nat × RegClass)) {h : Homes} (hi : HInv h) :
    HInv (l.foldl homeStep h) := by
  induction l generalizing h with
  | nil => exact hi
  | cons a l ih => exact ih (homeStep_inv hi a)

private theorem blockFold_inv (l : List VBlock) {h : Homes} (hi : HInv h) :
    HInv (l.foldl blockStep h) := by
  induction l generalizing h with
  | nil => exact hi
  | cons a l ih => exact ih (homeFold_inv _ hi)

private theorem empty_inv : HInv ({} : Homes) :=
  ⟨fun k n hk => by simp at hk, fun k k' n hk _ => by simp at hk⟩

private theorem spillHomes_inv (vc : VCode) : HInv (spillHomes vc) := by
  rw [spillHomes_eq]; exact blockFold_inv _ empty_inv

theorem spillHomes_lt (vc : VCode) {k : Nat × RegClass} {n : Nat}
    (h : (spillHomes vc)[k]? = some n) : n < (spillHomes vc).size :=
  (spillHomes_inv vc).1 _ _ h

theorem spillHomes_inj (vc : VCode) {k k' : Nat × RegClass} {n : Nat}
    (h : (spillHomes vc)[k]? = some n) (h' : (spillHomes vc)[k']? = some n) : k = k' :=
  (spillHomes_inv vc).2 _ _ _ h h'

/-! ## Membership -/

private theorem homeStep_mem {h : Homes} {j : Nat × RegClass} (hj : j ∈ h)
    (k : Nat × RegClass) : j ∈ homeStep h k := by
  unfold homeStep
  split
  · exact hj
  · exact Std.HashMap.mem_insert.2 (Or.inr hj)

private theorem homeStep_self (h : Homes) (k : Nat × RegClass) : k ∈ homeStep h k := by
  unfold homeStep
  split
  · rename_i hc; exact Std.HashMap.mem_iff_contains.2 hc
  · exact Std.HashMap.mem_insert.2 (Or.inl (BEq.refl k))

private theorem homeFold_mem (l : List (Nat × RegClass)) {h : Homes} {j : Nat × RegClass}
    (hj : j ∈ h) : j ∈ l.foldl homeStep h := by
  induction l generalizing h with
  | nil => exact hj
  | cons a l ih => exact ih (homeStep_mem hj a)

private theorem homeFold_mem_of (l : List (Nat × RegClass)) (h : Homes) {j : Nat × RegClass}
    (hj : j ∈ l) : j ∈ l.foldl homeStep h := by
  induction l generalizing h with
  | nil => cases hj
  | cons a l ih =>
    rcases List.mem_cons.1 hj with rfl | hj
    · exact homeFold_mem l (homeStep_self h j)
    · exact ih _ hj

private theorem blockFold_mem (l : List VBlock) {h : Homes} {j : Nat × RegClass}
    (hj : j ∈ h) : j ∈ l.foldl blockStep h := by
  induction l generalizing h with
  | nil => exact hj
  | cons a l ih => exact ih (homeFold_mem _ hj)

private theorem blockFold_mem_of (l : List VBlock) (h : Homes) {vb : VBlock} (hvb : vb ∈ l)
    {k : Nat × RegClass} (hk : k ∈ blockVregs vb) : k ∈ l.foldl blockStep h := by
  induction l generalizing h with
  | nil => cases hvb
  | cons a l ih =>
    rcases List.mem_cons.1 hvb with rfl | hvb
    · exact blockFold_mem l (homeFold_mem_of _ h hk)
    · exact ih _ hvb

private theorem mem_toList_of_getElem? {α} {xs : Array α} {b : Nat} {a : α}
    (h : xs[b]? = some a) : a ∈ xs.toList :=
  Array.mem_toList_iff.2 (Array.mem_of_getElem? h)

theorem spillHomes_mem (vc : VCode) {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb)
    {k : Nat × RegClass} (hk : k ∈ blockVregs vb) : ∃ n, (spillHomes vc)[k]? = some n := by
  have hm : k ∈ spillHomes vc := by
    rw [spillHomes_eq]; exact blockFold_mem_of _ _ (mem_toList_of_getElem? hb) hk
  exact ⟨_, Std.HashMap.getElem?_eq_some_getElem hm⟩

/-! ## The argument area -/

private theorem maxFold_ge_init (l : List VBlock) (m : Nat) :
    m ≤ l.foldl (fun m b => max m b.branchArgs.size) m := by
  induction l generalizing m with
  | nil => exact Nat.le_refl _
  | cons a l ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem maxFold_ge (l : List VBlock) (m : Nat) {vb : VBlock} (hvb : vb ∈ l) :
    vb.branchArgs.size ≤ l.foldl (fun m b => max m b.branchArgs.size) m := by
  induction l generalizing m with
  | nil => cases hvb
  | cons a l ih =>
    rcases List.mem_cons.1 hvb with rfl | hvb
    · exact Nat.le_trans (Nat.le_max_right _ _) (maxFold_ge_init _ _)
    · exact ih _ hvb

theorem maxArgs_ge (vc : VCode) {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb) :
    vb.branchArgs.size ≤ vc.blocks.foldl (fun m b => max m b.branchArgs.size) 0 := by
  rw [← Array.foldl_toList]; exact maxFold_ge _ _ (mem_toList_of_getElem? hb)

end Backend.Proof.Spill
