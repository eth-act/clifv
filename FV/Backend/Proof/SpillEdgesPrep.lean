import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.PrepareComplete

/-!
# The spill allocator's CFG facts across `prepare` (V4)

`LowOk vc`: the CFG facts of the VCode `lowerFunction` builds, with labels = block indices
(entry without parameters and predecessors, branch arguments only on a `jump` to a block with
matching parameters, parameterless successors otherwise, a `try_call`'s successors targeted by
it alone). `edgesOk_prepare`: `prepare`'s output then meets `EdgesOk`. `prepare` drops
unreachable blocks, splits critical edges by edge blocks `jump l` (no parameters, no branch
arguments, for blocks with at least two successors, which have no branch arguments) and reorders
the blocks; predecessor lists are recomputed by label.

Generic facts first: `VCode.cfg`'s predecessor lists (one entry per edge), the blocks `rpo`
lists are reachable.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-! ## `VCode.cfg`'s predecessors -/

theorem forIn_ok_foldl {ε α β : Type} (l : List α) (init : β) (g : β → α → β) :
    (forIn l init fun a b => (Except.ok (ForInStep.yield (g b a)) : Except ε (ForInStep β))) =
      Except.ok (l.foldl g init) :=
  Prep.forIn_yield_foldl l init g _ (fun _ _ => rfl)

theorem forIn_ok_foldlA {ε α β : Type} (l : Array α) (init : β) (g : β → α → β) :
    (forIn l init fun a b => (Except.ok (ForInStep.yield (g b a)) : Except ε (ForInStep β))) =
      Except.ok (l.toList.foldl g init) := by
  rw [← Array.forIn_toList]; exact forIn_ok_foldl _ _ _

/-- The predecessor entries of `s` the edges `L` (successor lists with their block) add. -/
def predsOf (s : Nat) (L : List (Array Nat × Nat)) : List Nat :=
  L.flatMap fun q => List.replicate (q.1.toList.count s) q.2

theorem inner_fold (s i : Nat) : ∀ (x : List Nat) (p : Array (Array Nat)),
    (x.foldl (fun q s' => q.modify s' fun a => a.push i) p)[s]?.map Array.toList =
      p[s]?.map fun a => a.toList ++ List.replicate (x.count s) i
  | [], p => by simp
  | a :: x, p => by
    rw [List.foldl_cons, inner_fold s i x, Array.getElem?_modify, List.count_cons]
    by_cases h : a = s
    · subst h
      cases p[a]? <;> simp [List.replicate_succ]
    · simp only [h, ite_false, beq_iff_eq, Nat.add_zero]

theorem outer_fold (s : Nat) : ∀ (L : List (Array Nat × Nat)) (p : Array (Array Nat)),
    (L.foldl (fun b a => a.1.toList.foldl (fun q s' => q.modify s' fun x => x.push a.2) b) p)[s]?.map
        Array.toList = p[s]?.map fun a => a.toList ++ predsOf s L
  | [], p => by simp [predsOf]
  | a :: L, p => by
    rw [List.foldl_cons, outer_fold s L,
      show (fun a : Array Nat => a.toList ++ predsOf s L) = (fun l => l ++ predsOf s L) ∘ Array.toList
        from rfl, ← Option.map_map, inner_fold]
    cases p[s]? <;> simp [predsOf]

/-- **`VCode.cfg`'s predecessors**: one entry per edge, in block order. -/
theorem cfg_preds {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {s : Nat}
    (hs : s < vc.blocks.size) : ps[s]? = some (predsOf s ss.toList.zipIdx).toArray := by
  unfold VCode.cfg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i succs hsuccs
  rw [← Array.forIn_toList] at h
  simp only [pure, Except.pure] at h
  simp only [forIn_ok_foldlA (ε := String) _ _ (fun (q : Array (Array Nat)) (s : Nat) => q.modify s _)] at h
  simp only [forIn_ok_foldl, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have := outer_fold s succs.zipIdx.toList (Array.replicate vc.blocks.size #[])
  rw [Array.getElem?_replicate, ite_eq_left_iff.mpr (fun h => absurd hs h), Array.toList_zipIdx] at this
  cases e : (List.foldl (fun b a => a.1.toList.foldl (fun q s' => q.modify s' fun x => x.push a.2) b)
      (Array.replicate vc.blocks.size #[]) succs.toList.zipIdx)[s]? with
  | none => rw [e] at this; cases this
  | some a =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq, List.nil_append] at this
    rw [Array.toList_zipIdx, e, ← this]

theorem predsOf_nil (s : Nat) : ∀ (L : List (Array Nat)) (k : Nat),
    (∀ (i : Nat) (x : Array Nat), L[i]? = some x → s ∉ x.toList) → predsOf s (L.zipIdx k) = []
  | [], _, _ => rfl
  | a :: L, k, h => by
    rw [List.zipIdx_cons]
    simp only [predsOf, List.flatMap_cons]
    rw [List.count_eq_zero.mpr (h 0 a rfl)]
    exact predsOf_nil s L (k + 1) fun i x hx => h (i + 1) x hx

theorem count_one {s : Nat} : ∀ {l : List Nat} {j0 : Nat}, l[j0]? = some s →
    (∀ j, l[j]? = some s → j = j0) → l.count s = 1
  | [], _, h, _ => by simp at h
  | a :: l, j0, h, hu => by
    rw [List.count_cons]
    by_cases ha : a = s
    · subst ha
      have h0 := hu 0 rfl
      subst h0
      have : l.count a = 0 := List.count_eq_zero.mpr fun hm => by
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
        have := hu (j + 1) (by simp [List.getElem?_eq_getElem hj, e])
        omega
      simp [this]
    · cases j0 with
      | zero => simp at h; exact absurd h ha
      | succ j0 =>
        have := count_one (l := l) (j0 := j0) (by simpa using h)
          (fun j hj => by have := hu (j + 1) (by simpa using hj); omega)
        simp [this, ha]

theorem predsOf_one (s p : Nat) : ∀ (L : List (Array Nat)) (k : Nat),
    (∀ (i : Nat) (x : Array Nat), L[i]? = some x → s ∈ x.toList → k + i = p) →
    (∀ x, L[p - k]? = some x → x.toList.count s = 1) → k ≤ p → p < k + L.length →
    predsOf s (L.zipIdx k) = [p]
  | [], _, _, _, h1, h2 => by simp at h2; omega
  | a :: L, k, hu, h1, hk, hp => by
    rw [List.zipIdx_cons]
    simp only [predsOf, List.flatMap_cons]
    by_cases e : k = p
    · subst e
      rw [h1 a (by simp)]
      have := predsOf_nil s L (k + 1) fun i x hx hm => by have := hu (i + 1) x hx hm; omega
      simp only [predsOf] at this
      rw [this]; rfl
    · rw [List.count_eq_zero.mpr fun hm => e (by simpa using hu 0 a rfl hm)]
      have := predsOf_one s p L (k + 1) (fun i x hx hm => by have := hu (i + 1) x hx hm; omega)
        (fun x hx => h1 x (by rw [show p - k = (p - (k + 1)) + 1 by omega]; simpa using hx))
        (by omega) (by simp at hp; omega)
      simp only [predsOf] at this
      simpa using this

/-- No edge into `s`: no predecessors. -/
theorem preds_nil {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {s : Nat}
    (hs : s < vc.blocks.size)
    (hno : ∀ (q : Nat) (sq : Array Nat) (j : Nat), ss[q]? = some sq → sq[j]? = some s → False) :
    ps[s]? = some #[] := by
  rw [cfg_preds h hs, predsOf_nil s ss.toList 0 fun i x hx hm => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
    exact hno i x j (by simpa using hx) (by simp [← e])]

/-- One edge into `s`, from `p`: one predecessor. -/
theorem preds_one {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {s : Nat}
    (hs : s < vc.blocks.size) {p j0 : Nat} {sp : Array Nat} (hp : ss[p]? = some sp)
    (hj0 : sp[j0]? = some s)
    (hu : ∀ (q : Nat) (sq : Array Nat) (j : Nat), ss[q]? = some sq → sq[j]? = some s → q = p ∧ j = j0) :
    ps[s]? = some #[p] := by
  have hpl : p < ss.size := (Array.getElem?_eq_some_iff.mp hp).1
  rw [cfg_preds h hs, predsOf_one s p ss.toList 0 (fun i x hx hm => by
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
      simpa using (hu i x j (by simpa using hx) (by simp [← e])).1)
    (fun x hx => by
      rw [Nat.sub_zero, Array.getElem?_toList, hp] at hx
      cases hx
      exact count_one (j0 := j0) (by simpa using hj0)
        (fun j hj => (hu p sp j hp (by simpa using hj)).2))
    (Nat.zero_le _) (by simpa using hpl)]

/-! ## `rpo` lists reachable blocks -/

/-- The stacked and finished blocks of `rpo`'s search are reachable. -/
def RR (succs : Array (Array Nat)) (st : Prep.DState) : Prop :=
  (∀ p ∈ st.2.2, Prep.Reach succs p.1) ∧ ∀ b ∈ st.2.1.toList, Prep.Reach succs b

theorem dStep_rr {succs : Array (Array Nat)} {st : Prep.DState} (h : RR succs st) {p : Nat × Nat}
    {rest : List (Nat × Nat)} (hw : st.2.2 = p :: rest) : RR succs (Prep.dStep succs st p rest) := by
  rcases st with ⟨seen, post, stack⟩
  simp only at hw
  subst hw
  obtain ⟨h1, h2⟩ := h
  have hb : Prep.Reach succs p.1 := h1 p (by simp)
  unfold Prep.dStep
  split
  · rename_i s hs
    have hr : Prep.Reach succs s :=
      .step hb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs))
    split
    · refine ⟨fun q hq => ?_, h2⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact hr
      · exact hb
      · exact h1 q (by simp [hq])
    · refine ⟨fun q hq => ?_, h2⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hb
      · exact h1 q (by simp [hq])
  · refine ⟨fun q hq => h1 q (by simp [hq]), fun b hb' => ?_⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb'
    rcases hb' with hb' | rfl
    · exact h2 b hb'
    · exact hb

theorem iter_rr {succs : Array (Array Nat)} :
    ∀ m (st : Prep.DState), RR succs st → RR succs (Prep.iterW (fun st : Prep.DState => st.2.2) (Prep.dStep succs) m st)
  | 0, st, h => h
  | m + 1, st, h => by
    simp only [Prep.iterW]
    split
    · exact h
    · rename_i p rest hw
      exact iter_rr m _ (dStep_rr h hw)

/-- Every block `rpo` lists is reachable. -/
theorem rpo_reach {succs : Array (Array Nat)} {b : Nat} (hb : b ∈ (rpo succs).toList) :
    Prep.Reach succs b := by
  by_cases h0 : succs.size = 0
  · have e : rpo succs = #[] := by unfold rpo; simp [h0]
    rw [e] at hb; simp at hb
  rw [Prep.rpo_eq succs h0] at hb
  have := iter_rr (succs := succs) (Prep.dFuel succs)
    ((Array.replicate succs.size false).set! 0 true, #[], [(0, 0)])
    ⟨fun p hp => by simp at hp; subst hp; exact .entry, fun b hb => by simp at hb⟩
  exact this.2 b (by simpa using hb)

end Backend.Proof.Spill
