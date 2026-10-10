import FV.Backend.Proof.DeadCleanupLive

namespace Backend.DeadCleanup

/-- An ordered deletion that keeps every instruction outside the whitelist. -/
inductive PureSublist : List MInst → List MInst → Prop
  | nil : PureSublist [] []
  | drop {xs ys : List MInst} {i : MInst} : pureForm i = true →
      PureSublist xs ys → PureSublist xs (i :: ys)
  | keep {xs ys : List MInst} {i : MInst} :
      PureSublist xs ys → PureSublist (i :: xs) (i :: ys)

theorem PureSublist.refl (xs : List MInst) : PureSublist xs xs := by
  induction xs with
  | nil => exact .nil
  | cons i xs ih => exact .keep ih

theorem PureSublist.sublist {xs ys : List MInst} (h : PureSublist xs ys) : xs.Sublist ys := by
  induction h with
  | nil => exact .slnil
  | drop _ _ ih => exact .cons _ ih
  | keep _ ih => exact .cons_cons _ ih

theorem PureSublist.findSome {α : Type} {xs ys : List MInst} (h : PureSublist xs ys)
    (f : MInst → Option α) (hf : ∀ i, pureForm i = true → f i = none) :
    xs.findSome? f = ys.findSome? f := by
  induction h with
  | nil => rfl
  | drop hp h ih => simp [List.findSome?_cons, hf _ hp, ih]
  | keep h ih => simp only [List.findSome?_cons, ih]

theorem scan_pureSublist (n : Nat) (ms : List MInst) (L : List Nat) :
    PureSublist (scan n ms L).1 ms := by
  induction ms with
  | nil => exact .nil
  | cons i ms ih =>
    simp only [scan]
    split
    · rename_i hd
      exact .drop (discard_pure hd) ih
    · exact .keep ih

theorem PureSublist.nonpure_mem {xs ys : List MInst} (h : PureSublist xs ys)
    {i : MInst} (hi : i ∈ ys) (hp : pureForm i = false) : i ∈ xs := by
  induction h with
  | nil => cases hi
  | @drop xs ys j hj h ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hp] at hj
      cases hj
    · exact ih hi
  | @keep xs ys j h ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih hi)

/-- A surviving instruction has an original position with the same instruction;
the prefix before it also keeps every non-pure instruction in order. -/
theorem PureSublist.prefix {xs ys : List MInst} (h : PureSublist xs ys)
    {k : Nat} {i : MInst} (hi : xs[k]? = some i) :
    ∃ pre post, ys = pre ++ i :: post ∧ PureSublist (xs.take k) pre := by
  induction h generalizing k with
  | nil => simp at hi
  | @drop xs ys j hj h ih =>
    obtain ⟨pre, post, he, hp⟩ := ih hi
    exact ⟨j :: pre, post, by simp [he], .drop hj hp⟩
  | @keep xs ys j h ih =>
    cases k with
    | zero =>
      cases hi
      exact ⟨[], ys, rfl, .nil⟩
    | succ k =>
      obtain ⟨pre, post, he, hp⟩ := ih hi
      exact ⟨j :: pre, post, by simp [he], .keep hp⟩

example : PureSublist [liveBic, liveReturn] [deadMvn, liveBic, liveReturn] :=
  .drop rfl (.keep (.keep .nil))

end Backend.DeadCleanup
