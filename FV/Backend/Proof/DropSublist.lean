import FV.Backend.Proof.DeadCleanupDeletion

/-!
# Ordered deletions of whitelisted instructions

`DropSublist p xs ys`: `xs` is `ys` with some instructions satisfying `p` deleted, in order.
`DeadCleanup.PureSublist` is `DropSublist (pureForm ∨ cmpForm)` (`dropSublist_of_pure`); the skip of
unused instructions deletes `skipDel` instructions only, and the production cleanup stage (the
skip, then the cleanup) deletes `fun i => pureForm i || cmpForm i || skipDel i` ones
(`DropSublist.trans`).
-/

namespace Backend.Proof.Driver
open Backend Backend.DeadCleanup

inductive DropSublist (p : MInst → Bool) : List MInst → List MInst → Prop
  | nil : DropSublist p [] []
  | drop {xs ys : List MInst} {i : MInst} : p i = true → DropSublist p xs ys →
      DropSublist p xs (i :: ys)
  | keep {xs ys : List MInst} {i : MInst} : DropSublist p xs ys → DropSublist p (i :: xs) (i :: ys)

variable {p q : MInst → Bool}

theorem DropSublist.refl (xs : List MInst) : DropSublist p xs xs := by
  induction xs with
  | nil => exact .nil
  | cons i xs ih => exact .keep ih

theorem DropSublist.mono {xs ys : List MInst} (h : DropSublist p xs ys)
    (hpq : ∀ i, p i = true → q i = true) : DropSublist q xs ys := by
  induction h with
  | nil => exact .nil
  | drop hp _ ih => exact .drop (hpq _ hp) ih
  | keep _ ih => exact .keep ih

/-- `PureSublist` deletes pure producers and dead compares (`cmpForm`, main #605/#608): the
statement changed with the cleanup (it was `DropSublist pureForm`). -/
theorem dropSublist_of_pure {xs ys : List MInst} (h : PureSublist xs ys) :
    DropSublist (fun i => pureForm i || cmpForm i) xs ys := by
  induction h with
  | nil => exact .nil
  | drop hp _ ih => exact .drop (by rcases hp with hp | hp <;> simp [hp]) ih
  | keep _ ih => exact .keep ih

theorem DropSublist.sublist {xs ys : List MInst} (h : DropSublist p xs ys) : xs.Sublist ys := by
  induction h with
  | nil => exact .slnil
  | drop _ _ ih => exact .cons _ ih
  | keep _ ih => exact .cons_cons _ ih

/-- Deleting `p` instructions from a `q`-deletion of `zs` is a `p || q`-deletion of `zs`. -/
theorem DropSublist.trans {xs ys zs : List MInst} (h1 : DropSublist p xs ys)
    (h2 : DropSublist q ys zs) : DropSublist (fun i => p i || q i) xs zs := by
  induction h2 generalizing xs with
  | nil => cases h1; exact .nil
  | drop hq _ ih => exact .drop (by simp [hq]) (ih h1)
  | @keep ys zs j _ ih =>
    cases h1 with
    | drop hp h1 => exact .drop (by simp [hp]) (ih h1)
    | keep h1 => exact .keep (ih h1)

theorem DropSublist.head {xs ys : List MInst} (h : DropSublist p xs ys)
    {i : MInst} (hi : ys[0]? = some i) (hn : p i = false) : xs[0]? = some i := by
  induction h with
  | nil => simp at hi
  | drop hp _ _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst i
    rw [hn] at hp
    cases hp
  | keep _ _ => simpa only [List.getElem?_cons_zero] using hi

theorem DropSublist.findSome {α : Type} {xs ys : List MInst} (h : DropSublist p xs ys)
    (f : MInst → Option α) (hf : ∀ i, p i = true → f i = none) :
    xs.findSome? f = ys.findSome? f := by
  induction h with
  | nil => rfl
  | drop hp _ ih => simp [List.findSome?_cons, hf _ hp, ih]
  | keep _ ih => simp only [List.findSome?_cons, ih]

theorem DropSublist.mem {xs ys : List MInst} (h : DropSublist p xs ys)
    {i : MInst} (hi : i ∈ ys) (hp : p i = false) : i ∈ xs := by
  induction h with
  | nil => cases hi
  | @drop xs ys j hj _ ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hp] at hj
      cases hj
    · exact ih hi
  | @keep xs ys j _ ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih hi)

/-- A surviving instruction has an original position with the same instruction; the prefix
before it is a deletion of the original prefix. -/
theorem DropSublist.prefix {xs ys : List MInst} (h : DropSublist p xs ys)
    {k : Nat} {i : MInst} (hi : xs[k]? = some i) :
    ∃ pre post, ys = pre ++ i :: post ∧ DropSublist p (xs.take k) pre := by
  induction h generalizing k with
  | nil => simp at hi
  | @drop xs ys j hj _ ih =>
    obtain ⟨pre, post, he, hp⟩ := ih hi
    exact ⟨j :: pre, post, by simp [he], .drop hj hp⟩
  | @keep xs ys j _ ih =>
    cases k with
    | zero =>
      cases hi
      exact ⟨[], ys, rfl, .nil⟩
    | succ k =>
      obtain ⟨pre, post, he, hp⟩ := ih hi
      exact ⟨j :: pre, post, by simp [he], .keep hp⟩

example : DropSublist (fun _ => true) [.rets []] [.rets [], .rets []] :=
  .drop rfl (.keep .nil)

end Backend.Proof.Driver
