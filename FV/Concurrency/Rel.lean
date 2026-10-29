module

@[expose] public section

/-!
# Relations for axiomatic memory models (T2, #38)

Event relations as `α → α → Prop` with the herd/cat operators the memory models of
`FV/Concurrency/Armv8.lean` and `FV/Concurrency/ClifMM.lean` use: union, sequence, the reflexive
closure `r?`, the transitive closure `r⁺` (`Relation.TransGen`), irreflexivity and acyclicity.
Plan: `docs/plans/atomics.md`.
-/

namespace Concurrency

/-- A binary relation on events. -/
abbrev Rel (α : Type) := α → α → Prop

namespace Rel

variable {α β : Type} {r s : Rel α}

/-- `r ∪ s`. -/
def union (r s : Rel α) : Rel α := fun a b => r a b ∨ s a b

/-- `r ; s`. -/
def seq (r s : Rel α) : Rel α := fun a c => ∃ b, r a b ∧ s b c

/-- `r?`, the reflexive closure. -/
def opt (r : Rel α) : Rel α := fun a b => a = b ∨ r a b

/-- `[P]; r; [P]`: `r` between events of `P`. -/
def restr (P : α → Prop) (r : Rel α) : Rel α := fun a b => P a ∧ r a b ∧ P b

/-- `irreflexive(r)`. -/
def Irrefl (r : Rel α) : Prop := ∀ a, ¬ r a a

/-- `acyclic(r)`: `r⁺` is irreflexive. -/
def Acyclic (r : Rel α) : Prop := ∀ a, ¬ Relation.TransGen r a a

/-- `r` is transitive. -/
def Trans (r : Rel α) : Prop := ∀ a b c, r a b → r b c → r a c

theorem plus_map {r : Rel α} {s : Rel β} (f : α → β) (h : ∀ a b, r a b → s (f a) (f b))
    {a b : α} (hab : Relation.TransGen r a b) : Relation.TransGen s (f a) (f b) := by
  induction hab with
  | single h1 => exact .single (h _ _ h1)
  | tail _ h2 ih => exact .tail ih (h _ _ h2)

theorem plus_mono (h : ∀ a b, r a b → s a b) {a b : α} (hab : Relation.TransGen r a b) :
    Relation.TransGen s a b :=
  plus_map id h hab

/-- A relation inside the transitive closure of `s` has its closure there too. -/
theorem plus_flat (h : ∀ a b, r a b → Relation.TransGen s a b) {a b : α}
    (hab : Relation.TransGen r a b) : Relation.TransGen s a b := by
  induction hab with
  | single h1 => exact h _ _ h1
  | tail _ h2 ih => exact ih.trans (h _ _ h2)

theorem Acyclic.mono (h : ∀ a b, r a b → s a b) (hs : Acyclic s) : Acyclic r :=
  fun a ha => hs a (plus_mono h ha)

theorem Acyclic.of_plus (h : ∀ a b, r a b → Relation.TransGen s a b) (hs : Acyclic s) :
    Acyclic r :=
  fun a ha => hs a (plus_flat h ha)

theorem plus_of_trans (ht : Trans r) {a b : α} (h : Relation.TransGen r a b) : r a b := by
  induction h with
  | single h => exact h
  | tail _ h2 ih => exact ht _ _ _ ih h2

/-- A relation increasing a natural-number rank is acyclic (the certificate the witnesses use). -/
theorem acyclic_of_rank (f : α → Nat) (h : ∀ a b, r a b → f a < f b) : Acyclic r := by
  intro a ha
  have key : ∀ {x y}, Relation.TransGen r x y → f x < f y := by
    intro x y hxy
    induction hxy with
    | single h1 => exact h _ _ h1
    | tail _ h2 ih => exact Nat.lt_trans ih (h _ _ h2)
  exact Nat.lt_irrefl _ (key ha)

/-- The first step of a path. -/
theorem plus_head {a b : α} (h : Relation.TransGen r a b) :
    ∃ c, r a c ∧ (c = b ∨ Relation.TransGen r c b) := by
  induction h with
  | single h => exact ⟨_, h, .inl rfl⟩
  | tail _ h2 ih =>
    obtain ⟨c, hac, hcb⟩ := ih
    refine ⟨c, hac, .inr ?_⟩
    rcases hcb with rfl | hcb
    · exact .single h2
    · exact .tail hcb h2

/-- The last step of a path. -/
theorem plus_last {a b : α} (h : Relation.TransGen r a b) : ∃ c, r c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h2 => exact ⟨_, h2⟩

/-- A path through `r ∪ s` with `r` transitive: one `r` step, or `(r?; s)⁺` followed by `r?`. -/
theorem path_split (ht : Trans r) {a b : α} (h : Relation.TransGen (union r s) a b) :
    r a b ∨ ∃ c, Relation.TransGen (seq (opt r) s) a c ∧ opt r c b := by
  induction h with
  | single h =>
    rcases h with h | h
    · exact .inl h
    · exact .inr ⟨_, .single ⟨_, .inl rfl, h⟩, .inl rfl⟩
  | tail _ h2 ih =>
    rcases ih with h1 | ⟨c, hp, hc⟩
    · rcases h2 with h2 | h2
      · exact .inl (ht _ _ _ h1 h2)
      · exact .inr ⟨_, .single ⟨_, .inr h1, h2⟩, .inl rfl⟩
    · rcases h2 with h2 | h2
      · refine .inr ⟨c, hp, .inr ?_⟩
        rcases hc with rfl | hc
        · exact h2
        · exact ht _ _ _ hc h2
      · exact .inr ⟨_, .tail hp ⟨_, hc, h2⟩, .inl rfl⟩

/-- **Cycles through `r ∪ s` with `r` transitive**: an `r` loop, or a cycle of `r?; s` steps
(rotated to start after an `s` step). -/
theorem cycle_split (ht : Trans r) {a : α} (h : Relation.TransGen (union r s) a a) :
    r a a ∨ ∃ b, Relation.TransGen (seq (opt r) s) b b := by
  rcases path_split ht h with h | ⟨c, hp, hc⟩
  · exact .inl h
  · rcases hc with rfl | hca
    · exact .inr ⟨_, hp⟩
    · -- rotate: prepend `r c a` to the first step of `a → c`
      obtain ⟨d, ⟨e, hae, hed⟩, hdc⟩ := plus_head hp
      have hce : r c e := by
        rcases hae with rfl | hae
        · exact hca
        · exact ht _ _ _ hca hae
      have hcd : seq (opt r) s c d := ⟨e, .inr hce, hed⟩
      refine .inr ⟨c, ?_⟩
      rcases hdc with rfl | hdc
      · exact .single hcd
      · exact (Relation.TransGen.single hcd).trans hdc

end Rel

end Concurrency
