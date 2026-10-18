import FV.Concurrency.Rel

/-!
# Execution graphs (T2, #38)

An axiomatic execution in herd/cat style (Arm ARM B2.3; Pulte et al., POPL 2018): events with a
thread, a direction (read, write, fence) and a location; program order `po`, reads-from `rf`,
coherence order `co` and the atomic-update pairs `rmw`. Derived: from-reads `fr = rf⁻¹; co`,
communication `com = rf ∪ co ∪ fr`, `po-loc`, internal/external parts. Locations are abstract (no
mixed-size accesses), initial writes are ordinary write events. Values are not recorded: a read's
value is its `rf` source's.

`Exec.Wf` is well-formedness; the lemmas below are the facts about `com` that both memory models
(`Armv8`, `ClifMM`) use. Plan: `docs/plans/atomics.md`.
-/

namespace Concurrency

open Rel

/-- Direction of an event. -/
inductive Dir where
  | R | W | F
  deriving DecidableEq, Repr

/-- An execution graph over the events `E`. -/
structure Exec (E : Type) where
  tid : E → Nat
  dir : E → Dir
  loc : E → Nat
  po : Rel E
  rf : Rel E
  co : Rel E
  rmw : Rel E

namespace Exec

variable {E : Type} (X : Exec E)

/-- From-reads: `fr = rf⁻¹; co`. -/
def fr : Rel E := fun r w => ∃ w0, X.rf w0 r ∧ X.co w0 w

/-- Communication: `com = rf ∪ co ∪ fr`. -/
def com : Rel E := fun a b => X.rf a b ∨ X.co a b ∨ X.fr a b

/-- `po-loc`: program order between accesses of the same location. -/
def poLoc : Rel E := fun a b =>
  X.po a b ∧ X.loc a = X.loc b ∧ X.dir a ≠ .F ∧ X.dir b ≠ .F

/-- The external part `re` of a relation (different threads). -/
def ext (r : Rel E) : Rel E := fun a b => r a b ∧ X.tid a ≠ X.tid b

/-- Sequential consistency of the execution: `acyclic(po ∪ com)`. -/
def SC : Prop := Acyclic (union X.po X.com)

/-- Well-formedness. -/
structure Wf : Prop where
  po_irrefl : ∀ a, ¬ X.po a a
  po_trans : ∀ a b c, X.po a b → X.po b c → X.po a c
  po_tid : ∀ a b, X.po a b → X.tid a = X.tid b
  /-- `po` is total on each thread. -/
  po_total : ∀ a b, X.tid a = X.tid b → a ≠ b → X.po a b ∨ X.po b a
  rf_dir : ∀ a b, X.rf a b → X.dir a = .W ∧ X.dir b = .R
  rf_loc : ∀ a b, X.rf a b → X.loc a = X.loc b
  rf_func : ∀ a a' b, X.rf a b → X.rf a' b → a = a'
  /-- Every read reads from some write (initial writes are events). -/
  rf_total : ∀ b, X.dir b = .R → ∃ a, X.rf a b
  co_dir : ∀ a b, X.co a b → X.dir a = .W ∧ X.dir b = .W
  co_loc : ∀ a b, X.co a b → X.loc a = X.loc b
  co_irrefl : ∀ a, ¬ X.co a a
  co_trans : ∀ a b c, X.co a b → X.co b c → X.co a c
  /-- `co` is total on the writes of each location. -/
  co_total : ∀ a b, X.dir a = .W → X.dir b = .W → X.loc a = X.loc b → a ≠ b →
    X.co a b ∨ X.co b a
  rmw_dir : ∀ a b, X.rmw a b → X.dir a = .R ∧ X.dir b = .W
  rmw_loc : ∀ a b, X.rmw a b → X.loc a = X.loc b
  rmw_po : ∀ a b, X.rmw a b → X.po a b
  /-- The two halves of an atomic update are `po`-adjacent. -/
  rmw_imm : ∀ a b c, X.rmw a b → X.po a c → X.po c b → False

variable {X}

namespace Wf

variable (hX : X.Wf)
include hX

theorem fr_dir {a b : E} (h : X.fr a b) : X.dir a = .R ∧ X.dir b = .W := by
  obtain ⟨w, h1, h2⟩ := h
  exact ⟨(hX.rf_dir _ _ h1).2, (hX.co_dir _ _ h2).2⟩

theorem fr_loc {a b : E} (h : X.fr a b) : X.loc a = X.loc b := by
  obtain ⟨w, h1, h2⟩ := h
  rw [← hX.rf_loc _ _ h1, hX.co_loc _ _ h2]

theorem com_loc {a b : E} (h : X.com a b) : X.loc a = X.loc b := by
  rcases h with h | h | h
  · exact hX.rf_loc _ _ h
  · exact hX.co_loc _ _ h
  · exact hX.fr_loc h

theorem com_notF {a b : E} (h : X.com a b) : X.dir a ≠ .F ∧ X.dir b ≠ .F := by
  rcases h with h | h | h
  · obtain ⟨h1, h2⟩ := hX.rf_dir _ _ h; rw [h1, h2]; decide
  · obtain ⟨h1, h2⟩ := hX.co_dir _ _ h; rw [h1, h2]; decide
  · obtain ⟨h1, h2⟩ := hX.fr_dir h; rw [h1, h2]; decide

/-- A `com` edge has a write at one end. -/
theorem com_write {a b : E} (h : X.com a b) : X.dir a = .W ∨ X.dir b = .W := by
  rcases h with h | h | h
  · exact .inl (hX.rf_dir _ _ h).1
  · exact .inl (hX.co_dir _ _ h).1
  · exact .inr (hX.fr_dir h).2

theorem com_ne {a b : E} (h : X.com a b) : a ≠ b := by
  rintro rfl
  rcases h with h | h | h
  · have := hX.rf_dir _ _ h; rw [this.1] at this; exact absurd this.2 (by decide)
  · exact hX.co_irrefl _ h
  · have := hX.fr_dir h; rw [this.1] at this; exact absurd this.2 (by decide)

theorem fr_co {a b c : E} (h1 : X.fr a b) (h2 : X.co b c) : X.fr a c := by
  obtain ⟨w, hw, hwb⟩ := h1
  exact ⟨w, hw, hX.co_trans _ _ _ hwb h2⟩

theorem rf_fr {a b c : E} (h1 : X.rf a b) (h2 : X.fr b c) : X.co a c := by
  obtain ⟨w, hw, hwc⟩ := h2
  rw [hX.rf_func _ _ _ h1 hw]; exact hwc

/-- The shape of `com⁺` (`eco`): `rf ∪ co ∪ fr ∪ co;rf ∪ fr;rf`. -/
def EcoShape (X : Exec E) (a b : E) : Prop :=
  X.rf a b ∨ X.co a b ∨ X.fr a b ∨ (∃ c, X.co a c ∧ X.rf c b) ∨ (∃ c, X.fr a c ∧ X.rf c b)

omit hX in
theorem ecoShape_of_com {a b : E} (h : X.com a b) : EcoShape X a b := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))

theorem ecoShape_tail {a b c : E} (h1 : EcoShape X a b) (h2 : X.com b c) : EcoShape X a c := by
  -- a write cannot be the target of `rf`'s source side twice, etc.: the impossible compositions
  -- are those whose middle event would be both a read and a write
  have rw_ne : ∀ {e : E}, X.dir e = .R → X.dir e = .W → False := by
    intro e h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  rcases h1 with h1 | h1 | h1 | ⟨d, h1, h1'⟩ | ⟨d, h1, h1'⟩ <;>
    rcases h2 with h2 | h2 | h2
  -- rf; _
  · exact absurd (hX.rf_dir _ _ h2).1 (fun h => rw_ne (hX.rf_dir _ _ h1).2 h)
  · exact absurd (hX.co_dir _ _ h2).1 (fun h => rw_ne (hX.rf_dir _ _ h1).2 h)
  · exact .inr (.inl (hX.rf_fr h1 h2))
  -- co; _
  · exact .inr (.inr (.inr (.inl ⟨_, h1, h2⟩)))
  · exact .inr (.inl (hX.co_trans _ _ _ h1 h2))
  · exact absurd (hX.fr_dir h2).1 (fun h => rw_ne h (hX.co_dir _ _ h1).2)
  -- fr; _
  · exact .inr (.inr (.inr (.inr ⟨_, h1, h2⟩)))
  · exact .inr (.inr (.inl (hX.fr_co h1 h2)))
  · exact absurd (hX.fr_dir h2).1 (fun h => rw_ne h (hX.fr_dir h1).2)
  -- co;rf; _
  · exact absurd (hX.rf_dir _ _ h2).1 (fun h => rw_ne (hX.rf_dir _ _ h1').2 h)
  · exact absurd (hX.co_dir _ _ h2).1 (fun h => rw_ne (hX.rf_dir _ _ h1').2 h)
  · exact .inr (.inl (hX.co_trans _ _ _ h1 (hX.rf_fr h1' h2)))
  -- fr;rf; _
  · exact absurd (hX.rf_dir _ _ h2).1 (fun h => rw_ne (hX.rf_dir _ _ h1').2 h)
  · exact absurd (hX.co_dir _ _ h2).1 (fun h => rw_ne (hX.rf_dir _ _ h1').2 h)
  · exact .inr (.inr (.inl (hX.fr_co h1 (hX.rf_fr h1' h2))))

/-- `com⁺ ⊆ rf ∪ co ∪ fr ∪ co;rf ∪ fr;rf`. -/
theorem eco_shape {a b : E} (h : Relation.TransGen X.com a b) : EcoShape X a b := by
  induction h with
  | single h => exact ecoShape_of_com h
  | tail _ h2 ih => exact hX.ecoShape_tail ih h2

theorem eco_loc {a b : E} (h : Relation.TransGen X.com a b) : X.loc a = X.loc b := by
  induction h with
  | single h => exact hX.com_loc h
  | tail _ h2 ih => exact ih.trans (hX.com_loc h2)

theorem eco_notF {a b : E} (h : Relation.TransGen X.com a b) : X.dir a ≠ .F ∧ X.dir b ≠ .F := by
  obtain ⟨c, hc, -⟩ := plus_head h
  obtain ⟨d, hd⟩ := plus_last h
  exact ⟨(hX.com_notF hc).1, (hX.com_notF hd).2⟩

/-- **Internal communication is in `po`** under SC per location (`acyclic(po-loc ∪ com)`). -/
theorem com_int_po (hI : Acyclic (union X.poLoc X.com)) {a b : E} (h : X.com a b)
    (ht : X.tid a = X.tid b) : X.po a b := by
  rcases hX.po_total a b ht (hX.com_ne h) with h' | h'
  · exact h'
  · exfalso
    have hpl : X.poLoc b a :=
      ⟨h', (hX.com_loc h).symm, (hX.com_notF h).2, (hX.com_notF h).1⟩
    exact hI b (.tail (.single (.inl hpl)) (.inr h))

end Wf

end Exec

end Concurrency
