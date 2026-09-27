/-!
# `DSL.Map`: the abstract finite-map collection

A deterministic, insertion-ordered association list. `insert` on a present key replaces the
value in place (position kept); on an absent key it appends. Hence iteration order is the
order of first insertion, independent of hashing. Programs only observe a map through
`get?`/`contains`/`size`, whose laws are proven below; the runtime (`flat-runtime`) may use
any representation satisfying these laws (see `docs/contracts/dsl.md`, "Collections").
-/

namespace DSL

/-- Finite map, insertion-ordered. Invariant (maintained by `insert`, not required by the
laws): keys are pairwise distinct. -/
structure Map (K V : Type) where
  entries : List (K × V)
  deriving DecidableEq, Repr, BEq

namespace Map

variable {K V : Type} [DecidableEq K]

def empty : Map K V := ⟨[]⟩

instance : Inhabited (Map K V) := ⟨empty⟩

/-- Lookup in an entry list (first match). -/
def lookupL (k : K) : List (K × V) → Option V
  | [] => none
  | (k', v) :: t => if k = k' then some v else lookupL k t

/-- Update-in-place or append. -/
def upsertL (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k', v') :: t => if k = k' then (k, v) :: t else (k', v') :: upsertL k v t

def get? (m : Map K V) (k : K) : Option V := lookupL k m.entries
def contains (m : Map K V) (k : K) : Bool := (m.get? k).isSome
def insert (m : Map K V) (k : K) (v : V) : Map K V := ⟨upsertL k v m.entries⟩
def size (m : Map K V) : Nat := m.entries.length
def keys (m : Map K V) : List K := m.entries.map Prod.fst

/-! ## Laws -/

@[simp] theorem get?_empty (k : K) : (empty : Map K V).get? k = none := rfl

@[simp] theorem contains_empty (k : K) : (empty : Map K V).contains k = false := rfl

theorem lookupL_upsertL_self (k : K) (v : V) :
    ∀ l : List (K × V), lookupL k (upsertL k v l) = some v
  | [] => by simp [upsertL, lookupL]
  | (k', v') :: t => by
    by_cases h : k = k'
    · simp [upsertL, lookupL, h]
    · simp [upsertL, lookupL, h, lookupL_upsertL_self k v t]

theorem lookupL_upsertL_ne {k k₂ : K} (v : V) (hne : k₂ ≠ k) :
    ∀ l : List (K × V), lookupL k₂ (upsertL k v l) = lookupL k₂ l
  | [] => by simp [upsertL, lookupL, hne]
  | (k', v') :: t => by
    by_cases h : k = k'
    · subst h; simp [upsertL, lookupL, hne]
    · simp only [upsertL, h, ↓reduceIte, lookupL]
      split <;> simp [lookupL_upsertL_ne v hne t]

/-- get-after-insert, same key. -/
@[simp] theorem get?_insert_self (m : Map K V) (k : K) (v : V) :
    (m.insert k v).get? k = some v :=
  lookupL_upsertL_self k v m.entries

/-- get-after-insert, other key. -/
@[simp] theorem get?_insert_ne (m : Map K V) {k k₂ : K} (v : V) (h : k₂ ≠ k) :
    (m.insert k v).get? k₂ = m.get? k₂ :=
  lookupL_upsertL_ne v h m.entries

theorem get?_insert (m : Map K V) (k k₂ : K) (v : V) :
    (m.insert k v).get? k₂ = if k₂ = k then some v else m.get? k₂ := by
  split
  · subst_vars; simp
  · simp [*]

@[simp] theorem contains_insert_self (m : Map K V) (k : K) (v : V) :
    (m.insert k v).contains k = true := by
  simp [contains]

@[simp] theorem contains_insert_ne (m : Map K V) {k k₂ : K} (v : V) (h : k₂ ≠ k) :
    (m.insert k v).contains k₂ = m.contains k₂ := by
  simp [contains, h]

theorem contains_insert (m : Map K V) (k k₂ : K) (v : V) :
    (m.insert k v).contains k₂ = (k₂ == k || m.contains k₂) := by
  by_cases h : k₂ = k
  · subst h; simp
  · simp [h]

theorem contains_iff_get? (m : Map K V) (k : K) : m.contains k = true ↔ ∃ v, m.get? k = some v := by
  simp [contains, Option.isSome_iff_exists]

theorem lookupL_eq_none_length_upsertL (k : K) (v : V) :
    ∀ l : List (K × V), lookupL k l = none → (upsertL k v l).length = l.length + 1
  | [] => by simp [upsertL]
  | (k', v') :: t => by
    intro h
    by_cases hk : k = k'
    · simp [lookupL, hk] at h
    · simp [lookupL, hk] at h
      simp [upsertL, hk, lookupL_eq_none_length_upsertL k v t h]

theorem lookupL_isSome_length_upsertL (k : K) (v : V) :
    ∀ l : List (K × V), (lookupL k l).isSome → (upsertL k v l).length = l.length
  | [] => by simp [lookupL]
  | (k', v') :: t => by
    intro h
    by_cases hk : k = k'
    · simp [upsertL, hk]
    · simp [lookupL, hk] at h
      simp [upsertL, hk, lookupL_isSome_length_upsertL k v t h]

/-- Inserting a fresh key grows the map by one. -/
theorem size_insert_of_not_contains (m : Map K V) (k : K) (v : V) (h : m.contains k = false) :
    (m.insert k v).size = m.size + 1 := by
  simp [contains, get?] at h
  exact lookupL_eq_none_length_upsertL k v m.entries h

/-- Overwriting a present key keeps the size. -/
theorem size_insert_of_contains (m : Map K V) (k : K) (v : V) (h : m.contains k = true) :
    (m.insert k v).size = m.size :=
  lookupL_isSome_length_upsertL k v m.entries h

/-- Insert is idempotent on the observable `get?`. -/
theorem get?_insert_insert (m : Map K V) (k k₂ : K) (v w : V) :
    ((m.insert k v).insert k w).get? k₂ = (m.insert k w).get? k₂ := by
  simp only [get?_insert]; split <;> rfl

end Map
end DSL
