module

public import FV.Front.Rename

@[expose] public section

/-!
# A bijection of names from finitely many pairs (T7d)

`Ren.ofPairs ps`: a bijection of `String` that maps `a` to `b` for every pair `(a, b)` of `ps`
when the first components are distinct and the second components are distinct
(`Ren.ofPairs_fwd`), built from transpositions: for `(a, b) :: ps`, the bijection `π` of `ps`
followed by the transposition of `π a` and `b`. It moves no name outside the pairs
(`Ren.ofPairs_fwd_other`).
-/

namespace Clif

namespace Ren

/-- Exchange `a` and `b`. -/
def sw (a b x : String) : String := if x = a then b else if x = b then a else x

theorem sw_sw (a b x : String) : sw a b (sw a b x) = x := by
  unfold sw
  by_cases h1 : x = a
  · subst h1
    by_cases h2 : b = x <;> simp [h2]
  · by_cases h2 : x = b
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- The transposition of `a` and `b`. -/
def swap (a b : String) : Ren := ⟨sw a b, sw a b, sw_sw a b, sw_sw a b⟩

/-- **The bijection of the pairs** (`ofPairs_fwd`). -/
def ofPairs : List (String × String) → Ren
  | [] => Ren.id
  | (a, b) :: ps => (ofPairs ps).trans (swap ((ofPairs ps).fwd a) b)

theorem ofPairs_cons_fwd (a b : String) (ps : List (String × String)) (x : String) :
    (ofPairs ((a, b) :: ps)).fwd x = sw ((ofPairs ps).fwd a) b ((ofPairs ps).fwd x) := rfl

/-- **`ofPairs` maps every pair's first component to its second**, for distinct first and
distinct second components. -/
theorem ofPairs_fwd : ∀ (ps : List (String × String)), (ps.map (·.1)).Nodup →
    (ps.map (·.2)).Nodup → ∀ a b, (a, b) ∈ ps → (ofPairs ps).fwd a = b
  | [], _, _, _, _, h => nomatch h
  | (a0, b0) :: ps, h1, h2, a, b, hm => by
    rw [List.map_cons, List.nodup_cons] at h1 h2
    rw [ofPairs_cons_fwd]
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      simp [sw]
    · have ih := ofPairs_fwd ps h1.2 h2.2 a b hm
      rw [ih]
      have hb : b ≠ b0 := fun he => h2.1 (he ▸ List.mem_map_of_mem (f := (·.2)) hm)
      have ha : a ≠ a0 := fun he => h1.1 (he ▸ List.mem_map_of_mem (f := (·.1)) hm)
      have hb' : b ≠ (ofPairs ps).fwd a0 := by
        rw [← ih]; exact fun he => ha ((ofPairs ps).fwd_inj he)
      simp [sw, hb, hb']

/-- `ofPairs` moves no name that is no component of a pair. -/
theorem ofPairs_fwd_other : ∀ (ps : List (String × String)) (x : String),
    x ∉ ps.map (·.1) → x ∉ ps.map (·.2) → (ofPairs ps).fwd x = x
  | [], _, _, _ => rfl
  | (a0, b0) :: ps, x, h1, h2 => by
    simp only [List.map_cons, List.mem_cons, not_or] at h1 h2
    have ih := ofPairs_fwd_other ps x h1.2 h2.2
    rw [ofPairs_cons_fwd, ih]
    have hx : x ≠ (ofPairs ps).fwd a0 := by
      intro he
      have : a0 = x := (ofPairs ps).fwd_inj (by rw [ih]; exact he.symm)
      exact h1.1 this.symm
    have hx' : x ≠ b0 := h2.1
    simp [sw, hx, hx']

/-- Pairs that are a partial bijection: two pairs agree in their first components iff they
agree in their second ones (duplicates allowed). -/
def Consistent (ps : List (String × String)) : Prop :=
  ∀ a b a' b', (a, b) ∈ ps → (a', b') ∈ ps → (a = a' ↔ b = b')

theorem Consistent.tail {p : String × String} {ps : List (String × String)}
    (h : Consistent (p :: ps)) : Consistent ps :=
  fun a b a' b' h1 h2 => h a b a' b' (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2)

/-- **`ofPairs` maps every pair's first component to its second**, for pairs that are a partial
bijection (duplicates allowed). -/
theorem ofPairs_fwd_of_consistent : ∀ (ps : List (String × String)), Consistent ps →
    ∀ a b, (a, b) ∈ ps → (ofPairs ps).fwd a = b
  | [], _, _, _, h => nomatch h
  | (a0, b0) :: ps, hc, a, b, hm => by
    have ih := ofPairs_fwd_of_consistent ps hc.tail
    rw [ofPairs_cons_fwd]
    have h0 : (a0, b0) ∈ (a0, b0) :: ps := List.mem_cons_self
    by_cases hk : ∃ b', (a0, b') ∈ ps
    · -- `(a0, b0)` repeats a pair of `ps`: the transposition is the identity
      obtain ⟨b', hb'⟩ := hk
      have hbb : b' = b0 := (hc a0 b' a0 b0 (List.mem_cons_of_mem _ hb') h0).1 rfl
      subst hbb
      rw [ih a0 b' hb']
      have hsw : ∀ x, sw b' b' x = x := fun x => by unfold sw; split <;> simp_all
      rw [hsw]
      rcases List.mem_cons.mp hm with he | hm
      · cases he; exact ih _ _ hb'
      · exact ih a b hm
    · have hk' : ∀ b', (a0, b') ∉ ps := fun b' h => hk ⟨b', h⟩
      rcases List.mem_cons.mp hm with he | hm
      · cases he; simp [sw]
      · rw [ih a b hm]
        have ha : a ≠ a0 := fun he => hk' b (he ▸ hm)
        have hb : b ≠ b0 := fun he =>
          ha ((hc a b a0 b0 (List.mem_cons_of_mem _ hm) h0).2 he)
        have hb' : b ≠ (ofPairs ps).fwd a0 := by
          rw [← ih a b hm]; exact fun he => ha ((ofPairs ps).fwd_inj he)
        simp [sw, hb, hb']

end Ren

end Clif
