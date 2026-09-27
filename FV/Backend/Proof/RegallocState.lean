import FV.Backend.Proof.VCodeSem

/-!
# The checker's abstract state: lemmas and the invariant `Inv` (M6 proof)

`Inv keep a m ρ r₀`: every symbol the abstract state `a` puts in a location holds there —
`vreg v` means `m ℓ = ρ v`; `entry r` means `r` is callee-saved and `m ℓ` agrees with the
entry value `r₀ r` on its `keep r`-part. Each transfer function of the checker preserves it
(`Inv_move`, `Inv_defineAll`, `Inv_clobberAll`, `Inv_parCopy`, `Inv_mono`), and it holds at the
function entry (`Inv_entryState`).

All lemmas are about *membership upper bounds*: the checker only ever needs "what `a'` claims
was already claimed (or was just established)".
-/

namespace Backend.Proof

open Backend

/-! ## Locations and `AState` -/

theorem Loc.index_inj {l l' : Loc} {i : Nat} (h : l.index = some i) (h' : l'.index = some i) :
    l = l' := by
  rcases l with ((_|n|_|_|n)|⟨s, _|_⟩|(_|n|_|_|n)) <;>
  rcases l' with ((_|n'|_|_|n')|⟨s', _|_⟩|(_|n'|_|_|n')) <;>
  simp only [Loc.index] at h h' <;> (try split at h) <;> (try split at h') <;> simp_all <;> omega

theorem AState.mem_get {a : AState} {l : Loc} {s : Sym} (h : s ∈ AState.get a l) :
    ∃ i, l.index = some i ∧ s ∈ a.getD i [] := by
  unfold AState.get at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · simp at h

theorem AState.mem_get_of {a : AState} {l : Loc} {i : Nat} {s : Sym} (hi : l.index = some i)
    (h : s ∈ a.getD i []) : s ∈ AState.get a l := by
  unfold AState.get; rw [hi]; exact h

theorem AState.mem_get_put {a : AState} {l l' : Loc} {xs : List Sym} {s : Sym}
    (h : s ∈ AState.get (AState.put a l xs) l') : (l' = l ∧ s ∈ xs) ∨ (l' ≠ l ∧ s ∈ AState.get a l') := by
  obtain ⟨j, hj, hs⟩ := AState.mem_get h
  unfold AState.put at hs
  split at hs
  · rename_i i hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at hs
    by_cases hij : i = j
    · subst hij
      left
      refine ⟨Loc.index_inj hj hi, ?_⟩
      by_cases hlt : i < a.size <;> simp [hlt] at hs
      exact hs
    · simp only [hij, ite_false] at hs
      right
      refine ⟨fun e => hij (by subst e; rw [hi] at hj; exact Option.some.inj hj), ?_⟩
      exact AState.mem_get_of hj (by rw [Array.getD_eq_getD_getElem?]; exact hs)
  · rename_i hn
    right
    exact ⟨fun e => (by subst e; rw [hn] at hj; cases hj), AState.mem_get_of hj hs⟩

theorem AState.mem_get_map {a : AState} {f : List Sym → List Sym} {l : Loc} {s : Sym}
    (h : s ∈ AState.get (a.map f) l) : s ∈ f (AState.get a l) := by
  obtain ⟨i, hi, hs⟩ := AState.mem_get h
  simp only [AState.get, hi, Array.getD_eq_getD_getElem?]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map] at hs
  cases h' : a[i]? <;> simp_all

theorem AState.mem_get_remove {a : AState} {t s : Sym} {l : Loc}
    (h : s ∈ AState.get (a.remove t) l) : s ∈ AState.get a l ∧ s ≠ t := by
  have := AState.mem_get_map h
  simpa using this

theorem AState.mem_get_define {a : AState} {l l' : Loc} {t s : Sym}
    (h : s ∈ AState.get (a.define l t) l') :
    (l' = l ∧ s = t) ∨ (l' ≠ l ∧ s ∈ AState.get a l' ∧ s ≠ t) := by
  unfold AState.define at h
  rcases AState.mem_get_put h with ⟨e, hs⟩ | ⟨e, hs⟩
  · exact .inl ⟨e, by simpa using hs⟩
  · exact .inr ⟨e, AState.mem_get_remove hs⟩

theorem AState.mem_get_meet {a b : AState} {l : Loc} {s : Sym} (h : s ∈ AState.get (a.meet b) l) :
    s ∈ AState.get a l ∧ s ∈ AState.get b l := by
  obtain ⟨i, hi, hs⟩ := AState.mem_get h
  unfold AState.meet at hs
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx] at hs
  cases h' : a[i]? with
  | none => simp [h'] at hs
  | some xs =>
    simp only [h', Option.map_some, Option.getD_some, List.mem_filter] at hs
    refine ⟨AState.mem_get_of hi ?_, AState.mem_get_of hi ?_⟩
    · rw [Array.getD_eq_getD_getElem?, h']; exact hs.1
    · simpa using hs.2

theorem AState.mem_get_le {a b : AState} {l : Loc} {s : Sym} (hle : a.le b = true)
    (h : s ∈ AState.get a l) : s ∈ AState.get b l := by
  obtain ⟨i, hi, hs⟩ := AState.mem_get h
  unfold AState.le at hle
  have hlt : i < a.size := by
    rw [Array.getD_eq_getD_getElem?] at hs
    apply Classical.byContradiction
    intro hc
    rw [Array.getElem?_eq_none (by omega)] at hs
    simp at hs
  have := (List.all_eq_true.mp hle) i (List.mem_range.mpr hlt)
  have := (List.all_eq_true.mp this) s hs
  exact AState.mem_get_of hi (by simpa using this)

theorem AState.mem_get_parCopy {a : AState} {ps xs : List Nat} {l : Loc} {s : Sym}
    (h : s ∈ AState.get (a.parCopy ps xs) l) :
    (s ∈ AState.get a l ∧ s ∉ ps.map Sym.vreg) ∨
      (∃ p x, (p, x) ∈ ps.zip xs ∧ s = .vreg p ∧ Sym.vreg x ∈ AState.get a l) := by
  have h := AState.mem_get_map h
  simp only [List.mem_append, List.mem_filter, List.mem_filterMap] at h
  rcases h with ⟨hs, hn⟩ | ⟨⟨⟨p, x⟩, hpx, hsome⟩, _⟩
  · left; exact ⟨hs, by simpa using hn⟩
  · right
    split at hsome
    · rename_i hc
      exact ⟨p, x, hpx, (Option.some.inj hsome).symm, by simpa using hc⟩
    · cases hsome

/-! ## The invariant -/

section
variable {V : Type} (keep : Reg → V → V)

/-- The meaning of a symbol, as a predicate on the value of the location holding it. -/
def Holds (ρ : Nat → V) (r₀ : Reg → V) : Sym → V → Prop
  | .vreg v, x => x = ρ v
  | .entry r, x => r ∈ calleeSaved ∧ keep r x = keep r (r₀ r)

/-- The checker's invariant between an abstract state and the concrete store. -/
def Inv (a : AState) (m : Loc → V) (ρ : Nat → V) (r₀ : Reg → V) : Prop :=
  ∀ l s, s ∈ a.get l → Holds keep ρ r₀ s (m l)

variable {keep}

theorem Inv_mono {a b : AState} {m : Loc → V} {ρ r₀} (hle : a.le b = true)
    (h : Inv keep b m ρ r₀) : Inv keep a m ρ r₀ :=
  fun l s hs => h l s (AState.mem_get_le hle hs)

theorem Inv_move {a : AState} {m : Loc → V} {ρ r₀} (src dst : Loc)
    (h : Inv keep a m ρ r₀) : Inv keep (a.put dst (a.get src)) (upd m dst (m src)) ρ r₀ := by
  intro l s hs
  rcases AState.mem_get_put hs with ⟨e, hs'⟩ | ⟨e, hs'⟩
  · simp only [upd, e, ite_true]; exact h _ _ hs'
  · simp only [upd, e, ite_false]; exact h _ _ hs'

theorem Inv_define {a : AState} {m : Loc → V} {ρ r₀} (l : Loc) (v : Nat) (x : V)
    (h : Inv keep a m ρ r₀) : Inv keep (a.define l (.vreg v)) (upd m l x) (upd ρ v x) r₀ := by
  intro l' s hs
  rcases AState.mem_get_define hs with ⟨e, rfl⟩ | ⟨e, hs, hne⟩
  · subst e; simp [Holds, upd]
  · have := h _ _ hs
    simp only [upd, e, ite_false]
    cases s with
    | vreg u =>
      have hu : u ≠ v := fun hu => hne (by rw [hu])
      simp only [Holds, upd, hu, ite_false] at this ⊢; exact this
    | entry r => exact this

theorem Inv_defineAll {a : AState} {m : Loc → V} {ρ r₀} (dl : List ((Operand × Loc) × V))
    (h : Inv keep a m ρ r₀) :
    Inv keep (defineAll a (dl.map (·.1))) (writeM m dl) (writeV ρ (dl.map fun p => (p.1.1, p.2)))
      r₀ := by
  induction dl generalizing a m ρ with
  | nil => exact h
  | cons p dl ih =>
    obtain ⟨⟨o, l⟩, x⟩ := p
    exact ih (Inv_define l o.vreg x h)

theorem mem_get_defineAll {a : AState} {ds : List (Operand × Loc)} {l : Loc} {s : Sym}
    (hl : l ∉ ds.map (·.2)) (h : s ∈ (defineAll a ds).get l) : s ∈ a.get l := by
  induction ds generalizing a with
  | nil => exact h
  | cons d ds ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hl
    have := ih hl.2 h
    rcases AState.mem_get_define this with ⟨e, _⟩ | ⟨_, hs, _⟩
    · exact absurd e hl.1
    · exact hs

theorem mem_get_clobberAll {a : AState} {clob : List Reg} {l : Loc} {s : Sym}
    (h : s ∈ (clobberAll a clob).get l) : s ∈ a.get l ∧ ∀ c ∈ clob, l = .reg c → s = .entry c := by
  induction clob generalizing a with
  | nil => exact ⟨h, by simp⟩
  | cons c clob ih =>
    obtain ⟨h1, h2⟩ := ih h
    rcases AState.mem_get_put h1 with ⟨e, hs⟩ | ⟨e, hs⟩
    · simp only [List.mem_filter, beq_iff_eq] at hs
      refine ⟨e ▸ hs.1, ?_⟩
      intro c' hc' e'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hs.2
      · exact h2 c' hc' e'
    · refine ⟨hs, ?_⟩
      intro c' hc' e'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact absurd e' e
      · exact h2 c' hc' e'

theorem Inv_clobberAll {a : AState} {m m' : Loc → V} {ρ r₀} {clob : List Reg}
    (h : Inv keep a m ρ r₀) (hc : Clobbered keep clob m m') :
    Inv keep (clobberAll a clob) m' ρ r₀ := by
  intro l s hs
  obtain ⟨hs, hcl⟩ := mem_get_clobberAll hs
  by_cases hl : ∃ c ∈ clob, l = .reg c
  · obtain ⟨c, hc', rfl⟩ := hl
    have hsc := hcl c hc' rfl
    subst hsc
    obtain ⟨hcs, hk⟩ := h _ _ hs
    exact ⟨hcs, by rw [hc.2 c hc' hcs, hk]⟩
  · have : m' l = m l := hc.1 l (fun c hc' e => hl ⟨c, hc', e⟩)
    rw [this]; exact h _ _ hs

theorem lookup_zip_of_nodup {ps xs : List Nat} {p x : Nat} (hn : ps.Nodup)
    (h : (p, x) ∈ ps.zip xs) : (ps.zip xs).lookup p = some x := by
  induction ps generalizing xs with
  | nil => simp at h
  | cons q ps ih =>
    cases xs with
    | nil => simp at h
    | cons y xs =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rw [List.nodup_cons] at hn
      simp only [List.zip_cons_cons, List.lookup_cons]
      rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · have hpq : p ≠ q := fun e => hn.1 (e ▸ (List.of_mem_zip h).1)
        have hb : (p == q) = false := by simp [hpq]
        simp only [hb]
        exact ih hn.2 h

theorem lookup_zip_none {ps xs : List Nat} {u : Nat} (h : u ∉ ps) :
    (ps.zip xs).lookup u = none := by
  induction ps generalizing xs with
  | nil => simp
  | cons q ps ih =>
    cases xs with
    | nil => simp
    | cons y xs =>
      simp only [List.mem_cons, not_or] at h
      have hb : (u == q) = false := by simp [h.1]
      simp only [List.zip_cons_cons, List.lookup_cons, hb]
      exact ih h.2

theorem Inv_parCopy {a : AState} {m : Loc → V} {ρ r₀} {ps xs : List Nat} (hn : ps.Nodup)
    (h : Inv keep a m ρ r₀) : Inv keep (a.parCopy ps xs) m (parCopyEnv ρ ps xs) r₀ := by
  intro l s hs
  rcases AState.mem_get_parCopy hs with ⟨hs, hn'⟩ | ⟨p, x, hpx, rfl, hx⟩
  · have := h _ _ hs
    cases s with
    | vreg u =>
      have hu : u ∉ ps := fun hu => hn' (List.mem_map.mpr ⟨u, hu, rfl⟩)
      simp only [Holds, parCopyEnv, lookup_zip_none hu] at this ⊢
      exact this
    | entry r => exact this
  · have := h _ _ hx
    simp only [Holds, parCopyEnv, lookup_zip_of_nodup hn hpx] at this ⊢
    exact this

theorem mem_get_entryState {n : Nat} {l : Loc} {s : Sym} (h : s ∈ (entryState n).get l) :
    ∃ r ∈ calleeSaved, l = .reg r ∧ s = .entry r := by
  unfold entryState at h
  suffices ∀ (rs : List Reg) (a : AState), (∀ l s, s ∈ a.get l → ∃ r ∈ calleeSaved, l = .reg r ∧ s = .entry r) →
      (∀ r ∈ rs, r ∈ calleeSaved) →
      s ∈ (rs.foldl (fun a r => a.put (.reg r) [.entry r]) a).get l →
      ∃ r ∈ calleeSaved, l = .reg r ∧ s = .entry r from
    this calleeSaved _ (fun l s hs => by
      obtain ⟨i, _, hs⟩ := AState.mem_get hs
      simp [Array.getD_eq_getD_getElem?] at hs
      rcases h : (Array.replicate n ([] : List Sym))[i]? with _ | xs
      · simp [h] at hs
      · rw [Array.getElem?_replicate] at h
        split at h <;> simp_all) (fun _ h => h) h
  intro rs
  induction rs with
  | nil => intro a ha _ h; exact ha _ _ h
  | cons r rs ih =>
    intro a ha hrs h
    refine ih _ ?_ (fun r' h' => hrs r' (List.mem_cons_of_mem _ h')) h
    intro l s hs
    rcases AState.mem_get_put hs with ⟨e, hs⟩ | ⟨_, hs⟩
    · exact ⟨r, hrs r (List.mem_cons_self), e, by simpa using hs⟩
    · exact ha _ _ hs

theorem Inv_entryState {n : Nat} {m : Loc → V} {ρ : Nat → V} :
    Inv keep (entryState n) m ρ (fun r => m (.reg r)) := by
  intro l s hs
  obtain ⟨r, hr, rfl, rfl⟩ := mem_get_entryState hs
  exact ⟨hr, rfl⟩

end

end Backend.Proof
