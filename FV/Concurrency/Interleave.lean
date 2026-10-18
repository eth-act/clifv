import FV.Concurrency.Mapping

/-!
# SC executions are interleavings (T2, #38)

A finite sequentially consistent execution has a rank (its position in an interleaving) that
increases along `po ∪ com`: in any total order refining the rank, every read reads the latest
write to its location before it, and no write to the location of an atomic update falls between
its read and its write. This is the interface to the sequential semantics: each thread's slice of
the interleaving runs against a memory where the other threads' writes happen between its steps,
which is what `Clif.run` and `E2E.backend_correct_final` describe for one thread. Composed with the
mapping: `Mapping.armv8_interleaving`. Plan: `docs/plans/atomics.md`.
-/

namespace Concurrency

open Rel

theorem countP_lt {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
      l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | y :: ys, hpq, ⟨x, hx, hqx, hpx⟩ => by
    rw [List.countP_cons, List.countP_cons]
    have hpq' : ∀ z ∈ ys, p z = true → q z = true :=
      fun z hz => hpq z (List.mem_cons_of_mem _ hz)
    have hy := hpq y List.mem_cons_self
    rcases List.mem_cons.mp hx with rfl | hx
    · have := List.countP_mono_left hpq'
      simp [hqx, hpx]; omega
    · have := countP_lt hpq' ⟨x, hx, hqx, hpx⟩
      by_cases h1 : p y = true
      · simp [h1, hy h1]; omega
      · simp only [Bool.not_eq_true] at h1
        by_cases h2 : q y = true <;> simp [h1, h2] <;> omega

namespace Exec

variable {E : Type} {X : Exec E}

open Classical in
/-- **A finite acyclic relation has an increasing rank**: the number of events before an event in
the transitive closure. -/
theorem rank_of_acyclic {r : Rel E} (hr : Acyclic r) (evs : List E) (hall : ∀ e, e ∈ evs) :
    ∃ rank : E → Nat, ∀ a b, r a b → rank a < rank b := by
  refine ⟨fun e => evs.countP (fun y => decide (Relation.TransGen r y e)), ?_⟩
  intro a b hab
  refine countP_lt ?_ ⟨a, hall a, ?_, ?_⟩
  · intro y _ hy
    simp only [decide_eq_true_eq] at hy ⊢
    exact hy.tail hab
  · simp only [decide_eq_true_eq]; exact .single hab
  · simp only [decide_eq_false_iff_not]; exact hr a

/-- **Theorem 5: a finite SC execution is an interleaving.** There is a rank increasing along
`po ∪ com` in which every read reads from the latest same-location write before it, and no
same-location write falls between the read and the write of an atomic update (given atomicity,
`rmw ∩ (fr; co) = ∅`). -/
theorem sc_interleaving (hX : X.Wf) (hsc : X.SC) (evs : List E) (hall : ∀ e, e ∈ evs)
    (hat : ∀ a b, X.rmw a b → ¬ ∃ c, X.fr a c ∧ X.co c b) :
    ∃ rank : E → Nat,
      (∀ a b, union X.po X.com a b → rank a < rank b) ∧
      (∀ w r, X.rf w r → ∀ w', X.dir w' = .W → X.loc w' = X.loc r → w' ≠ w →
        rank w' < rank w ∨ rank r < rank w') ∧
      (∀ r w, X.rmw r w → ∀ w', X.dir w' = .W → X.loc w' = X.loc r → w' ≠ w →
        rank w' < rank r ∨ rank w < rank w') := by
  obtain ⟨rank, hrank⟩ := rank_of_acyclic hsc evs hall
  have hco : ∀ {a b}, X.co a b → rank a < rank b := fun h => hrank _ _ (.inr (.inr (.inl h)))
  have hfr : ∀ {a b}, X.fr a b → rank a < rank b := fun h => hrank _ _ (.inr (.inr (.inr h)))
  have hrf : ∀ {a b}, X.rf a b → rank a < rank b := fun h => hrank _ _ (.inr (.inl h))
  refine ⟨rank, hrank, ?_, ?_⟩
  · intro w r h w' hw' hl hne
    rcases hX.co_total w' w hw' (hX.rf_dir _ _ h).1 (hl.trans (hX.rf_loc _ _ h).symm) hne
      with h' | h'
    · exact .inl (hco h')
    · exact .inr (hfr ⟨w, h, h'⟩)
  · intro r w h w' hw' hl hne
    obtain ⟨w0, h0⟩ := hX.rf_total r (hX.rmw_dir _ _ h).1
    by_cases h0' : w' = w0
    · subst h0'; exact .inl (hrf h0)
    · rcases hX.co_total w' w0 hw' (hX.rf_dir _ _ h0).1 (hl.trans (hX.rf_loc _ _ h0).symm) h0'
        with h' | h'
      · exact .inl (Nat.lt_trans (hco h') (hrf h0))
      · have hfr' : X.fr r w' := ⟨w0, h0, h'⟩
        rcases hX.co_total w' w hw' (hX.rmw_dir _ _ h).2 (hl.trans (hX.rmw_loc _ _ h)) hne
          with h'' | h''
        · exact absurd ⟨w', hfr', h''⟩ (hat r w h)
        · exact .inr (hco h'')

end Exec

namespace Mapping

variable {E : Type} {X : Exec E} {ak : E → AKind} {S : E → Prop} {sk : E → SKind}

/-- **Theorems 4 + 5: a finite race-free CLIF execution whose compiled image is Armv8-consistent
is an interleaving** in which every read sees the latest write and atomic updates are
indivisible. -/
theorem armv8_interleaving (hX : X.Wf) (hc : Armv8.Consistent X ak)
    (hm : Compiled X ak S sk) (hr : ClifMM.RaceFree (X.restrict S) (srcKind sk S))
    (evs : List {e // S e}) (hall : ∀ e, e ∈ evs) :
    ∃ rank : {e // S e} → Nat,
      (∀ a b, union (X.restrict S).po (X.restrict S).com a b → rank a < rank b) ∧
      (∀ w r, (X.restrict S).rf w r → ∀ w', (X.restrict S).dir w' = .W →
        (X.restrict S).loc w' = (X.restrict S).loc r → w' ≠ w →
        rank w' < rank w ∨ rank r < rank w') ∧
      (∀ r w, (X.restrict S).rmw r w → ∀ w', (X.restrict S).dir w' = .W →
        (X.restrict S).loc w' = (X.restrict S).loc r → w' ≠ w →
        rank w' < rank r ∨ rank w < rank w') :=
  Exec.sc_interleaving (hX.restrict hm.rf_src) (armv8_drf_sc hX hc hm hr) evs hall
    (armv8_to_clif hX hc hm).atomicity

end Mapping

end Concurrency
