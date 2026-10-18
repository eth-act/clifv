import FV.Concurrency.ArmFence
import FV.Concurrency.Witness

/-!
# Non-vacuity for the strengthening and the fence contract (T2f, #304)

* `sbf_contract`/`sbf_not_rc11`: store buffering with SC fences and plain accesses (`x = 1;
  fence(SeqCst); r1 = y ‖ y = 1; fence(SeqCst); r2 = x` with `r1 = r2 = 0`) is consistent for the
  contract of `ClifMM.lean` but not for RC11: the fence axiom of `ClifMM.ConsistentF` is needed.
* `mpf_*`: message passing through fences and relaxed atomics (`x = 1; fence(Release);
  y.store(1, Relaxed) ‖ y.load(Relaxed) == 1; fence(Acquire); r = x`), compiled (`str; dmb ish;
  stlr ‖ ldar; dmb ish; ldr`): every premise of `armv8_to_clifF` holds, so the CLIF execution
  satisfies the contract with fences (`mpf_consistentF`), the Rust execution is RC11-consistent
  (`mpf_rc11`, `strength_sound`) and RC11-race-free through the fences' synchronisation
  (`mpf_raceFree`), hence race-free for the contract (`raceFree_strength`).
* `incX_consistentF`: the two LL/SC increments of `Witness.incX` satisfy the contract with fences.
-/

namespace Concurrency.Witness

open Rel

/-! ## The fence axiom is needed -/

/-- Events: 0 init `x`, 1 init `y` (thread 0); thread 1: 2 `x = 1`, 3 `fence`, 4 `r1 = y`
(reads 1); thread 2: 5 `y = 1`, 6 `fence`, 7 `r2 = x` (reads 0). -/
abbrev sbf : Exec (Fin 8) where
  tid e := ([0, 0, 1, 1, 1, 2, 2, 2] : List Nat).getD e.val 0
  dir e := ([.W, .W, .W, .F, .R, .W, .F, .R] : List Dir).getD e.val .F
  loc e := ([0, 1, 0, 0, 1, 1, 1, 0] : List Nat).getD e.val 0
  po a b := (a.val, b.val) ∈ [(0, 1), (2, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)]
  rf a b := (a.val, b.val) ∈ [(1, 4), (0, 7)]
  co a b := (a.val, b.val) ∈ [(0, 2), (1, 5)]
  rmw _ _ := False

/-- The CLIF kinds: plain accesses and fences. -/
abbrev sbfSK (e : Fin 8) : SKind :=
  ([.naW, .naW, .naW, .fence, .naR, .naW, .fence, .naR] : List SKind).getD e.val .naW

/-- The Rust kinds: plain accesses and `SeqCst` fences. -/
abbrev sbfK (e : Fin 8) : RKind :=
  ([.naW, .naW, .naW, .F .sc, .naR, .naW, .F .sc, .naR] : List RKind).getD e.val .naW

theorem sbf_wf : sbf.Wf := by
  constructor <;> decide

set_option synthInstance.maxSize 4096 in
/-- **The store-buffering outcome is consistent for the contract without fence semantics.** -/
theorem sbf_contract : ClifMM.Consistent sbf sbfSK where
  coherence a b h he := by
    -- no atomics: `hb` is `po`
    have hnw : ∀ x : Fin 8, sbfSK x ≠ .scW := by decide
    have hpo : sbf.po a b := by
      refine plus_of_trans sbf_wf.po_trans (plus_mono ?_ h)
      rintro x y (h | ⟨hx, -, -⟩)
      · exact h
      · exact absurd hx (hnw x)
    rcases he with rfl | he
    · exact sbf_wf.po_irrefl _ hpo
    · have hs := sbf_wf.eco_shape he
      have key : ∀ a b : Fin 8, sbf.po a b → Exec.Wf.EcoShape sbf b a → False := by
        unfold Exec.Wf.EcoShape Exec.fr; decide
      exact key a b hpo hs
  atomicity _ _ h := h.elim
  sc a h := by
    obtain ⟨c, ⟨hc, -⟩, -⟩ := plus_head h
    have : ∀ x : Fin 8, ¬ ClifMM.At sbfSK x := by unfold ClifMM.At; decide
    exact this a hc

/-- **It is not RC11-consistent**: the SC fences are `psc`-ordered both ways. -/
theorem sbf_not_rc11 : ¬ RC11.ConsistentNoNTA sbf sbfK := by
  intro hc
  have f36 : RC11.psc sbf sbfK 3 6 :=
    .inr ⟨rfl, rfl, .inr ⟨4, 5, .single (.inl (by decide)), .single (.inr (.inr ⟨1, by decide,
      by decide⟩)), .single (.inl (by decide))⟩⟩
  have f63 : RC11.psc sbf sbfK 6 3 :=
    .inr ⟨rfl, rfl, .inr ⟨7, 2, .single (.inl (by decide)), .single (.inr (.inr ⟨0, by decide,
      by decide⟩)), .single (.inl (by decide))⟩⟩
  exact hc.sc 3 (.tail (.single f36) f63)

/-! ## Message passing through fences and relaxed atomics -/

/-- Events: thread 1: 0 `str x`, 1 `dmb ish`, 2 `stlr y`; thread 2: 3 `ldar y` (reads 2),
4 `dmb ish`, 5 `ldr x` (reads 0). `x` is location 0, `y` location 1. -/
abbrev mpf : Exec (Fin 6) where
  tid e := ([1, 1, 1, 2, 2, 2] : List Nat).getD e.val 0
  dir e := ([.W, .F, .W, .R, .F, .R] : List Dir).getD e.val .F
  loc e := ([0, 0, 1, 1, 0, 0] : List Nat).getD e.val 0
  po a b := (a.val, b.val) ∈ [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]
  rf a b := (a.val, b.val) ∈ [(2, 3), (0, 5)]
  co _ _ := False
  rmw _ _ := False

abbrev mpfAK (e : Fin 6) : AKind :=
  ([.plainW, .dmb, .relW, .acqR, .dmb, .plainR] : List AKind).getD e.val .dmb

abbrev mpfSK (e : Fin 6) : SKind :=
  ([.naW, .fence, .scW, .scR, .fence, .naR] : List SKind).getD e.val .fence

abbrev mpfS (_ : Fin 6) : Prop := True

/-- The Rust kinds: `fence(Release)`, `Relaxed` store and load, `fence(Acquire)`. -/
abbrev mpfK (e : {e : Fin 6 // mpfS e}) : RKind :=
  ([.naW, .F .rel, .W .rlx, .R .rlx, .F .acq, .naR] : List RKind).getD e.1.val .naW

theorem mpf_wf : mpf.Wf := by
  constructor <;> decide

theorem mpf_kind : Armv8.KindOk mpf mpfAK := by
  unfold Armv8.KindOk AKind.dir; decide

set_option synthInstance.maxSize 4096 in
theorem mpf_consistent : Armv8.Consistent mpf mpfAK where
  internal := by
    refine acyclic_of_rank (fun e => e.val) ?_
    simp only [union, Exec.poLoc, Exec.com, Exec.fr]
    decide
  atomic := by
    simp only [Exec.ext, Exec.fr]
    decide
  external := by
    refine acyclic_of_rank (fun e => e.val) ?_
    simp only [Armv8.ob, Armv8.obs, Armv8.bob, Armv8.A, Armv8.L, Exec.ext, Exec.fr]
    decide

theorem mpf_compiled : Mapping.Compiled mpf mpfAK mpfS mpfSK where
  maps := by decide
  rf_src := by decide

/-- **The compiled execution satisfies the contract with fences** (`armv8_to_clifF`). -/
theorem mpf_consistentF : ClifMM.ConsistentF (mpf.restrict mpfS) (Mapping.srcKind mpfSK mpfS) :=
  Mapping.armv8_to_clifF mpf_wf mpf_compiled mpf_kind mpf_consistent (fun _ _ _ _ h => h.elim)

theorem mpfK_strength : (fun e => (mpfK e).strength) = Mapping.srcKind mpfSK mpfS := by
  funext e; obtain ⟨e, ⟨⟩⟩ := e; revert e; decide

/-- **The Rust execution with its weak orderings is RC11-consistent** (`strength_sound`). -/
theorem mpf_rc11 : RC11.ConsistentNoNTA (mpf.restrict mpfS) mpfK := by
  refine RC11.strength_sound (mpf_wf.restrict mpf_compiled.rf_src) (fun _ _ h => h.elim) ?_
  rw [mpfK_strength]; exact mpf_consistentF

set_option synthInstance.maxSize 4096 in
/-- **The data accesses are ordered by RC11's `hb`** through the fences: `x = 1` `po`
`fence(Release)` `sw` `fence(Acquire)` `po` `r = x`. -/
theorem mpf_raceFree : RC11.RaceFree (mpf.restrict mpfS) mpfK := by
  have hsw : RC11.sw (mpf.restrict mpfS) mpfK ⟨1, trivial⟩ ⟨4, trivial⟩ :=
    ⟨⟨.rel, rfl, .inr rfl⟩, ⟨.acq, rfl, .inr rfl⟩, ⟨2, trivial⟩, ⟨2, trivial⟩, ⟨3, trivial⟩,
      .inr ⟨⟨.rel, rfl⟩, show mpf.po 1 2 by decide⟩,
      ⟨show mpf.dir 2 = .W by decide, ⟨2, trivial⟩, .inl rfl, ⟨.rlx, rfl⟩, .refl _⟩,
      show mpf.rf 2 3 by decide, ⟨.rlx, rfl⟩, .inr ⟨⟨.acq, rfl⟩, show mpf.po 3 4 by decide⟩⟩
  have hb05 : RC11.hb (mpf.restrict mpfS) mpfK ⟨0, trivial⟩ ⟨5, trivial⟩ :=
    .tail (.tail (.single (.inl (show (mpf.restrict mpfS).po ⟨0, trivial⟩ ⟨1, trivial⟩ from
      show mpf.po 0 1 by decide))) (.inr hsw))
      (.inl (show (mpf.restrict mpfS).po ⟨4, trivial⟩ ⟨5, trivial⟩ from show mpf.po 4 5 by decide))
  have hpairs : ∀ a b : Fin 6, a ≠ b → mpf.loc a = mpf.loc b → mpf.dir a ≠ .F → mpf.dir b ≠ .F →
      (mpf.dir a = .W ∨ mpf.dir b = .W) → (a.val ≠ 2 ∨ b.val ≠ 3) → (a.val ≠ 3 ∨ b.val ≠ 2) →
      (a.val = 0 ∧ b.val = 5) ∨ (a.val = 5 ∧ b.val = 0) := by
    intro a b; revert a b; decide
  rintro ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩ ⟨hne, hl, ha, hb, hw⟩ hn
  have hne' : a ≠ b := fun h => hne (by subst h; rfl)
  have h23 : a.val ≠ 2 ∨ b.val ≠ 3 := by
    by_cases h1 : a.val = 2
    · by_cases h2 : b.val = 3
      · exfalso; apply hn
        have e1 : a = 2 := Fin.ext h1
        have e2 : b = 3 := Fin.ext h2
        subst e1 e2
        exact ⟨.inr ⟨.rlx, rfl⟩, .inl ⟨.rlx, rfl⟩⟩
      · exact .inr h2
    · exact .inl h1
  have h32 : a.val ≠ 3 ∨ b.val ≠ 2 := by
    by_cases h1 : a.val = 3
    · by_cases h2 : b.val = 2
      · exfalso; apply hn
        have e1 : a = 3 := Fin.ext h1
        have e2 : b = 2 := Fin.ext h2
        subst e1 e2
        exact ⟨.inl ⟨.rlx, rfl⟩, .inr ⟨.rlx, rfl⟩⟩
      · exact .inr h2
    · exact .inl h1
  rcases hpairs a b hne' hl ha hb hw h23 h32 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : a = 0 := Fin.ext h1
    have e2 : b = 5 := Fin.ext h2
    subst e1 e2; exact .inl hb05
  · have e1 : a = 5 := Fin.ext h1
    have e2 : b = 0 := Fin.ext h2
    subst e1 e2; exact .inr hb05

/-- **Race-freedom for the contract follows** (`raceFree_strength`). -/
theorem mpf_contract_raceFree :
    ClifMM.RaceFree (mpf.restrict mpfS) (Mapping.srcKind mpfSK mpfS) := by
  rw [← mpfK_strength]
  exact RC11.raceFree_strength (mpf_wf.restrict mpf_compiled.rf_src) (fun _ _ h => h.elim)
    mpf_raceFree

/-! ## The LL/SC increments -/

theorem incX_consistentF : ClifMM.ConsistentF (incX.restrict incS) (Mapping.srcKind incSK incS) :=
  Mapping.armv8_to_clifF incX_wf incX_compiled incX_kind incX_consistent (by
    intro a b _ _ h
    revert h; revert a b; decide)

end Concurrency.Witness
