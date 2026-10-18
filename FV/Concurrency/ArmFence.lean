import FV.Concurrency.RC11

/-!
# Cranelift's `fence` on Armv8: the contract with fences (T2f, #304)

`Mapping.armv8_to_clifF`: the CLIF execution of an Armv8-consistent compiled execution satisfies
`ClifMM.ConsistentF`, the contract with Cranelift's documented SC fences (RC11's SC axiom with every
atomic and fence `seq_cst`), for the table of `FV/Concurrency/Mapping.lean` (`fence` ↦ `dmb ish`).

* `Armv8.R` = `ob ∪ [dmb]; po ∪ po; [dmb]` is acyclic (`R_acyclic`): `ob` edges into or out of a
  `dmb` are `po` edges, and `po; [dmb]; po ⊆ ob`, so every `dmb` on a cycle can be bypassed;
* RC11's `hb` (every atomic SC) is in the Arm `hbA` (`hbY_hbA`);
* every `psc` edge between SC accesses (`ldar`/`ldaxr`/`stlr`/`stlxr`) and fences (`dmb`) is an
  `R⁺` path (`psc_R`): `po`-runs are absorbed at their acquire/`dmb` start or release/`dmb` end.
-/

namespace Concurrency

open Rel

namespace Armv8

variable {E : Type} {X : Exec E} {k : E → AKind}

/-- `[dmb]; po ∪ po; [dmb]`. -/
def D (X : Exec E) (k : E → AKind) : Rel E := fun a b => X.po a b ∧ (k a = .dmb ∨ k b = .dmb)

/-- `ob ∪ [dmb]; po ∪ po; [dmb]`. -/
def R (X : Exec E) (k : E → AKind) : Rel E := union (ob X k) (D X k)

theorem not_A_of_dmb {e : E} (h : k e = .dmb) : ¬ A k e := by
  rintro (h' | h') <;> rw [h] at h' <;> cases h'

theorem not_L_of_dmb {e : E} (h : k e = .dmb) : ¬ L k e := by
  rintro (h' | h') <;> rw [h] at h' <;> cases h'

/-- `dmb` events are fences (what `KindOk` gives for them). -/
def DmbF (X : Exec E) (k : E → AKind) : Prop := ∀ e, k e = .dmb → X.dir e = .F

theorem KindOk.dmbF (hk : KindOk X k) : DmbF X k := fun e h => by rw [← hk e, h]; rfl

theorem dir_of_dmb (hk : DmbF X k) {e : E} (h : k e = .dmb) : X.dir e = .F := hk e h

/-- An `ob` edge into a `dmb` is a `po` edge. -/
theorem ob_into_dmb (hX : X.Wf) (hk : DmbF X k) {a d : E} (hd : k d = .dmb) (h : ob X k a d) :
    X.po a d := by
  have hF := dir_of_dmb hk hd
  rcases h with (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | h | h
  · exact absurd hF (by rw [(hX.rf_dir _ _ h).2]; decide)
  · exact absurd hF (by rw [(hX.co_dir _ _ h).2]; decide)
  · exact absurd hF (by rw [(hX.fr_dir h).2]; decide)
  · exact absurd hF (by rw [(hX.rmw_dir _ _ h).2]; decide)
  · rcases h with ⟨f, h1, -, h2⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact hX.po_trans _ _ _ h1 h2
    · exact absurd h (not_A_of_dmb hd)
    · exact h
    · exact h

/-- An `ob` edge out of a `dmb` is a `po` edge. -/
theorem ob_out_dmb (hX : X.Wf) (hk : DmbF X k) {d b : E} (hd : k d = .dmb) (h : ob X k d b) :
    X.po d b := by
  have hF := dir_of_dmb hk hd
  rcases h with (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | h | h
  · exact absurd hF (by rw [(hX.rf_dir _ _ h).1]; decide)
  · exact absurd hF (by rw [(hX.co_dir _ _ h).1]; decide)
  · exact absurd hF (by rw [(hX.fr_dir h).1]; decide)
  · exact absurd hF (by rw [(hX.rmw_dir _ _ h).1]; decide)
  · rcases h with ⟨f, h1, -, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hX.po_trans _ _ _ h1 h2
    · exact absurd h (not_L_of_dmb hd)
    · exact absurd h (not_A_of_dmb hd)
    · exact h

/-- The shape of an `R⁺` path by whether its ends are `dmb`s. -/
def RShape (X : Exec E) (k : E → AKind) (a b : E) : Prop :=
  (k a ≠ .dmb ∧ k b ≠ .dmb ∧ Relation.TransGen (ob X k) a b) ∨
  (k a ≠ .dmb ∧ k b = .dmb ∧ ∃ c, k c ≠ .dmb ∧ (c = a ∨ Relation.TransGen (ob X k) a c) ∧ X.po c b) ∨
  (k a = .dmb ∧ k b ≠ .dmb ∧ ∃ c, k c ≠ .dmb ∧ X.po a c ∧ (c = b ∨ Relation.TransGen (ob X k) c b)) ∨
  (k a = .dmb ∧ k b = .dmb ∧ (X.po a b ∨ ∃ c c', k c ≠ .dmb ∧ k c' ≠ .dmb ∧ X.po a c ∧
    (c = c' ∨ Relation.TransGen (ob X k) c c') ∧ X.po c' b))

theorem R_po (hX : X.Wf) (hk : DmbF X k) {a b : E} (h : R X k a b) (hd : k a = .dmb ∨ k b = .dmb) :
    X.po a b := by
  rcases h with h | h
  · rcases hd with hd | hd
    · exact ob_out_dmb hX hk hd h
    · exact ob_into_dmb hX hk hd h
  · exact h.1

theorem rshape_one (hX : X.Wf) (hk : DmbF X k) {a b : E} (h : R X k a b) : RShape X k a b := by
  by_cases ha : k a = .dmb <;> by_cases hb : k b = .dmb
  · exact .inr (.inr (.inr ⟨ha, hb, .inl (R_po hX hk h (.inl ha))⟩))
  · exact .inr (.inr (.inl ⟨ha, hb, b, hb, R_po hX hk h (.inl ha), .inl rfl⟩))
  · exact .inr (.inl ⟨ha, hb, a, ha, .inl rfl, R_po hX hk h (.inr hb)⟩)
  · rcases h with h | ⟨-, h⟩
    · exact .inl ⟨ha, hb, .single h⟩
    · exact absurd h (by rintro (h | h) <;> contradiction)

theorem rshape_tail (hX : X.Wf) (hk : DmbF X k) {a b e : E} (h1 : RShape X k a b)
    (h2 : R X k b e) : RShape X k a e := by
  rcases h1 with ⟨ha, hb, hab⟩ | ⟨ha, hb, c, hc, hac, hcb⟩ | ⟨ha, hb, c, hc, hac, hcb⟩ |
    ⟨ha, hb, hab⟩
  · -- `b` is not a `dmb`
    by_cases he : k e = .dmb
    · exact .inr (.inl ⟨ha, he, b, hb, .inr hab, R_po hX hk h2 (.inr he)⟩)
    · rcases h2 with h2 | ⟨-, h2⟩
      · exact .inl ⟨ha, he, hab.tail h2⟩
      · exact absurd h2 (by rintro (h | h) <;> contradiction)
  · -- `b` is a `dmb`: `c po b po e`
    have hbe := R_po hX hk h2 (.inl hb)
    by_cases he : k e = .dmb
    · exact .inr (.inl ⟨ha, he, c, hc, hac, hX.po_trans _ _ _ hcb hbe⟩)
    · have hce : ob X k c e := ob_dmb hcb hb hbe
      rcases hac with rfl | hac
      · exact .inl ⟨ha, he, .single hce⟩
      · exact .inl ⟨ha, he, hac.tail hce⟩
  · by_cases he : k e = .dmb
    · exact .inr (.inr (.inr ⟨ha, he, .inr ⟨c, b, hc, hb, hac, hcb, R_po hX hk h2 (.inr he)⟩⟩))
    · rcases h2 with h2 | ⟨-, h2⟩
      · refine .inr (.inr (.inl ⟨ha, he, c, hc, hac, .inr ?_⟩))
        rcases hcb with rfl | hcb
        · exact .single h2
        · exact hcb.tail h2
      · exact absurd h2 (by rintro (h | h) <;> contradiction)
  · have hbe := R_po hX hk h2 (.inl hb)
    by_cases he : k e = .dmb
    · rcases hab with hab | ⟨c, c', hc, hc', hac, hcc, hcb⟩
      · exact .inr (.inr (.inr ⟨ha, he, .inl (hX.po_trans _ _ _ hab hbe)⟩))
      · exact .inr (.inr (.inr ⟨ha, he, .inr ⟨c, c', hc, hc', hac, hcc,
          hX.po_trans _ _ _ hcb hbe⟩⟩))
    · rcases hab with hab | ⟨c, c', hc, hc', hac, hcc, hcb⟩
      · exact .inr (.inr (.inl ⟨ha, he, e, he, hX.po_trans _ _ _ hab hbe, .inl rfl⟩))
      · have hce : ob X k c' e := ob_dmb hcb hb hbe
        refine .inr (.inr (.inl ⟨ha, he, c, hc, hac, .inr ?_⟩))
        rcases hcc with rfl | hcc
        · exact .single hce
        · exact hcc.tail hce

/-- **`ob ∪ [dmb]; po ∪ po; [dmb]` is acyclic.** -/
theorem R_acyclic (hX : X.Wf) (hk : DmbF X k) (hc : Consistent X k) : Acyclic (R X k) := by
  have gen : ∀ {a b}, Relation.TransGen (R X k) a b → RShape X k a b := by
    intro a b h
    induction h with
    | single h => exact rshape_one hX hk h
    | tail _ h2 ih => exact rshape_tail hX hk ih h2
  intro a ha
  have hs : RShape X k a a := gen ha
  rcases hs with ⟨-, -, h⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨ha, -, h | ⟨c, c', -, -, hac, hcc, hca⟩⟩
  · exact hc.external a h
  · exact h1 h2
  · exact h2 h1
  · exact hX.po_irrefl a h
  · have hcc' : ob X k c' c := ob_dmb hca ha hac
    rcases hcc with rfl | hcc
    · exact hc.external c (.single hcc')
    · exact hc.external c (hcc.tail hcc')

/-! ## `psc` paths on Arm -/

section paths

variable (X k)

/-- Anchors of `po`-runs on the left: acquires and `dmb`s. -/
def Anch (e : E) : Prop := A k e ∨ k e = .dmb

/-- The `psc` nodes: acquires, releases, `dmb`s. -/
def Endpt (e : E) : Prop := A k e ∨ L k e ∨ k e = .dmb

/-- The shape of the Arm happens-before (`hb_shape`). -/
def HbS (a b : E) : Prop :=
  X.po a b ∨ ∃ l a', opt X.po a l ∧ L k l ∧ Relation.TransGen (ob X k) l a' ∧ A k a' ∧ opt X.po a' b

/-- From `u`: a step, then a pending `po`-run from an anchor (or none). -/
def LNA (u c : E) : Prop :=
  ∃ m, (m = u ∨ Relation.TransGen (R X k) u m) ∧ Anch k m ∧ opt X.po m c ∧ (m = u → X.po m c)

/-- The shape of `scb` on Arm. -/
def SNF (x y : E) : Prop :=
  X.po x y ∨ ob X k x y ∨
    ∃ l a', opt X.po x l ∧ L k l ∧ Relation.TransGen (ob X k) l a' ∧ A k a' ∧ opt X.po a' y

end paths

section pathlemmas

variable (hX : X.Wf) (hk : DmbF X k)
include hX

omit hX in
theorem R_of_po_anch {a b : E} (ha : Anch k a) (h : X.po a b) : R X k a b := by
  rcases ha with ha | ha
  · exact .inl (ob_acq ha h)
  · exact .inr ⟨h, .inl ha⟩

omit hX in
theorem R_of_po_rel {a b : E} (hb : L k b ∨ k b = .dmb) (h : X.po a b) : R X k a b := by
  rcases hb with hb | hb
  · exact .inl (ob_rel h hb)
  · exact .inr ⟨h, .inr hb⟩

omit hX in
theorem obs_R {x y : E} (h : Relation.TransGen (ob X k) x y) : Relation.TransGen (R X k) x y :=
  plus_mono (fun _ _ h => .inl h) h

theorem hbS_of_hbA (hc : Consistent X k) {a b : E} (h : hbA X k a b) : HbS X k a b := by
  rcases hb_shape hX hc h with h | ⟨l, x, h1, h2, h3, h4, h5⟩
  · exact .inl h
  · exact .inr ⟨l, x, h1, h2, h4, h3, h5⟩

omit hX in
/-- The `ob` part of `hb` from a run: `x po? l ob⁺ a'` is an `R⁺` path. -/
theorem R_lob {x l a' : E} (h1 : opt X.po x l) (hl : L k l) (h2 : Relation.TransGen (ob X k) l a') :
    Relation.TransGen (R X k) x a' := by
  rcases h1 with rfl | h1
  · exact obs_R h2
  · exact (Relation.TransGen.single (R_of_po_rel (.inl hl) h1)).trans (obs_R h2)

omit hX in
theorem lna_of_hb {u c : E} (hu : k u = .dmb) (h : HbS X k u c) : LNA X k u c := by
  rcases h with h | ⟨l, a', h1, hl, h2, ha, h3⟩
  · exact ⟨u, .inl rfl, .inr hu, .inr h, fun _ => h⟩
  · have hla : Relation.TransGen (R X k) u a' := by
      rcases h1 with rfl | h1
      · exact absurd hl (not_L_of_dmb hu)
      · exact (Relation.TransGen.single (R_of_po_anch (.inr hu) h1)).trans (obs_R h2)
    exact ⟨a', .inr hla, .inl ha, h3, fun e => by subst e; exact absurd ha (not_A_of_dmb hu)⟩

omit hX in
theorem lna_disch {u c : E} (h : LNA X k u c) : u = c ∨ Relation.TransGen (R X k) u c := by
  obtain ⟨m, hm, ha, hmc, _⟩ := h
  rcases hmc with rfl | hmc
  · exact hm.elim (fun h => .inl h.symm) .inr
  · rcases hm with rfl | hm
    · exact .inr (.single (R_of_po_anch ha hmc))
    · exact .inr (hm.tail (R_of_po_anch ha hmc))

omit hX in
theorem lna_ob {u c y : E} (h : LNA X k u c) (h2 : ob X k c y) : Relation.TransGen (R X k) u y := by
  rcases lna_disch h with rfl | h
  · exact .single (.inl h2)
  · exact h.tail (.inl h2)

theorem lna_po {u c y : E} (h : LNA X k u c) (h2 : X.po c y) : LNA X k u y := by
  obtain ⟨m, hm, ha, hmc, hne⟩ := h
  have hmy : X.po m y := by
    rcases hmc with rfl | hmc
    · exact h2
    · exact hX.po_trans _ _ _ hmc h2
  exact ⟨m, hm, ha, .inr hmy, fun _ => hmy⟩

theorem lna_absorb {u c v : E} (h : LNA X k u c) (hd : Relation.TransGen (R X k) c v)
    (habs : ∀ m, X.po m c → Relation.TransGen (R X k) m v) : Relation.TransGen (R X k) u v := by
  obtain ⟨m, hm, ha, hmc, hne⟩ := h
  rcases hmc with rfl | hmc
  · rcases hm with rfl | hm
    · exact absurd (hne rfl) (hX.po_irrefl _)
    · exact hm.trans hd
  · rcases hm with rfl | hm
    · exact habs _ hmc
    · exact hm.trans (habs _ hmc)

/-- The right part of a `psc_F` path or of a `psc_base` path ending at a `dmb`. -/
theorem rn_dmb {y v : E} (hv : k v = .dmb) (h : HbS X k y v) :
    Relation.TransGen (R X k) y v ∧ ∀ m, X.po m y → Relation.TransGen (R X k) m v := by
  rcases h with h | ⟨l, a', h1, hl, h2, ha, h3⟩
  · exact ⟨.single (R_of_po_rel (.inr hv) h), fun m hm =>
      .single (R_of_po_rel (.inr hv) (hX.po_trans _ _ _ hm h))⟩
  · have hav : Relation.TransGen (R X k) a' v := by
      rcases h3 with rfl | h3
      · exact absurd ha (not_A_of_dmb hv)
      · exact .single (R_of_po_anch (.inl ha) h3)
    refine ⟨(R_lob h1 hl h2).trans hav, fun m hm => ?_⟩
    have hml : X.po m l := by
      rcases h1 with rfl | h1
      · exact hm
      · exact hX.po_trans _ _ _ hm h1
    exact (R_lob (.inr hml) hl h2).trans hav

/-- The tail of a `psc_base` path: `scb` and the right part. -/
theorem tail_of {x y v : E} (hs : SNF X k x y)
    (hr : (y = v ∧ Endpt k v) ∨ (k v = .dmb ∧ HbS X k y v)) :
    Relation.TransGen (R X k) x v ∨ (X.po x v ∧ A k v) := by
  rcases hr with ⟨rfl, hv⟩ | ⟨hv, hr⟩
  · rcases hs with hs | hs | ⟨l, a', h1, hl, h2, ha, h3⟩
    · rcases hv with hv | hv | hv
      · exact .inr ⟨hs, hv⟩
      · exact .inl (.single (R_of_po_rel (.inl hv) hs))
      · exact .inl (.single (R_of_po_rel (.inr hv) hs))
    · exact .inl (.single (.inl hs))
    · rcases h3 with rfl | h3
      · exact .inl (R_lob h1 hl h2)
      · exact .inl ((R_lob h1 hl h2).tail (R_of_po_anch (.inl ha) h3))
  · obtain ⟨hd, habs⟩ := rn_dmb hX hv hr
    rcases hs with hs | hs | ⟨l, a', h1, hl, h2, ha, h3⟩
    · exact .inl (habs _ hs)
    · exact .inl ((Relation.TransGen.single (.inl hs)).trans hd)
    · rcases h3 with rfl | h3
      · exact .inl ((R_lob h1 hl h2).trans hd)
      · exact .inl ((R_lob h1 hl h2).trans
          ((Relation.TransGen.single (R_of_po_anch (.inl ha) h3)).trans hd))

theorem combine {u x v : E} (hl : (x = u ∧ Endpt k u) ∨ LNA X k u x)
    (ht : Relation.TransGen (R X k) x v ∨ (X.po x v ∧ A k v)) : Relation.TransGen (R X k) u v := by
  rcases hl with ⟨rfl, hu⟩ | hl
  · rcases ht with ht | ⟨ht, hv⟩
    · exact ht
    · rcases hu with hu | hu | hu
      · exact .single (.inl (ob_acq hu ht))
      · exact .single (.inl (ob_rel_acq hu ht hv))
      · exact .single (.inr ⟨ht, .inl hu⟩)
  · rcases ht with ht | ⟨ht, hv⟩
    · rcases lna_disch hl with rfl | hl'
      · exact ht
      · exact hl'.trans ht
    · obtain ⟨m, hm, ha, hmc, hne⟩ := hl
      have hmv : X.po m v := by
        rcases hmc with rfl | hmc
        · exact ht
        · exact hX.po_trans _ _ _ hmc ht
      rcases hm with rfl | hm
      · exact .single (R_of_po_anch ha hmv)
      · exact hm.tail (R_of_po_anch ha hmv)

end pathlemmas

end Armv8

/-! ## The CLIF execution of compiled code -/

theorem SKind.strength_liftSC (s : SKind) : s.liftSC.strength = s := by cases s <;> rfl

namespace Mapping

variable {E EY : Type} {X : Exec E} {ak : E → AKind} {Y : Exec EY} {sk : EY → SKind}

/-- **A CLIF execution `Y` is mapped into the Arm execution `X` by `ψ`**: `po`, `rf`, `co` are
preserved, atomics and fences have the table's kinds, and CLIF atomic updates are atomics. -/
structure Hom (Y : Exec EY) (sk : EY → SKind) (X : Exec E) (ak : E → AKind) (ψ : EY → E) : Prop where
  po : ∀ a b, Y.po a b → X.po (ψ a) (ψ b)
  rf : ∀ a b, Y.rf a b → X.rf (ψ a) (ψ b)
  co : ∀ a b, Y.co a b → X.co (ψ a) (ψ b)
  kind : ∀ e, (sk e = .scR ∨ sk e = .scW ∨ sk e = .fence) → Maps (sk e) (ak (ψ e))
  rmw : ∀ a b, Y.rmw a b → sk a = .scR ∧ sk b = .scW

variable {ψ : EY → E} (hX : X.Wf) (hY : Y.Wf) (hh : Hom Y sk X ak ψ)
include hX hY hh

omit hX hY in
theorem Hom.com {a b : EY} (h : Y.com a b) : X.com (ψ a) (ψ b) := by
  rcases h with h | h | ⟨w, h1, h2⟩
  · exact .inl (hh.rf _ _ h)
  · exact .inr (.inl (hh.co _ _ h))
  · exact .inr (.inr ⟨ψ w, hh.rf _ _ h1, hh.co _ _ h2⟩)

omit hX hY in
theorem Hom.esc_AL {u : EY} (h : RC11.Esc (fun e => (sk e).liftSC) u) :
    Armv8.A ak (ψ u) ∨ Armv8.L ak (ψ u) := by
  rcases h with h | h
  · have : sk u = .scR := by cases hs : sk u <;> simp [hs, SKind.liftSC] at h ⊢
    have hm := hh.kind u (.inl this); rw [this] at hm; exact .inl hm
  · have : sk u = .scW := by cases hs : sk u <;> simp [hs, SKind.liftSC] at h ⊢
    have hm := hh.kind u (.inr (.inl this)); rw [this] at hm; exact .inr hm

omit hX hY in
theorem Hom.fsc_dmb {u : EY} (h : RC11.Fsc (fun e => (sk e).liftSC) u) : ak (ψ u) = .dmb := by
  have : sk u = .fence := by
    simp only [RC11.Fsc] at h
    cases hs : sk u <;> simp [hs, SKind.liftSC] at h ⊢
  have hm := hh.kind u (.inr (.inr this)); rw [this] at hm; exact hm

omit hX in
/-- RC11's `hb` (atomics and fences `seq_cst`) is in the Arm `hbA`. -/
theorem Hom.hb {a b : EY} (h : RC11.hb Y (fun e => (sk e).liftSC) a b) :
    Armv8.hbA X ak (ψ a) (ψ b) := by
  have hra : RC11.RmwAt Y (fun e => (sk e).liftSC) := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := hh.rmw x y hxy
    exact ⟨⟨.sc, by simp [h1, SKind.liftSC]⟩, ⟨.sc, by simp [h2, SKind.liftSC]⟩⟩
  have h' := RC11.hb_strength hY hra h
  simp only [SKind.strength_liftSC] at h'
  refine plus_map ψ ?_ h'
  rintro x y (h | ⟨hx, hrf, hy⟩)
  · exact .inl (hh.po _ _ h)
  · have hx' : sk x = .scW := hx
    have hy' : sk y = .scR := hy
    have m1 := hh.kind x (.inr (.inl hx'))
    have m2 := hh.kind y (.inl hy')
    rw [hx'] at m1; rw [hy'] at m2
    exact .inr ⟨m1, hh.rf _ _ hrf, m2⟩

/-- `scb` of the CLIF execution has the Arm shape `SNF`. -/
theorem Hom.scb_snf (hc : Armv8.Consistent X ak) {x y : EY}
    (h : RC11.scb Y (fun e => (sk e).liftSC) x y) : Armv8.SNF X ak (ψ x) (ψ y) := by
  have hbS : ∀ {a b : EY}, RC11.hb Y (fun e => (sk e).liftSC) a b → Armv8.HbS X ak (ψ a) (ψ b) :=
    fun h => Armv8.hbS_of_hbA hX hc (hh.hb hY h)
  have hcom : ∀ {a b : EY}, Y.com a b → Armv8.ob X ak (ψ a) (ψ b) ∨ X.po (ψ a) (ψ b) :=
    fun h => Armv8.com_ob_or_po hX hc (hh.com h)
  rcases h with h | ⟨c, d, h1, -, h2, h3, -⟩ | ⟨h, -⟩ | h | h
  · exact .inl (hh.po _ _ h)
  · have h1 := hh.po _ _ h1
    have h3 := hh.po _ _ h3
    rcases hbS h2 with h2 | ⟨l, a', hl1, hl, hob, ha, ha2⟩
    · exact .inl (hX.po_trans _ _ _ (hX.po_trans _ _ _ h1 h2) h3)
    · refine .inr (.inr ⟨l, a', .inr ?_, hl, hob, ha, .inr ?_⟩)
      · rcases hl1 with e | hl1
        · rw [← e]; exact h1
        · exact hX.po_trans _ _ _ h1 hl1
      · rcases ha2 with e | ha2
        · rw [e]; exact h3
        · exact hX.po_trans _ _ _ ha2 h3
  · rcases hbS h with h | ⟨l, a', hl1, hl, hob, ha, ha2⟩
    · exact .inl h
    · exact .inr (.inr ⟨l, a', hl1, hl, hob, ha, ha2⟩)
  · rcases hcom (.inr (.inl h)) with h | h
    · exact .inr (.inl h)
    · exact .inl h
  · rcases hcom (.inr (.inr h)) with h | h
    · exact .inr (.inl h)
    · exact .inl h

/-- **Every `psc` edge of the CLIF execution is an `R⁺` path on Arm.** -/
theorem Hom.psc_R (hc : Armv8.Consistent X ak) {u v : EY}
    (h : RC11.psc Y (fun e => (sk e).liftSC) u v) :
    Relation.TransGen (Armv8.R X ak) (ψ u) (ψ v) := by
  have hbS : ∀ {a b : EY}, RC11.hb Y (fun e => (sk e).liftSC) a b → Armv8.HbS X ak (ψ a) (ψ b) :=
    fun h => Armv8.hbS_of_hbA hX hc (hh.hb hY h)
  rcases h with ⟨x, y, hl, hs, hr⟩ | ⟨hu, hv, hh'⟩
  · have hl' : (ψ x = ψ u ∧ Armv8.Endpt ak (ψ u)) ∨ Armv8.LNA X ak (ψ u) (ψ x) := by
      rcases hl with ⟨rfl, he⟩ | ⟨hf, rfl | hhb⟩
      · exact .inl ⟨rfl, (hh.esc_AL he).elim .inl (fun h => .inr (.inl h))⟩
      · exact .inl ⟨rfl, .inr (.inr (hh.fsc_dmb hf))⟩
      · exact .inr (Armv8.lna_of_hb (hh.fsc_dmb hf) (hbS hhb))
    have hr' : (ψ y = ψ v ∧ Armv8.Endpt ak (ψ v)) ∨ (ak (ψ v) = .dmb ∧ Armv8.HbS X ak (ψ y) (ψ v)) := by
      rcases hr with ⟨rfl, he⟩ | ⟨hf, rfl | hhb⟩
      · exact .inl ⟨rfl, (hh.esc_AL he).elim .inl (fun h => .inr (.inl h))⟩
      · exact .inl ⟨rfl, .inr (.inr (hh.fsc_dmb hf))⟩
      · exact .inr ⟨hh.fsc_dmb hf, hbS hhb⟩
    exact Armv8.combine hX hl' (Armv8.tail_of hX (hh.scb_snf hX hY hc hs) hr')
  · have hu' := hh.fsc_dmb hu
    have hv' := hh.fsc_dmb hv
    rcases hh' with hh' | ⟨c, d, h1, h2, h3⟩
    · exact (Armv8.rn_dmb hX hv' (hbS hh')).1
    · have hl := Armv8.lna_of_hb hu' (hbS h1)
      obtain ⟨hd, habs⟩ := Armv8.rn_dmb hX hv' (hbS h3)
      have one : ∀ {a b : EY}, Y.com a b → Armv8.ob X ak (ψ a) (ψ b) ∨ X.po (ψ a) (ψ b) :=
        fun h => Armv8.com_ob_or_po hX hc (hh.com h)
      have fin1 : ∀ {m : E}, Armv8.LNA X ak (ψ u) m → (Armv8.ob X ak m (ψ d) ∨ X.po m (ψ d)) →
          Relation.TransGen (Armv8.R X ak) (ψ u) (ψ v) := by
        intro m hlm hmd
        rcases hmd with hmd | hmd
        · exact (Armv8.lna_ob hlm hmd).trans hd
        · exact Armv8.lna_absorb hX (Armv8.lna_po hX hlm hmd) hd habs
      have fin2 : ∀ {m : EY}, Y.com c m → Y.com m d →
          Relation.TransGen (Armv8.R X ak) (ψ u) (ψ v) := by
        intro m e1 e2
        rcases one e1 with e1 | e1
        · have hum := Armv8.lna_ob hl e1
          rcases one e2 with e2 | e2
          · exact (hum.tail (.inl e2)).trans hd
          · exact hum.trans (habs _ e2)
        · exact fin1 (Armv8.lna_po hX hl e1) (one e2)
      rcases hY.eco_shape h2 with e | e | e | ⟨m, e1, e2⟩ | ⟨m, e1, e2⟩
      · exact fin1 hl (one (.inl e))
      · exact fin1 hl (one (.inr (.inl e)))
      · exact fin1 hl (one (.inr (.inr e)))
      · exact fin2 (.inr (.inl e1)) (.inl e2)
      · exact fin2 (.inr (.inr e1)) (.inl e2)

/-- **`psc` of a CLIF execution mapped into an Armv8-consistent execution is acyclic.** -/
theorem Hom.psc_acyclic (hk : Armv8.DmbF X ak) (hc : Armv8.Consistent X ak) :
    Acyclic (RC11.psc Y (fun e => (sk e).liftSC)) := by
  intro a ha
  have key : ∀ {x y : EY}, Relation.TransGen (RC11.psc Y (fun e => (sk e).liftSC)) x y →
      Relation.TransGen (Armv8.R X ak) (ψ x) (ψ y) := by
    intro x y h
    induction h with
    | single h => exact hh.psc_R hX hY hc h
    | tail _ h2 ih => exact ih.trans (hh.psc_R hX hY hc h2)
  exact Armv8.R_acyclic hX hk hc (ψ a) (key ha)

end Mapping

/-- CLIF atomic updates are atomics. -/
def Mapping.RmwSc {E : Type} (X : Exec E) (S : E → Prop) (sk : E → SKind) : Prop :=
  ∀ a b, S a → S b → X.rmw a b → sk a = .scR ∧ sk b = .scW

/-- **Cranelift's `fence` ↦ `dmb ish` is sound for its SC semantics**: the CLIF execution of an
Armv8-consistent compiled execution satisfies the contract with fences, `ClifMM.ConsistentF`
(CLIF atomic updates are atomics: `RmwSc`). -/
theorem Mapping.armv8_to_clifF {E : Type} {X : Exec E} {ak : E → AKind} {S : E → Prop}
    {sk : E → SKind} (hX : X.Wf) (hm : Compiled X ak S sk) (hk : Armv8.KindOk X ak)
    (hc : Armv8.Consistent X ak) (hrmw : RmwSc X S sk) :
    ClifMM.ConsistentF (X.restrict S) (srcKind sk S) where
  toConsistent := armv8_to_clif hX hc hm
  psc := by
    have hh : Hom (X.restrict S) (srcKind sk S) X ak Subtype.val :=
      ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun e _ => hm.maps e.1 e.2,
        fun a b h => hrmw a.1 b.1 a.2 b.2 h⟩
    exact hh.psc_acyclic hX (hX.restrict hm.rf_src) hk.dmbF hc


end Concurrency
