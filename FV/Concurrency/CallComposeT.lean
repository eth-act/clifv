import FV.Concurrency.CallCompose
import FV.Concurrency.PrivCohT
import FV.Concurrency.ClifThreadI

/-!
# Calls with time-varying private sets (#473, (iv))

The linking induction of `CallCompose` on `PrivCohT.RefinesT` refinements of `CStepS` runs (CLIF
threads with stack slots, `ClifThreadI.CStepI` with the mask carried in the thread state's bytes):

* `RefinesC.app`, **`RefinesT.app`**: refinements of consecutive Arm segments compose; the
  private sets concatenate (`catP`), the locations dirty at the end of the first segment (`Clean`
  fails: private at the start, or last written by an unmatched write, without a source write
  since) must be private at the start of the second;
* `CStepS`, `CRunS`: `CStepI` on thread states whose bytes encode the mask (`maskOf`: `none` is
  masked);
* `RealizedT env p Bnd ls k c c' D D'`: the first `k` labels of `ls` realize a `CRunS` run from `c`
  to `c'`, with private sets inside the thread's bound `Bnd`, the locations dirty at the start
  `D`, at the end within `D'`; `RealizedT.zero`, `RealizedT.trans`;
* `FunRealG`, `SegOkG`, **`link_composeG`**: `CallCompose.link_compose` for any realization
  relation with `zero`, `le` and `trans`;
* **`realizes_linkedT`**: `CallCompose.realizes_linked` for threads given by `RealizedT`
  contracts, through `PrivCohT.realizes_of_threads_privT`, under the trusted premise
  `StackDisjoint` for the threads' bounds.
-/

namespace Concurrency.CallComposeT

open Arm ArmThread Prog ClifThread ProgE2E ThreadRefine ArmAllocThread ClifCStepTerm
  RealizeCompiled CallCompose PrivCohT ClifThreadI PrepThread Rel

/-! ## Refinements of consecutive segments -/

section app
variable {K : Type} {MK : K → AKind → Prop}

theorem RefinesC.img {K' V : Type} {MK : K → K' → Prop} {pairT : Nat × Nat → Nat × Nat → Prop}
    {trS : List (List (Ev K V))} {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : RefinesC MK pairT trS trT ψ) {p : Nat × Nat} (hp : (evAt trS p).isSome) :
    (evAt trT (ψ p)).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨y, hy, -⟩ := h.ev p x hx
  rw [hy]; rfl

/-- **The order- and pair-preserving parts of consecutive refinements compose**
(`CallCompose.Refines.app` without the private sets). -/
theorem RefinesC.app {A B : List (List (Ev K BVal))} {TA TB : List (List Ev)}
    {ψ1 ψ2 : Nat × Nat → Nat × Nat}
    (h1 : RefinesC MK (MonPair TA) A (conv TA) ψ1)
    (h2 : RefinesC MK (MonPair TB) B (conv TB) ψ2)
    (hx : XClosed TB ∨ ∀ a x, evAt TA a = some x → x.k ≠ .acqXR) :
    RefinesC MK (MonPair (TA ++ TB)) (A ++ B) (conv (TA ++ TB))
      (appMap A.length TA.length ψ1 ψ2) := by
  have sA : ∀ p, (evAt A p).isSome → p.1 < A.length := fun p h => lt_of_isSome h
  have tA : ∀ p, (evAt A p).isSome → (ψ1 p).1 < TA.length := fun p h => by
    have := lt_of_isSome (RefinesC.img h1 h); simpa using this
  have eS : ∀ p : Nat × Nat, ¬ p.1 < A.length → evAt (A ++ B) p = evAt B (p.1 - A.length, p.2) :=
    fun p h => evAt_append_ge _ _ (by omega)
  have eS' : ∀ q : Nat × Nat, (q.1 + A.length - A.length, q.2) = q := fun q => by
    obtain ⟨q1, q2⟩ := q; simp
  rw [conv_append]
  exact {
    ev := fun p x hx => by
      by_cases hp : p.1 < A.length
      · rw [evAt_append_lt _ _ hp] at hx
        obtain ⟨y, hy, rest⟩ := h1.ev p x hx
        refine ⟨y, ?_, rest⟩
        rw [appMap_lt hp, evAt_append_lt _ _ (evAt_lt hy)]
        exact hy
      · rw [eS p hp] at hx
        obtain ⟨y, hy, rest⟩ := h2.ev _ x hx
        refine ⟨y, ?_, rest⟩
        rw [appMap_ge hp, ← conv_length TA, evAt_shift]
        exact hy
    mono := fun p q hp hq hl => by
      by_cases hpa : p.1 < A.length <;> by_cases hqa : q.1 < A.length
      · rw [evAt_append_lt _ _ hpa] at hp
        rw [evAt_append_lt _ _ hqa] at hq
        rw [appMap_lt hpa, appMap_lt hqa]
        exact h1.mono p q hp hq hl
      · rw [evAt_append_lt _ _ hpa] at hp
        rw [appMap_lt hpa, appMap_ge hqa]
        have := tA p hp
        left; simp only [shift]; omega
      · exfalso
        obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
        simp only [Lt] at hl hpa hqa; omega
      · rw [eS p hpa] at hp
        rw [eS q hqa] at hq
        rw [appMap_ge hpa, appMap_ge hqa]
        refine lt_shift.2 (h2.mono _ _ hp hq ?_)
        obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
        simp only [Lt] at hl hpa hqa ⊢; omega
    len := fun j hj => by
      by_cases hja : j < A.length
      · rw [List.getElem_append_left hja]; exact h1.len j hja
      · rw [List.getElem_append_right (by omega)]
        exact h2.len _ (by simp at hj; omega)
    pair := fun j hj h2l => by
      by_cases hja : j < A.length
      · rw [List.getElem_append_left hja] at h2l
        have hp := h1.pair j hja h2l
        rw [appMap_lt (p := (j, 0)) hja, appMap_lt (p := (j, 1)) hja]
        have hb : (ψ1 (j, 1)).1 < TA.length := tA _ (by
          simp only [evAt, List.getElem?_eq_getElem hja, Option.bind_some]
          rw [List.getElem?_eq_getElem (by omega)]; rfl)
        exact (monPair_left hb).2 hp
      · rw [List.getElem_append_right (by omega)] at h2l
        have hjb : j - A.length < B.length := by simp at hj; omega
        have hp := h2.pair _ hjb h2l
        rw [appMap_ge (p := (j, 0)) hja, appMap_ge (p := (j, 1)) hja]
        exact monPair_right.2 hp
    pair_inv := fun p q hp hq hpr => by
      by_cases hpa : p.1 < A.length <;> by_cases hqa : q.1 < A.length
      · rw [evAt_append_lt _ _ hpa] at hp
        rw [evAt_append_lt _ _ hqa] at hq
        rw [appMap_lt hpa, appMap_lt hqa] at hpr
        exact h1.pair_inv p q hp hq ((monPair_left (tA q hq)).1 hpr)
      · -- a monitor pair from the first segment into the second: excluded by `hx`
        exfalso
        rw [evAt_append_lt _ _ hpa] at hp
        rw [eS q hqa] at hq
        rw [appMap_lt hpa, appMap_ge hqa] at hpr
        obtain ⟨⟨x0, hx0, hx0k⟩, ⟨y, hy, hyk⟩, -, hbt⟩ := hpr
        have hpl := tA p hp
        rcases hx with hx | hx
        · rw [evAt_shift] at hy
          obtain ⟨a, x, hxa, hxk, hab⟩ := hx _ y hy hyk
          refine (hbt (shift TA.length a) x ?_ (lt_shift.2 hab)
            (by rw [evAt_shift]; exact hxa)).1 hxk
          left; simp only [shift]; omega
        · rw [evAt_append_lt _ _ hpl] at hx0
          exact hx _ x0 hx0 hx0k
      · exfalso
        rw [eS p hpa] at hp
        rw [evAt_append_lt _ _ hqa] at hq
        rw [appMap_ge hpa, appMap_lt hqa] at hpr
        obtain ⟨-, -, hab, -⟩ := hpr
        have := tA q hq
        simp only [Lt, shift] at hab; omega
      · rw [eS p hpa] at hp
        rw [eS q hqa] at hq
        rw [appMap_ge hpa, appMap_ge hqa] at hpr
        obtain ⟨j, e0, e1⟩ := h2.pair_inv _ _ hp hq (monPair_right.1 hpr)
        refine ⟨j + A.length, ?_, ?_⟩
        · obtain ⟨p1, p2⟩ := p
          simp only [Prod.mk.injEq] at e0 hpa ⊢; omega
        · obtain ⟨q1, q2⟩ := q
          simp only [Prod.mk.injEq] at e1 hqa ⊢; omega }

/-- The private sets of consecutive segments: the first `m` target steps' `P1`, the rest `P2`
shifted. -/
def catP (m : Nat) (P1 P2 : Nat × Nat → Nat → Prop) (q : Nat × Nat) : Nat → Prop :=
  if q.1 < m then P1 q else P2 (q.1 - m, q.2)

theorem catP_lt {m : Nat} {P1 P2 : Nat × Nat → Nat → Prop} {q : Nat × Nat} (h : q.1 < m) :
    catP m P1 P2 q = P1 q := by simp [catP, h]

theorem catP_shift {m : Nat} {P1 P2 : Nat × Nat → Nat → Prop} (q : Nat × Nat) :
    catP m P1 P2 (shift m q) = P2 q := by
  obtain ⟨q1, q2⟩ := q
  have h : ¬ q1 + m < m := by omega
  simp [catP, shift, h]

/-- **The location `a` is clean at the end of a refined segment** from the dirty set `D`: if `a`
is dirty at the start a source write writes it, and every unmatched Arm write there is followed
by a source write there. -/
def Clean {K' V : Type} (D : Nat → Prop) (trS : List (List (Ev K V))) (trT : List (List (Ev K' V)))
    (ψ : Nat × Nat → Nat × Nat) (a : Nat) : Prop :=
  (D a → ∃ q x, evAt trS q = some x ∧ x.dir = .W ∧ x.loc = a) ∧
  ∀ q y, evAt trT q = some y → y.dir = .W → y.loc = a → Unmatched trS ψ q →
    ∃ q' x', evAt trS q' = some x' ∧ x'.dir = .W ∧ x'.loc = a ∧ Lt q (ψ q')

/-- **`RefinesT` of consecutive Arm segments compose** (module doc). -/
theorem RefinesT.app {A B : List (List (Ev K BVal))} {TA TB : List (List Ev)}
    {ψ1 ψ2 : Nat × Nat → Nat × Nat} {D D' : Nat → Prop} {P1 P2 : Nat × Nat → Nat → Prop}
    (h1 : RefinesT MK D P1 (MonPair TA) A (conv TA) ψ1)
    (h2 : RefinesT MK D' P2 (MonPair TB) B (conv TB) ψ2)
    (hx : XClosed TB ∨ ∀ a x, evAt TA a = some x → x.k ≠ .acqXR)
    (hD : ∀ a, ¬ Clean D A (conv TA) ψ1 a → D' a) :
    RefinesT MK D (catP TA.length P1 P2) (MonPair (TA ++ TB)) (A ++ B) (conv (TA ++ TB))
      (appMap A.length TA.length ψ1 ψ2) := by
  classical
  have hc := RefinesC.app h1.toRefinesC h2.toRefinesC hx
  have sA : ∀ p, (evAt A p).isSome → p.1 < A.length := fun p h => lt_of_isSome h
  have tA : ∀ p, (evAt A p).isSome → (ψ1 p).1 < TA.length := fun p h => by
    have := lt_of_isSome (RefinesC.img h1.toRefinesC h); simpa using this
  have eS : ∀ p : Nat × Nat, ¬ p.1 < A.length → evAt (A ++ B) p = evAt B (p.1 - A.length, p.2) :=
    fun p h => evAt_append_ge _ _ (by omega)
  have unA : ∀ q, Unmatched (A ++ B) (appMap A.length TA.length ψ1 ψ2) q → Unmatched A ψ1 q :=
    fun q hu r hr e => hu r (by rw [evAt_append_lt _ _ (sA r hr)]; exact hr)
      (by rw [appMap_lt (sA r hr)]; exact e)
  have embA : ∀ q x', evAt A q = some x' → evAt (A ++ B) q = some x' := fun q x' h => by
    rw [evAt_append_lt _ _ (evAt_lt h)]; exact h
  have ltAB : ∀ q (r : Nat × Nat), (evAt A q).isSome → Lt (ψ1 q) (shift TA.length r) := fun q r h => by
    have := tA q h; left; simp only [shift]; omega
  refine { toRefinesC := hc, shared := ?_, priv := ?_, fresh0 := ?_, fresh := ?_ }
  · intro p x hx hF
    by_cases hp : p.1 < A.length
    · rw [evAt_append_lt _ _ hp] at hx
      rw [appMap_lt hp, catP_lt (tA p (by rw [hx]; rfl))]
      exact h1.shared p x hx hF
    · rw [eS p hp] at hx
      rw [appMap_ge hp, catP_shift]
      exact h2.shared _ x hx hF
  · intro q y hy hW hu
    rw [conv_append] at hy
    by_cases hq : q.1 < (conv TA).length
    · rw [evAt_append_lt _ _ hq] at hy
      rw [catP_lt (by simpa using hq)]
      exact h1.priv q y hy hW (unA q hu)
    · rw [evAt_append_ge _ _ (by omega)] at hy
      have e : q = shift TA.length (q.1 - (conv TA).length, q.2) := by
        obtain ⟨q1, q2⟩ := q; simp only [conv_length, shift] at hq ⊢; congr 1; omega
      rw [e, catP_shift]
      refine h2.priv _ y hy hW fun r hr e' => hu (shift A.length r) (by rw [evAt_shift]; exact hr) ?_
      rw [appMap_shift, e']
      exact e.symm
  · intro p x hx hR hDa
    by_cases hp : p.1 < A.length
    · rw [evAt_append_lt _ _ hp] at hx
      obtain ⟨q, x', hq, hW, hl, hlt⟩ := h1.fresh0 p x hx hR hDa
      refine ⟨q, x', embA q x' hq, hW, hl, ?_⟩
      rw [appMap_lt (evAt_lt hq), appMap_lt hp]; exact hlt
    · rw [eS p hp] at hx
      by_cases hm : ∃ q x', evAt A q = some x' ∧ x'.dir = .W ∧ x'.loc = x.loc
      · obtain ⟨q, x', hq, hW, hl⟩ := hm
        refine ⟨q, x', embA q x' hq, hW, hl, ?_⟩
        rw [appMap_lt (evAt_lt hq), appMap_ge hp]
        exact ltAB q _ (by rw [hq]; rfl)
      · have hd : D' x.loc := hD _ fun hc => hm (hc.1 hDa)
        obtain ⟨q, x', hq, hW, hl, hlt⟩ := h2.fresh0 _ x hx hR hd
        refine ⟨shift A.length q, x', by rw [evAt_shift]; exact hq, hW, hl, ?_⟩
        rw [appMap_shift, appMap_ge hp]; exact lt_shift.2 hlt
  · intro p x hx hR q y hy hW hl hlt hu
    rw [conv_append] at hy
    by_cases hp : p.1 < A.length
    · rw [evAt_append_lt _ _ hp] at hx
      rw [appMap_lt hp] at hlt
      have hqA : q.1 < (conv TA).length := by
        have := tA p (by rw [hx]; rfl)
        rcases hlt with h | ⟨h, -⟩ <;> simp only [conv_length] <;> omega
      rw [evAt_append_lt _ _ hqA] at hy
      obtain ⟨q', x', hq', hW', hl', h1', h2'⟩ := h1.fresh p x hx hR q y hy hW hl hlt (unA q hu)
      refine ⟨q', x', embA q' x' hq', hW', hl', ?_, ?_⟩
      · rw [appMap_lt (evAt_lt hq')]; exact h1'
      · rw [appMap_lt (evAt_lt hq'), appMap_lt hp]; exact h2'
    · rw [eS p hp] at hx
      rw [appMap_ge hp] at hlt
      by_cases hq : q.1 < (conv TA).length
      · rw [evAt_append_lt _ _ hq] at hy
        by_cases hm : ∃ q' x', evAt A q' = some x' ∧ x'.dir = .W ∧ x'.loc = x.loc ∧ Lt q (ψ1 q')
        · obtain ⟨q', x', hq', hW', hl', h1'⟩ := hm
          refine ⟨q', x', embA q' x' hq', hW', hl', by rw [appMap_lt (evAt_lt hq')]; exact h1', ?_⟩
          rw [appMap_lt (evAt_lt hq'), appMap_ge hp]
          exact ltAB q' _ (by rw [hq']; rfl)
        · have hd : D' x.loc := hD _ fun hc => hm (hc.2 q y hy hW hl (unA q hu))
          obtain ⟨r, x', hr, hW', hl', hlt'⟩ := h2.fresh0 _ x hx hR hd
          refine ⟨shift A.length r, x', by rw [evAt_shift]; exact hr, hW', hl', ?_, ?_⟩
          · rw [appMap_shift]; left; simp only [conv_length] at hq; simp only [shift]; omega
          · rw [appMap_shift, appMap_ge hp]; exact lt_shift.2 hlt'
      · rw [evAt_append_ge _ _ (by omega)] at hy
        have e : q = shift TA.length (q.1 - (conv TA).length, q.2) := by
          obtain ⟨q1, q2⟩ := q; simp only [conv_length, shift] at hq ⊢; congr 1; omega
        have hu2 : Unmatched B ψ2 (q.1 - (conv TA).length, q.2) := fun r hr e' =>
          hu (shift A.length r) (by rw [evAt_shift]; exact hr) (by rw [appMap_shift, e', ← e])
        have hlt2 : Lt (q.1 - (conv TA).length, q.2) (ψ2 (p.1 - A.length, p.2)) := by
          rw [e] at hlt; exact lt_shift.1 hlt
        obtain ⟨r, x', hr, hW', hl', h1', h2'⟩ := h2.fresh _ x hx hR _ y hy hW hl hlt2 hu2
        refine ⟨shift A.length r, x', by rw [evAt_shift]; exact hr, hW', hl', ?_, ?_⟩
        · rw [appMap_shift]; rw [e]; exact lt_shift.2 (by simpa using h1')
        · rw [appMap_shift, appMap_ge hp]; exact lt_shift.2 h2'

/-- **Cleanliness composes**: a location clean at the end of the second segment from the first
segment's end dirty set is clean at the end of both. -/
theorem clean_app {A B : List (List (Ev K BVal))} {TA TB : List (List Ev)}
    {ψ1 ψ2 : Nat × Nat → Nat × Nat} {D D' : Nat → Prop}
    (h1 : RefinesC MK (MonPair TA) A (conv TA) ψ1)
    (hD : ∀ a, ¬ Clean D A (conv TA) ψ1 a → D' a) {a : Nat} (h2 : Clean D' B (conv TB) ψ2 a) :
    Clean D (A ++ B) (conv (TA ++ TB)) (appMap A.length TA.length ψ1 ψ2) a := by
  classical
  have sA : ∀ p, (evAt A p).isSome → p.1 < A.length := fun p h => lt_of_isSome h
  have tA : ∀ p, (evAt A p).isSome → (ψ1 p).1 < TA.length := fun p h => by
    have := lt_of_isSome (RefinesC.img h1 h); simpa using this
  have embA : ∀ q x', evAt A q = some x' → evAt (A ++ B) q = some x' := fun q x' h => by
    rw [evAt_append_lt _ _ (evAt_lt h)]; exact h
  have unA : ∀ q, Unmatched (A ++ B) (appMap A.length TA.length ψ1 ψ2) q → Unmatched A ψ1 q :=
    fun q hu r hr e => hu r (by rw [evAt_append_lt _ _ (sA r hr)]; exact hr)
      (by rw [appMap_lt (sA r hr)]; exact e)
  refine ⟨fun hDa => ?_, fun q y hy hW hl hu => ?_⟩
  · by_cases hm : ∃ q x, evAt A q = some x ∧ x.dir = .W ∧ x.loc = a
    · obtain ⟨q, x, hq, hW, hl⟩ := hm
      exact ⟨q, x, embA q x hq, hW, hl⟩
    · obtain ⟨q, x, hq, hW, hl⟩ := h2.1 (hD a fun hc => hm (hc.1 hDa))
      exact ⟨shift A.length q, x, by rw [evAt_shift]; exact hq, hW, hl⟩
  · rw [conv_append] at hy
    by_cases hq : q.1 < (conv TA).length
    · rw [evAt_append_lt _ _ hq] at hy
      by_cases hm : ∃ q' x', evAt A q' = some x' ∧ x'.dir = .W ∧ x'.loc = a ∧ Lt q (ψ1 q')
      · obtain ⟨q', x', hq', hW', hl', h1'⟩ := hm
        exact ⟨q', x', embA q' x' hq', hW', hl', by rw [appMap_lt (evAt_lt hq')]; exact h1'⟩
      · obtain ⟨r, x', hr, hW', hl'⟩ := h2.1 (hD a fun hc => hm (hc.2 q y hy hW hl (unA q hu)))
        refine ⟨shift A.length r, x', by rw [evAt_shift]; exact hr, hW', hl', ?_⟩
        rw [appMap_shift]; left; simp only [conv_length] at hq; simp only [shift]; omega
    · rw [evAt_append_ge _ _ (by omega)] at hy
      have e : q = shift TA.length (q.1 - (conv TA).length, q.2) := by
        obtain ⟨q1, q2⟩ := q; simp only [conv_length, shift] at hq ⊢; congr 1; omega
      have hu2 : Unmatched B ψ2 (q.1 - (conv TA).length, q.2) := fun r hr e' =>
        hu (shift A.length r) (by rw [evAt_shift]; exact hr) (by rw [appMap_shift, e', ← e])
      obtain ⟨r, x', hr, hW', hl', h1'⟩ := h2.2 _ y hy hW hl hu2
      refine ⟨shift A.length r, x', by rw [evAt_shift]; exact hr, hW', hl', ?_⟩
      rw [appMap_shift, e]; exact lt_shift.2 (by simpa using h1')

end app

/-! ## CLIF threads whose bytes carry the mask -/

/-- The mask a thread state's own bytes encode: the `none` bytes. -/
def maskOf : TState → Nat → Prop
  | .run s => fun a => s.mem.bytes a = none
  | .ret _ => fun _ => False

/-- **`CStepI` on thread states carrying their mask in their bytes.** -/
def CStepS (env : Clif.Env) (p : Clif.Program) : TSem TState SKind BVal := fun t evs t' =>
  CStepI env p (t, maskOf t) evs (t', maskOf t')

/-- Runs of `CStepS`. -/
inductive CRunS (env : Clif.Env) (p : Clif.Program) :
    TState → List (List (Ev SKind BVal)) → TState → Prop
  | nil {t} : CRunS env p t [] t
  | cons {t t' t'' e tr} : CStepS env p t e t' → CRunS env p t' tr t'' → CRunS env p t (e :: tr) t''

theorem CRunS.append {env : Clif.Env} {p : Clif.Program} :
    ∀ {t t' t'' : TState} {a b : List (List (Ev SKind BVal))},
      CRunS env p t a t' → CRunS env p t' b t'' → CRunS env p t (a ++ b) t''
  | _, _, _, [], _, .nil, h => h
  | _, _, _, _ :: _, _, .cons h1 r, h => .cons h1 (r.append h)

theorem crunS_states {env : Clif.Env} {p : Clif.Program} :
    ∀ {t t' : TState} {tr : List (List (Ev SKind BVal))}, CRunS env p t tr t' →
      ∃ st : Nat → TState, st 0 = t ∧
        (∀ j (h : j < tr.length), CStepS env p (st j) tr[j] (st (j + 1))) ∧ st tr.length = t'
  | t, _, _, .nil => ⟨fun _ => t, rfl, fun j h => absurd h (Nat.not_lt_zero _), rfl⟩
  | t, _, _, .cons (t' := t1) hs hr => by
    obtain ⟨st, h0, hst, hend⟩ := crunS_states hr
    refine ⟨fun j => if j = 0 then t else st (j - 1), by simp, fun j h => ?_, by simpa using hend⟩
    cases j with
    | zero => simpa [h0] using hs
    | succ j => simpa using hst j (by simpa using h)

/-! ## Realized prefixes with time-varying private sets -/

section realized
variable (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop)

/-- **The first `k` labels of `ls` realize a `CRunS` run from `c` to `c'`** (module doc): with
private sets `P` inside the thread's bound `Bnd`, dirty locations `D` at the start, and every
location not clean at the end in `D'`. -/
def RealizedT (ls : List Lab) (k : Nat) (c c' : TState) (D D' : Nat → Prop) : Prop :=
  k ≤ ls.length ∧ ∃ (trS : List (List (Ev SKind BVal))) (ψ : Nat × Nat → Nat × Nat)
    (P : Nat × Nat → Nat → Prop), CRunS env p c trS c' ∧ XClosed (evTr (ls.take k)) ∧
    RefinesT Maps D P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
    (∀ q l, P q l → Bnd l) ∧ ∀ a, ¬ Clean D trS (conv (evTr (ls.take k))) ψ a → D' a

variable {env p Bnd}

theorem refinesT_nil {D : Nat → Prop} :
    RefinesT Maps D (fun _ _ => False) (MonPair []) ([] : List (List (Ev SKind BVal))) (conv [])
      id where
  ev p x hx := by rw [evAt_nil] at hx; cases hx
  mono p _ hp := by rw [evAt_nil] at hp; cases hp
  len j hj := absurd hj (Nat.not_lt_zero _)
  pair j hj := absurd hj (Nat.not_lt_zero _)
  pair_inv p _ hp := by rw [evAt_nil] at hp; cases hp
  shared p x hx := by rw [evAt_nil] at hx; cases hx
  priv p y hy := by simp [conv, evAt_nil] at hy
  fresh0 p x hx := by rw [evAt_nil] at hx; cases hx
  fresh p x hx := by rw [evAt_nil] at hx; cases hx

theorem RealizedT.zero (ls : List Lab) (c : TState) (D : Nat → Prop) :
    RealizedT env p Bnd ls 0 c c D D := by
  refine ⟨Nat.zero_le _, [], id, fun _ _ => False, .nil, by simpa [evTr] using xClosed_nil,
    by simpa [evTr] using refinesT_nil, fun _ _ h => h.elim, fun a ha => ?_⟩
  refine Classical.byContradiction fun hD => ha ⟨fun h => absurd h hD, fun q y hy => ?_⟩
  simp [evTr, conv, evAt_nil] at hy

theorem RealizedT.le {ls : List Lab} {k : Nat} {c c' : TState} {D D' : Nat → Prop}
    (h : RealizedT env p Bnd ls k c c' D D') : k ≤ ls.length := h.1

/-- **Realized prefixes compose.** -/
theorem RealizedT.trans {ls : List Lab} {k1 k2 : Nat} {c c1 c2 : TState} {D D1 D2 : Nat → Prop}
    (h1 : RealizedT env p Bnd ls k1 c c1 D D1)
    (h2 : RealizedT env p Bnd (ls.drop k1) k2 c1 c2 D1 D2) :
    RealizedT env p Bnd ls (k1 + k2) c c2 D D2 := by
  classical
  obtain ⟨hk1, A, ψ1, P1, r1, x1, f1, b1, d1⟩ := h1
  obtain ⟨hk2, B, ψ2, P2, r2, x2, f2, b2, d2⟩ := h2
  have e : evTr (ls.take (k1 + k2)) = evTr (ls.take k1) ++ evTr ((ls.drop k1).take k2) := by
    rw [List.take_add, evTr_append]
  refine ⟨by simp at hk2; omega, A ++ B, appMap A.length (evTr (ls.take k1)).length ψ1 ψ2,
    catP (evTr (ls.take k1)).length P1 P2, r1.append r2, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact x1.append x2
  · rw [e]; exact RefinesT.app f1 f2 (.inl x2) d1
  · intro q l h
    unfold catP at h
    split at h
    · exact b1 _ _ h
    · exact b2 _ _ h
  · intro a ha
    refine Classical.byContradiction fun hn => ha ?_
    rw [e]
    exact clean_app f1.toRefinesC d1 (Classical.byContradiction fun hc => hn (d2 a hc))

end realized

/-! ## The linking induction for any realization relation -/

section link
variable {σ : Type} (Real : List Lab → Nat → σ → σ → Prop) (M : ArmState → ArmState)
  (ok : ArmState → Lab → Prop)

/-- `CallCompose.FunReal` for the realization relation `Real`. -/
def FunRealG (Ret : AT → σ → AT → σ → Prop) (E : List Lab → σ → Prop) (u : AT) (c : σ) : Prop :=
  ∀ ls t', PRun Policy.arm M ok u ls t' → ∃ k c', Real ls k c c' ∧
    (k = ls.length ∨ E (ls.take k) c' ∨ ∃ v, PRun Policy.arm M ok u (ls.take k) v ∧ Ret u c v c')

/-- `CallCompose.SegOk` for the realization relation `Real`. -/
def SegOkG {G : Type} (Ent : G → AT → σ → Prop) (Ret : G → AT → σ → AT → σ → Prop)
    (E : List Lab → σ → Prop) (Inv : AT → σ → AT → σ → Prop) (g : G) : Prop :=
  ∀ u c x d, Inv u c x d → ∀ ls t', PRun Policy.arm M ok x ls t' →
    ∃ k d', Real ls k d d' ∧
      (k = ls.length ∨ E (ls.take k) d' ∨
        (∃ v, PRun Policy.arm M ok x (ls.take k) v ∧ Ret g u c v d') ∨
        (0 < k ∧ ∃ v h, PRun Policy.arm M ok x (ls.take k) v ∧ Ent h v d' ∧
          ∀ z d'', Ret h v d' z d'' → Inv u c z d''))

variable {Real M ok}

/-- **The linking induction for a realization relation with `zero`, `le` and `trans`**
(`CallCompose.link_compose`). -/
theorem link_composeG (hz : ∀ ls c, Real ls 0 c c) (hle : ∀ ls k c c', Real ls k c c' → k ≤ ls.length)
    (htr : ∀ ls k1 k2 c c1 c2, Real ls k1 c c1 → Real (ls.drop k1) k2 c1 c2 → Real ls (k1 + k2) c c2)
    {G : Type} {Ext : G → Prop} {Ent : G → AT → σ → Prop}
    {Ret : G → AT → σ → AT → σ → Prop} {E : List Lab → σ → Prop}
    {Inv : G → AT → σ → AT → σ → Prop} (hE : ∀ A B d, E B d → E (A ++ B) d)
    (hinit : ∀ g u c, ¬ Ext g → Ent g u c → Inv g u c u c)
    (hseg : ∀ g, ¬ Ext g → SegOkG Real M ok Ent Ret E (Inv g) g)
    (hext : ∀ h u c, Ext h → Ent h u c → FunRealG Real M ok (Ret h) E u c) :
    ∀ g u c, Ent g u c → FunRealG Real M ok (Ret g) E u c := by
  have key : ∀ n g u c x d ls t', ls.length ≤ n → ¬ Ext g → Inv g u c x d →
      PRun Policy.arm M ok x ls t' → ∃ k d', Real ls k d d' ∧
        (k = ls.length ∨ E (ls.take k) d' ∨ ∃ v, PRun Policy.arm M ok x (ls.take k) v ∧
          Ret g u c v d') := by
    intro n
    induction n with
    | zero =>
      intro g u c x d ls t' hl hg hI hr
      obtain rfl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact ⟨0, d, hz _ _, .inl rfl⟩
    | succ n ih =>
      intro g u c x d ls t' hl hg hI hr
      obtain ⟨k, d', hR, hend⟩ := hseg g hg u c x d hI ls t' hr
      rcases hend with h | h | h | ⟨hk, v, h, hv, hent, hres⟩
      · exact ⟨k, d', hR, .inl h⟩
      · exact ⟨k, d', hR, .inr (.inl h)⟩
      · exact ⟨k, d', hR, .inr (.inr h)⟩
      · have hkl := hle _ _ _ _ hR
        obtain ⟨v', hv', hrest⟩ := take_prun hr k
        obtain rfl := PRun.det hv' hv
        have hlen1 : (ls.drop k).length ≤ n := by simp; omega
        have hcal : ∃ k2 d2, Real (ls.drop k) k2 d' d2 ∧
            (k2 = (ls.drop k).length ∨ E ((ls.drop k).take k2) d2 ∨
              ∃ z, PRun Policy.arm M ok v' ((ls.drop k).take k2) z ∧ Ret h v' d' z d2) := by
          by_cases hx : Ext h
          · exact hext h v' d' hx hent _ _ hrest
          · exact ih h v' d' v' d' (ls.drop k) t' hlen1 hx (hinit h v' d' hx hent) hrest
        obtain ⟨k2, d2, hR2, hend2⟩ := hcal
        have hR12 := htr _ _ _ _ _ _ hR hR2
        rcases hend2 with h2 | h2 | ⟨z, hz', hret⟩
        · refine ⟨k + k2, d2, hR12, .inl ?_⟩
          simp at h2; omega
        · refine ⟨k + k2, d2, hR12, .inr (.inl ?_)⟩
          rw [List.take_add]
          exact hE _ _ _ h2
        · have hk2 := hle _ _ _ _ hR2
          obtain ⟨z', hz'', hrest2⟩ := take_prun hrest k2
          obtain rfl := PRun.det hz'' hz'
          have hlen2 : (ls.drop k |>.drop k2).length ≤ n := by simp; omega
          obtain ⟨k3, d3, hR3, hend3⟩ :=
            ih g u c z' d2 _ t' hlen2 hg (hres z' d2 hret) hrest2
          rw [List.drop_drop] at hR3 hend3
          have hR123 := htr _ _ _ _ _ _ hR12 hR3
          refine ⟨k + k2 + k3, d3, hR123, ?_⟩
          rcases hend3 with h3 | h3 | ⟨w, hw, hret3⟩
          · left; simp at h3 hk2 ⊢; omega
          · have e : ls.take (k + k2 + k3) = ls.take k ++ (ls.drop k).take k2 ++
                (ls.drop (k + k2)).take k3 := by
              rw [List.take_add, List.take_add]
            refine .inr (.inl ?_)
            rw [e]
            exact hE _ _ _ h3
          · refine .inr (.inr ⟨w, ?_, hret3⟩)
            have e : ls.take (k + k2 + k3) = ls.take k ++ (ls.drop k).take k2 ++
                (ls.drop (k + k2)).take k3 := by
              rw [List.take_add, List.take_add]
            rw [e]
            exact (hv'.append hz').append hw
  intro g u c hen ls t' hr
  by_cases hx : Ext g
  · exact hext g u c hx hen ls t' hr
  · exact key ls.length g u c u c ls t' (Nat.le_refl _) hx (hinit g u c hx hen) hr

end link

/-- The realization relation of a thread with bound `Bnd`: `RealizedT` on states carrying their
dirty set. -/
def RealT (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop) (ls : List Lab) (k : Nat)
    (c c' : TState × (Nat → Prop)) : Prop :=
  RealizedT env p Bnd ls k c.1 c'.1 c.2 c'.2

/-- **The linking induction with time-varying private sets.** -/
theorem link_composeT {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}
    {M : ArmState → ArmState} {ok : ArmState → Lab → Prop} {G : Type} {Ext : G → Prop}
    {Ent : G → AT → TState × (Nat → Prop) → Prop}
    {Ret : G → AT → TState × (Nat → Prop) → AT → TState × (Nat → Prop) → Prop}
    {E : List Lab → TState × (Nat → Prop) → Prop}
    {Inv : G → AT → TState × (Nat → Prop) → AT → TState × (Nat → Prop) → Prop}
    (hE : ∀ A B d, E B d → E (A ++ B) d) (hinit : ∀ g u c, ¬ Ext g → Ent g u c → Inv g u c u c)
    (hseg : ∀ g, ¬ Ext g → SegOkG (RealT env p Bnd) M ok Ent Ret E (Inv g) g)
    (hext : ∀ h u c, Ext h → Ent h u c → FunRealG (RealT env p Bnd) M ok (Ret h) E u c) :
    ∀ g u c, Ent g u c → FunRealG (RealT env p Bnd) M ok (Ret g) E u c :=
  link_composeG (fun ls c => RealizedT.zero ls c.1 c.2) (fun _ _ _ _ h => h.1)
    (fun ls k1 k2 c c1 c2 (h1 : RealizedT env p Bnd ls k1 c.1 c1.1 c.2 c1.2)
      (h2 : RealizedT env p Bnd (ls.drop k1) k2 c1.1 c2.1 c1.2 c2.2) =>
      (RealizedT.trans h1 h2 : RealizedT env p Bnd ls (k1 + k2) c.1 c2.1 c.2 c2.2)) hE hinit hseg hext

/-! ## The program -/

theorem StackDisjoint.mono {σ : Type} {PA : Traces σ AKind BVal} {U U' : Nat → Nat → Prop}
    (h : StackDisjoint PA U') (hU : ∀ j < PA.n, ∀ l, U j l → U' j l) : StackDisjoint PA U :=
  fun i hi j hj hne q x hx hF hU' => h i hi j hj hne q x hx hF (hU j hj _ hU')

/-- **The contract for `n` threads given by `RealizedT` contracts** (`CallCompose.realizes_linked`
with time-varying private sets): each thread `i` runs a precise Arm run of its machine from
`sA i`, whose prefixes are realized from the CLIF state `cs i` (dirty set `D0 i` at the start)
with private sets within the thread's bound `Bnd i`. Every SC-per-location execution of the
realized prefixes (well formed, initial writes first, its `rmw` the monitor pairs, its initial
locations beyond the CLIF ones dirty at some thread's start) in which no thread touches another
thread's bound or start-dirty locations (`StackDisjoint`, trusted) is realized by `CStepS` threads
from the `cs i`. -/
theorem realizes_linkedT {n : Nat} {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Nat → Prop}
    {M : Nat → ArmState → ArmState} {ok : Nat → ArmState → Lab → Prop} {cs : Nat → TState}
    {D0 : Nat → Nat → Prop} {sA : Nat → AT}
    (hc : ∀ i < n, ∀ ls t', PRun Policy.arm (M i) (ok i) (sA i) ls t' →
      ∃ k c' D', RealizedT env p (Bnd i) ls k (cs i) c' (D0 i) D')
    {ls : Nat → List Lab} {t' : Nat → AT}
    (hr : ∀ i < n, PRun Policy.arm (M i) (ok i) (sA i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = n →
        (∀ i < n, PA.tr i = conv (evTr ((ls i).take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        Acyclic (union (PA.exec locsA rfA coA rmwA).poLoc (PA.exec locsA rfA coA rmwA).com) →
        InitFirst (PA.exec locsA rfA coA rmwA) →
        (∀ i < n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr ((ls i).take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < n, D0 j (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        StackDisjoint PA (fun j l => D0 j l ∨ Bnd j l) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
          (∀ i < n, PC.st i 0 = cs i) ∧ PC.Runs (CStepS env p) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) := by
  classical
  have hth : ∀ i, ∃ c : Nat × (Nat × Nat → Nat → Prop), i < n → c.1 ≤ (ls i).length ∧
      ∃ (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      st 0 = cs i ∧ (∀ j (h : j < trS.length), CStepS env p (st j) trS[j] (st (j + 1))) ∧
      RefinesT Maps (D0 i) c.2 (MonPair (evTr ((ls i).take c.1))) trS
        (conv (evTr ((ls i).take c.1))) ψ ∧ ∀ q l, c.2 q l → Bnd i l := fun i => by
    by_cases hi : i < n
    · obtain ⟨k, c', D', hk, trS, ψ, P, hrun, -, href, hb, -⟩ := hc i hi _ _ (hr i hi)
      obtain ⟨st, h0, hst, -⟩ := crunS_states hrun
      exact ⟨(k, P), fun _ => ⟨hk, trS, st, ψ, h0, hst, href, hb⟩⟩
    · exact ⟨(0, fun _ _ => False), fun h => absurd h hi⟩
  let k : Nat → Nat := fun i => (Classical.choose (hth i)).1
  let P : Nat → Nat × Nat → Nat → Prop := fun i => (Classical.choose (hth i)).2
  have hk : ∀ i (hi : i < n), k i ≤ (ls i).length ∧
      ∃ (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      st 0 = cs i ∧ (∀ j (h : j < trS.length), CStepS env p (st j) trS[j] (st (j + 1))) ∧
      RefinesT Maps (D0 i) (P i) (MonPair (evTr ((ls i).take (k i)))) trS
        (conv (evTr ((ls i).take (k i)))) ψ ∧ ∀ q l, P i q l → Bnd i l :=
    fun i hi => Classical.choose_spec (hth i) hi
  refine ⟨k, fun i hi => (hk i hi).1, ?_⟩
  intro PA locsA locsC MA0 MC0 rfA coA rmwA hn htr hwf hint hinit hrmw hlocs hpriv0 hval0 hdisj
  obtain ⟨PC, φ, hPn, hs0, hruns, hreal⟩ := realizes_of_threads_privT (T := CStepS env p)
    (s0 := cs) (Priv0 := D0) (PrivAt := P)
    (pairT := fun i => MonPair (evTr ((ls i).take (k i)))) (Obs := fun _ _ _ => True)
    hwf hint hinit (fun i hi => hrmw i (hn ▸ hi)) hlocs
    (fun q h hq => by obtain ⟨j, hj, hD⟩ := hpriv0 q h hq; exact ⟨j, hn ▸ hj, hD⟩) hval0
    (StackDisjoint.mono hdisj fun j hj l h => by
      rcases h with h | ⟨q, h⟩
      · exact .inl h
      · obtain ⟨-, -, -, -, -, -, -, hb⟩ := hk j (hn ▸ hj)
        exact .inr (hb q l h))
    (fun i hi => by
      have hi' : i < n := hn ▸ hi
      obtain ⟨-, trS, st, ψ, h0, hst, href, -⟩ := hk i hi'
      exact ⟨trS, st, ψ, h0, hst, by rw [htr i hi']; exact href, trivial⟩)
  exact ⟨PC, φ, hPn.trans hn, fun i _ => hs0 i, hruns, hreal⟩

end Concurrency.CallComposeT
