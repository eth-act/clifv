import FV.Concurrency.PrepThread
import FV.Concurrency.ArmPrecise

/-!
# The Arm machine against the allocated code: the run level (T2h, #311, layer 4b)

Layer 4b (`docs/plans/atomics.md` §3e) relates the Arm thread (`ArmThread.TStep` under precise
labels, `ArmPrecise.Precise`) to the allocated code's thread semantics (`AllocThread.MTStep`).
It is **backward**: the Arm run is given (its reads return any bytes) and the source run is
built from it. This file is the run level, generic in the source step relation `S` and in the
relation `Rel` between Arm thread states and source configurations at item boundaries:

* `PRun P f ok`: precise runs of the Arm thread whose steps satisfy `ok` (e.g. reads of the
  thread's private memory return the thread's own bytes); deterministic given the labels
  (`PRun.det`);
* `MonPair`: the Arm trace's **monitor pairs**, an `ldaxr` read and a later successful `stlxr`
  write with no exclusive event in between (Armv8's `rmw` of the emitted code: a failing
  `stlxr` has no event, so a failed iteration's `ldaxr` pairs with nothing);
* `Img`: one source step's events are events of an Arm segment (same kind, address, size and
  bytes, in order), the segment's other writes are private, the source step's events are not
  (barrier events, direction `.F`, exempt: a `dmb` accesses no memory — its event
  `ArmInstFoot.dmbEv` is at address 0 with size 0 and no bytes — so it cannot touch private
  data, and nothing need keep address 0 out of the private set), and an atomic update
  (`Shape`: `[acqXR, relXW]`) maps to a monitor pair;
* `ItemSim`: **the per-item obligation**: from related states, every precise Arm run either
  reaches the end of the item (a source step whose events are the image of the segment, the
  states after it related; a step without Arm instructions decreases a measure `μ`), or ends
  inside it (with the source step already realized, or with private writes only), or the source
  has terminated (`Term`: returned, trapped);
* **`refines_of_itemSim`**: under `ItemSim`, every precise Arm run from related states realizes
  a source run (`SRun`) with `ThreadRefine.Refines` (kinds equal, private set `Priv`, atomic
  updates the monitor pairs) on the prefix up to the source's termination.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmThread ArmPrecise ThreadRefine ProgE2E PrepThread

/-! ## Precise runs -/

/-- **Precise runs of an Arm thread** whose steps satisfy `ok`. -/
inductive PRun (P : Policy) (f : ArmState → ArmState) (ok : ArmState → Lab → Prop) :
    ArmState × Mon → List Lab → ArmState × Mon → Prop
  | nil {t} : PRun P f ok t [] t
  | cons {t t1 t2 l ls} : TStep P f t l t1 → Precise t.1 l → ok t.1 l → PRun P f ok t1 ls t2 →
      PRun P f ok t (l :: ls) t2

section prun
variable {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}

/-- A thread step is determined by its label. -/
theorem tstep_det {t t1 t2 : ArmState × Mon} {l : Lab} (h1 : TStep P f t l t1)
    (h2 : TStep P f t l t2) : t1 = t2 := by
  cases h1 with
  | exec => cases h2 with
    | exec => rfl
  | xfail hc _ _ _ => cases h2 with
    | xfail hc' _ _ _ =>
      rw [hc] at hc'
      cases hc'
      rfl

theorem PRun.det : ∀ {t t1 t2 : ArmState × Mon} {ls : List Lab},
    PRun P f ok t ls t1 → PRun P f ok t ls t2 → t1 = t2
  | _, _, _, [], .nil, .nil => rfl
  | _, _, _, _ :: _, .cons h1 _ _ r1, .cons h2 _ _ r2 => by
    rw [tstep_det h1 h2] at r1
    exact PRun.det r1 r2

theorem PRun.append : ∀ {t t1 t2 : ArmState × Mon} {A B : List Lab},
    PRun P f ok t A t1 → PRun P f ok t1 B t2 → PRun P f ok t (A ++ B) t2
  | _, _, _, [], _, .nil, h => h
  | _, _, _, _ :: _, _, .cons h1 hp ho r1, h => .cons h1 hp ho (PRun.append r1 h)

theorem PRun.split : ∀ (A B : List Lab) {t t2 : ArmState × Mon},
    PRun P f ok t (A ++ B) t2 → ∃ t1, PRun P f ok t A t1 ∧ PRun P f ok t1 B t2
  | [], _, _, _, h => ⟨_, .nil, h⟩
  | _ :: A, B, _, _, .cons h1 hp ho r => by
    obtain ⟨t1, r1, r2⟩ := PRun.split A B r
    exact ⟨t1, .cons h1 hp ho r1, r2⟩

end prun

/-! ## Traces and positions -/

/-- The events of a run's labels, step by step. -/
def evTr (ls : List Lab) : List (List Ev) := ls.map (·.evs)

theorem evTr_append (A B : List Lab) : evTr (A ++ B) = evTr A ++ evTr B := List.map_append

theorem evTr_length (ls : List Lab) : (evTr ls).length = ls.length := List.length_map _

section pos
variable {α : Type}

theorem evAt_append_lt (A B : List (List α)) {p : Nat × Nat} (h : p.1 < A.length) :
    evAt (A ++ B) p = evAt A p := by
  simp only [evAt, List.getElem?_append_left h]

theorem evAt_append_ge (A B : List (List α)) {p : Nat × Nat} (h : A.length ≤ p.1) :
    evAt (A ++ B) p = evAt B (p.1 - A.length, p.2) := by
  simp only [evAt, List.getElem?_append_right h]

theorem evAt_lt {tr : List (List α)} {p : Nat × Nat} {x : α} (h : evAt tr p = some x) :
    p.1 < tr.length := by
  refine Classical.byContradiction fun hn => ?_
  simp only [evAt, List.getElem?_eq_none (by omega : tr.length ≤ p.1), Option.bind_none] at h
  cases h

theorem evAt_nil (p : Nat × Nat) : evAt ([] : List (List α)) p = none := by
  simp [evAt]

theorem evAt_single (e : List α) (k : Nat) : evAt [e] (0, k) = e[k]? := by
  simp [evAt]

theorem evAt_cons_succ (e : List α) (tr : List (List α)) (j k : Nat) :
    evAt (e :: tr) (j + 1, k) = evAt tr (j, k) := by
  simp [evAt]

theorem evAt_cons_zero (e : List α) (tr : List (List α)) (k : Nat) :
    evAt (e :: tr) (0, k) = e[k]? := by
  simp [evAt]

theorem evAt_conv (tr : List (List Ev)) (p : Nat × Nat) :
    evAt (conv tr) p = (evAt tr p).map convEv := by
  simp only [evAt, conv, List.getElem?_map]
  cases tr[p.1]? <;> simp [List.getElem?_map]

end pos

/-- Positions shifted by `n` steps. -/
def shift (n : Nat) (p : Nat × Nat) : Nat × Nat := (p.1 + n, p.2)

theorem lt_shift {n : Nat} {p q : Nat × Nat} : Lt (shift n p) (shift n q) ↔ Lt p q := by
  simp only [Lt, shift]; omega

/-! ## Monitor pairs, shapes, images -/

/-- **The monitor pairs of an Arm trace**: an `ldaxr` read at `a` and a successful `stlxr`
write at `b` after it, with no exclusive event in between. -/
def MonPair (tr : List (List Ev)) (a b : Nat × Nat) : Prop :=
  (∃ x, evAt tr a = some x ∧ x.k = .acqXR) ∧ (∃ y, evAt tr b = some y ∧ y.k = .relXW) ∧ Lt a b ∧
    ∀ q z, Lt a q → Lt q b → evAt tr q = some z → z.k ≠ .acqXR ∧ z.k ≠ .relXW

/-- The exclusive events of a source step: at most one event, no `relXW`, or exactly an atomic
update `[acqXR, relXW]`. -/
def Shape (evs : List Ev) : Prop :=
  (evs.length ≤ 1 ∧ ∀ e ∈ evs, e.k ≠ .relXW) ∨
    ∃ x y, evs = [x, y] ∧ x.k = .acqXR ∧ y.k = .relXW

theorem Shape.len {evs : List Ev} (h : Shape evs) : evs.length ≤ 2 := by
  rcases h with ⟨h, -⟩ | ⟨x, y, rfl, -⟩
  · omega
  · simp

/-- **The events `evs` of one source step are events of the Arm segment `tr`** through `φ`
(module doc). -/
structure Img (Priv : Nat → Prop) (evs : List Ev) (tr : List (List Ev)) (φ : Nat → Nat × Nat) :
    Prop where
  ev : ∀ k (h : k < evs.length), evAt tr (φ k) = some evs[k]
  mono : ∀ k k', k < k' → k' < evs.length → Lt (φ k) (φ k')
  priv : ∀ p y, evAt tr p = some y → y.k.dir = .W → (∀ k < evs.length, φ k ≠ p) →
    Priv y.addr.toNat ∧ y.k ≠ .relXW
  shared : ∀ e ∈ evs, e.k.dir ≠ .F → ¬ Priv e.addr.toNat
  shape : Shape evs
  pair : evs.length = 2 → MonPair tr (φ 0) (φ 1)

/-- An Arm segment without events beyond private writes images no step's events. A private write
is never a successful store exclusive (`relXW`): those are images of atomic updates. -/
def PrivW (Priv : Nat → Prop) (tr : List (List Ev)) : Prop :=
  ∀ p y, evAt tr p = some y → y.k.dir = .W → Priv y.addr.toNat ∧ y.k ≠ .relXW

/-! ## Refinement of Arm-event traces -/

/-- The refinement on Arm events (equal events), before conversion to program events. -/
structure RefA (Priv : Nat → Prop) (trS trT : List (List Ev)) (ψ : Nat × Nat → Nat × Nat) :
    Prop where
  ev : ∀ p x, evAt trS p = some x → evAt trT (ψ p) = some x
  mono : ∀ p q, (evAt trS p).isSome → (evAt trS q).isSome → Lt p q → Lt (ψ p) (ψ q)
  priv : ∀ p y, evAt trT p = some y → y.k.dir = .W → (∀ q, (evAt trS q).isSome → ψ q ≠ p) →
    Priv y.addr.toNat ∧ y.k ≠ .relXW
  shared : ∀ p x, evAt trS p = some x → x.k.dir ≠ .F → ¬ Priv x.addr.toNat
  shape : ∀ j (h : j < trS.length), Shape trS[j]
  pair : ∀ j (h : j < trS.length), trS[j].length = 2 → MonPair trT (ψ (j, 0)) (ψ (j, 1))

section refA
variable {Priv : Nat → Prop}

theorem refA_nil {trT : List (List Ev)} (h : PrivW Priv trT) (ψ : Nat × Nat → Nat × Nat) :
    RefA Priv [] trT ψ where
  ev p x hx := by rw [evAt_nil] at hx; cases hx
  mono p _ hp := by rw [evAt_nil] at hp; cases hp
  priv p y hy hW _ := h p y hy hW
  shared p x hx := by rw [evAt_nil] at hx; cases hx
  shape j hj := absurd hj (Nat.not_lt_zero _)
  pair j hj := absurd hj (Nat.not_lt_zero _)

theorem some_of_isSome {α : Type} {o : Option α} (h : o.isSome) : ∃ x, o = some x :=
  Option.isSome_iff_exists.mp h

/-- The composed position map: the first step through `φ`, the rest through `ψ` shifted past
the segment of `n` Arm steps. -/
def consMap (n : Nat) (φ : Nat → Nat × Nat) (ψ : Nat × Nat → Nat × Nat) (p : Nat × Nat) :
    Nat × Nat :=
  match p.1 with
  | 0 => φ p.2
  | j + 1 => shift n (ψ (j, p.2))

theorem lt_of_img {evs : List Ev} {A : List (List Ev)} {φ : Nat → Nat × Nat}
    (hi : Img Priv evs A φ) {k : Nat} (hk : k < evs.length) : (φ k).1 < A.length :=
  evAt_lt (hi.ev k hk)

theorem evAt_shift_some {trT : List (List Ev)} {ψ : Nat × Nat → Nat × Nat} {q : Nat × Nat}
    {x : Ev} (h : evAt trT (ψ q) = some x) (A : List (List Ev)) :
    evAt (A ++ trT) (shift A.length (ψ q)) = some x := by
  rw [evAt_append_ge _ _ (by simp [shift])]
  simpa [shift] using h

/-- **Composition**: an image of one step in a segment `A`, followed by a refinement of the
rest in `B`. -/
theorem RefA.cons {evs : List Ev} {trS : List (List Ev)} {A B : List (List Ev)}
    {φ : Nat → Nat × Nat} {ψ : Nat × Nat → Nat × Nat} (hi : Img Priv evs A φ)
    (hr : RefA Priv trS B ψ) : RefA Priv (evs :: trS) (A ++ B) (consMap A.length φ ψ) where
  ev p x hx := by
    obtain ⟨j, k⟩ := p
    cases j with
    | zero =>
      rw [evAt_cons_zero] at hx
      obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hx
      simp only [consMap]
      rw [evAt_append_lt _ _ (lt_of_img hi hk)]
      exact hi.ev k hk
    | succ j =>
      rw [evAt_cons_succ] at hx
      exact evAt_shift_some (hr.ev _ x hx) A
  mono p q hp hq hl := by
    obtain ⟨j, k⟩ := p
    obtain ⟨j', k'⟩ := q
    cases j with
    | zero =>
      rw [evAt_cons_zero] at hp
      obtain ⟨x, hx⟩ := some_of_isSome hp
      have hk := (List.getElem?_eq_some_iff.mp hx).1
      cases j' with
      | zero =>
        rw [evAt_cons_zero] at hq
        obtain ⟨x', hx'⟩ := some_of_isSome hq
        have hk' := (List.getElem?_eq_some_iff.mp hx').1
        simp only [Lt] at hl
        exact hi.mono k k' (by omega) hk'
      | succ j' =>
        rw [evAt_cons_succ] at hq
        obtain ⟨x', hx'⟩ := some_of_isSome hq
        have h1 := lt_of_img hi hk
        have h2 := hr.ev _ x' hx'
        simp only [consMap, Lt, shift]
        omega
    | succ j =>
      cases j' with
      | zero => simp only [Lt] at hl; omega
      | succ j' =>
        rw [evAt_cons_succ] at hp hq
        simp only [consMap]
        refine lt_shift.mpr (hr.mono _ _ hp hq ?_)
        simp only [Lt] at hl ⊢
        omega
  priv p y hy hW hn := by
    by_cases hp : p.1 < A.length
    · rw [evAt_append_lt _ _ hp] at hy
      refine hi.priv p y hy hW fun k hk e => hn (0, k) ?_ ?_
      · rw [evAt_cons_zero, List.getElem?_eq_getElem hk]; rfl
      · simp only [consMap]; exact e
    · rw [evAt_append_ge _ _ (by omega)] at hy
      refine hr.priv _ y hy hW fun q hq e => hn (q.1 + 1, q.2) ?_ ?_
      · rw [evAt_cons_succ]; exact hq
      · simp only [consMap, shift, e]
        ext <;> simp; omega
  shared p x hx hF := by
    obtain ⟨j, k⟩ := p
    cases j with
    | zero =>
      rw [evAt_cons_zero] at hx
      exact hi.shared x (List.mem_of_getElem? hx) hF
    | succ j =>
      rw [evAt_cons_succ] at hx
      exact hr.shared _ x hx hF
  shape j hj := by
    cases j with
    | zero => exact hi.shape
    | succ j => exact hr.shape j (by simpa using hj)
  pair j hj h2 := by
    cases j with
    | zero =>
      have hp := hi.pair h2
      simp only [consMap]
      obtain ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hl, hb⟩ := hp
      have h1 : (φ 0).1 < A.length := evAt_lt hx
      have h1' : (φ 1).1 < A.length := evAt_lt hy
      refine ⟨⟨x, by rw [evAt_append_lt _ _ h1]; exact hx, hxk⟩,
        ⟨y, by rw [evAt_append_lt _ _ h1']; exact hy, hyk⟩, hl, fun q z hq1 hq2 hz => ?_⟩
      have hq : q.1 < A.length := by simp only [Lt] at hq2; omega
      rw [evAt_append_lt _ _ hq] at hz
      exact hb q z hq1 hq2 hz
    | succ j =>
      have hp := hr.pair j (by simpa using hj) h2
      simp only [consMap]
      obtain ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hl, hb⟩ := hp
      refine ⟨⟨x, evAt_shift_some hx A, hxk⟩, ⟨y, evAt_shift_some hy A, hyk⟩, lt_shift.mpr hl,
        fun q z hq1 hq2 hz => ?_⟩
      have hq : A.length ≤ q.1 := by simp only [Lt, shift] at hq1; omega
      rw [evAt_append_ge _ _ hq] at hz
      have e : q = shift A.length (q.1 - A.length, q.2) := by
        simp only [shift]; ext <;> simp; omega
      rw [e] at hq1 hq2
      exact hb _ z (lt_shift.mp hq1) (lt_shift.mp hq2) hz

theorem RefA.lt_iff {trS trT : List (List Ev)} {ψ : Nat × Nat → Nat × Nat}
    (h : RefA Priv trS trT ψ) {p q : Nat × Nat}
    (hp : (evAt trS p).isSome) (hq : (evAt trS q).isSome) : Lt p q ↔ Lt (ψ p) (ψ q) := by
  refine ⟨h.mono p q hp hq, fun hl => Classical.byContradiction fun hn => ?_⟩
  by_cases e : p = q
  · subst e; exact Lt.irrefl _ hl
  · rcases Lt.total e with h' | h'
    · exact hn h'
    · exact Lt.asymm hl (h.mono q p hq hp h')

/-- The source position of a `relXW` event is the second of an atomic update. -/
theorem shape_relXW {trS : List (List Ev)} (hs : ∀ j (h : j < trS.length), Shape trS[j])
    {q : Nat × Nat} {x : Ev} (hx : evAt trS q = some x) (hk : x.k = .relXW) :
    q.2 = 1 ∧ ∃ x0, evAt trS (q.1, 0) = some x0 ∧ x0.k = .acqXR := by
  have hj := evAt_lt hx
  have hx' : trS[q.1][q.2]? = some x := by
    simpa [evAt, List.getElem?_eq_getElem hj] using hx
  rcases hs q.1 hj with ⟨hl, hn⟩ | ⟨a, b, he, ha, hb⟩
  · exact absurd hk (hn x (List.mem_of_getElem? hx'))
  · rw [he] at hx'
    have hq2 : q.2 < 2 := (List.getElem?_eq_some_iff.mp hx').1
    rcases (by omega : q.2 = 0 ∨ q.2 = 1) with h0 | h1
    · rw [h0] at hx'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx'
      subst hx'
      rw [ha] at hk; cases hk
    · refine ⟨h1, a, ?_, ha⟩
      simp [evAt, List.getElem?_eq_getElem hj, he]

/-- The source position of an `acqXR` event is the first of its step. -/
theorem shape_acqXR {trS : List (List Ev)} (hs : ∀ j (h : j < trS.length), Shape trS[j])
    {p : Nat × Nat} {x : Ev} (hx : evAt trS p = some x) (hk : x.k = .acqXR) : p.2 = 0 := by
  have hj := evAt_lt hx
  have hx' : trS[p.1][p.2]? = some x := by
    simpa [evAt, List.getElem?_eq_getElem hj] using hx
  have hl := (List.getElem?_eq_some_iff.mp hx').1
  rcases hs p.1 hj with ⟨hl1, -⟩ | ⟨a, b, he, ha, hb⟩
  · omega
  · rw [he] at hx' hl
    rcases (by simp at hl; omega : p.2 = 0 ∨ p.2 = 1) with h0 | h1
    · exact h0
    · rw [h1] at hx'
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx'
      subst hx'
      rw [hb] at hk; cases hk

/-- **Conversion to program events**: `RefA` is `ThreadRefine.Refines` with equal kinds, the
private set `Priv` and the monitor pairs as atomic pairs. -/
theorem RefA.refines {trS trT : List (List Ev)} {ψ : Nat × Nat → Nat × Nat}
    (h : RefA Priv trS trT ψ) :
    Refines (· = ·) Priv (MonPair trT) (conv trS) (conv trT) ψ where
  ev p x hx := by
    rw [evAt_conv] at hx
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hx
    refine ⟨convEv e, by rw [evAt_conv, h.ev p e he]; rfl, rfl, rfl, rfl, rfl, rfl⟩
  mono p q hp hq hl := by
    rw [evAt_conv, Option.isSome_map] at hp hq
    exact h.mono p q hp hq hl
  shared p x hx hF := by
    rw [evAt_conv] at hx
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact h.shared p e he hF
  priv p y hy hW hn := by
    rw [evAt_conv] at hy
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact (h.priv p e he hW fun q hq => hn q (by rw [evAt_conv, Option.isSome_map]; exact hq)).1
  len j hj := by
    simp only [conv, List.getElem_map, List.length_map]
    exact (h.shape j (by simpa [conv] using hj)).len
  pair j hj h2 := by
    simp only [conv, List.getElem_map, List.length_map] at h2
    exact h.pair j (by simpa [conv] using hj) h2
  pair_inv p q hp hq hpr := by
    rw [evAt_conv, Option.isSome_map] at hp hq
    obtain ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hl, hb⟩ := hpr
    obtain ⟨xs, hxs⟩ := some_of_isSome hp
    obtain ⟨ys, hys⟩ := some_of_isSome hq
    rw [h.ev p xs hxs] at hx
    rw [h.ev q ys hys] at hy
    cases hx; cases hy
    have hp0 := shape_acqXR h.shape hxs hxk
    obtain ⟨hq1, x0, hx0, hx0k⟩ := shape_relXW h.shape hys hyk
    have hlt : Lt p q := (h.lt_iff hp hq).mpr hl
    rcases Nat.lt_or_ge p.1 q.1 with h1 | h1
    · have hm1 : Lt (ψ p) (ψ (q.1, 0)) := h.mono _ _ hp (by rw [hx0]; rfl) (Or.inl h1)
      have hm2 : Lt (ψ (q.1, 0)) (ψ q) :=
        h.mono _ _ (by rw [hx0]; rfl) hq (Or.inr ⟨rfl, show 0 < q.2 by omega⟩)
      exact absurd hx0k (hb _ _ hm1 hm2 (h.ev _ _ hx0)).1
    · have e1 : p.1 = q.1 := by simp only [Lt] at hlt; omega
      exact ⟨p.1, by ext <;> simp [hp0], by ext <;> simp [e1, hq1]⟩

/-- **The target of a `RefA` is exclusive-closed** (`CallCompose.XClosed`): a `relXW` event is
not private, so it is the image of a source `relXW`, the second event of an atomic update whose
`acqXR` maps before it. -/
theorem RefA.xClosed {trS trT : List (List Ev)} {ψ : Nat × Nat → Nat × Nat}
    (h : RefA Priv trS trT ψ) :
    ∀ b y, evAt trT b = some y → y.k = .relXW →
      ∃ a x, evAt trT a = some x ∧ x.k = .acqXR ∧ Lt a b := by
  classical
  intro b y hy hk
  by_cases hm : ∃ q, (evAt trS q).isSome ∧ ψ q = b
  · obtain ⟨q, hq, rfl⟩ := hm
    obtain ⟨xs, hxs⟩ := some_of_isSome hq
    have e := h.ev q xs hxs
    rw [hy] at e; cases e
    obtain ⟨hq1, x0, hx0, hx0k⟩ := shape_relXW h.shape hxs hk
    refine ⟨ψ (q.1, 0), x0, h.ev _ _ hx0, hx0k, h.mono _ _ (by rw [hx0]; rfl) hq ?_⟩
    exact Or.inr ⟨rfl, show 0 < q.2 by omega⟩
  · have hW : y.k.dir = .W := by rw [hk]; rfl
    exact absurd hk (h.priv b y hy hW fun q hq e => hm ⟨q, hq, e⟩).2

end refA

/-! ## The per-item obligation and the run level -/

/-- Runs of a source step relation. -/
inductive SRun {C : Type} (S : C → List Ev → C → Prop) : C → List (List Ev) → C → Prop
  | nil {c} : SRun S c [] c
  | cons {c c' c'' evs tr} : S c evs c' → SRun S c' tr c'' → SRun S c (evs :: tr) c''

/-- **The per-item obligation** (module doc): from related states, every precise Arm run
reaches the end of the item (`n` steps, the source step's events their image, related states
after; with no Arm step only when the measure `μ` decreases), ends inside it (the source step
realized already, or private writes only), or the source has terminated (`Term`). -/
def ItemSim (P : Policy) (f : ArmState → ArmState) (ok : ArmState → Lab → Prop) {C : Type}
    (S : C → List Ev → C → Prop) (Rel : ArmState × Mon → C → Prop) (Term : C → Prop)
    (μ : C → Nat) (Priv : Nat → Prop) : Prop :=
  ∀ t c, Rel t c → ∀ ls t', PRun P f ok t ls t' →
    Term c ∨
    (∃ n evs c' t1 φ, n ≤ ls.length ∧ (0 < n ∨ μ c' < μ c) ∧ S c evs c' ∧
      PRun P f ok t (ls.take n) t1 ∧ Rel t1 c' ∧ Img Priv evs (evTr (ls.take n)) φ) ∨
    (∃ evs c' φ, S c evs c' ∧ Img Priv evs (evTr ls) φ) ∨
    PrivW Priv (evTr ls)

section run
variable {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop} {C : Type}
  {S : C → List Ev → C → Prop} {Rel : ArmState × Mon → C → Prop} {Term : C → Prop}
  {μ : C → Nat} {Priv : Nat → Prop}

theorem take_take_self (ls : List Lab) : ls.take ls.length = ls := List.take_length

theorem refA_run (hsim : ItemSim P f ok S Rel Term μ Priv) :
    ∀ N M (ls : List Lab) t t' c, ls.length ≤ N → μ c ≤ M → PRun P f ok t ls t' → Rel t c →
      ∃ n trS cE ψ, n ≤ ls.length ∧ SRun S c trS cE ∧ RefA Priv trS (evTr (ls.take n)) ψ ∧
        (n = ls.length ∨ Term cE) := by
  intro N
  induction N with
  | zero =>
    intro M
    induction M with
    | zero =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, -, -, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr hT⟩
      · omega
      · have hl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hl
        have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
          rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
        exact ⟨0, [evs], c', _, Nat.le_refl _, .cons hs .nil, by simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩
    | succ M ihM =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr hT⟩
      · have hn0 : n = 0 := by omega
        subst hn0
        have hl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hl
        obtain ⟨n', trS, cE, ψ, hn', hsr, href, hend⟩ :=
          ihM [] t1 t1 c' (by simp) (by omega) .nil hR1
        refine ⟨0, evs :: trS, cE, consMap 0 φ ψ, Nat.le_refl _, .cons hs hsr, ?_, .inl rfl⟩
        have := RefA.cons hi href
        simpa [evTr] using this
      · have hl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hl
        have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
          rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
        exact ⟨0, [evs], c', _, Nat.le_refl _, .cons hs .nil, by simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩
  | succ N ihN =>
    intro M
    induction M with
    | zero =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr hT⟩
      · have hn0 : 0 < n := by omega
        obtain ⟨t1', r1, r2⟩ := PRun.split (ls.take n) (ls.drop n)
          (by rw [List.take_append_drop]; exact hr)
        rw [PRun.det r1 hr1] at r2
        obtain ⟨n', trS, cE, ψ, hn', hsr, href, hend⟩ :=
          ihN (μ c') (ls.drop n) t1 t' c' (by simp; omega) (Nat.le_refl _) r2 hR1
        refine ⟨n + n', evs :: trS, cE, consMap n φ ψ, by simp at hn'; omega, .cons hs hsr,
          ?_, ?_⟩
        · have := RefA.cons hi href
          rw [← evTr_append, evTr_length, List.length_take, Nat.min_eq_left hn] at this
          rwa [show ls.take n ++ (ls.drop n).take n' = ls.take (n + n') by
            rw [List.take_add]] at this
        · rcases hend with h | h
          · left; simp at h; omega
          · exact .inr h
      · exact ⟨ls.length, [evs], c', _, Nat.le_refl _, .cons hs .nil, by
          rw [take_take_self]
          have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
            rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
          simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩
    | succ M ihM =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr hT⟩
      · obtain ⟨t1', r1, r2⟩ := PRun.split (ls.take n) (ls.drop n)
          (by rw [List.take_append_drop]; exact hr)
        rw [PRun.det r1 hr1] at r2
        obtain ⟨n', trS, cE, ψ, hn', hsr, href, hend⟩ : ∃ n' trS cE ψ, n' ≤ (ls.drop n).length ∧
            SRun S c' trS cE ∧ RefA Priv trS (evTr ((ls.drop n).take n')) ψ ∧
            (n' = (ls.drop n).length ∨ Term cE) := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            exact ihM (ls.drop 0) t1 t' c' (by simp; omega) (by omega) r2 hR1
          · exact ihN (μ c') (ls.drop n) t1 t' c' (by simp; omega) (Nat.le_refl _) r2 hR1
        refine ⟨n + n', evs :: trS, cE, consMap n φ ψ, by simp at hn'; omega, .cons hs hsr,
          ?_, ?_⟩
        · have := RefA.cons hi href
          rw [← evTr_append, evTr_length, List.length_take, Nat.min_eq_left hn] at this
          rwa [show ls.take n ++ (ls.drop n).take n' = ls.take (n + n') by
            rw [List.take_add]] at this
        · rcases hend with h | h
          · left; simp at h; omega
          · exact .inr h
      · exact ⟨ls.length, [evs], c', _, Nat.le_refl _, .cons hs .nil, by
          rw [take_take_self]
          have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
            rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
          simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩

/-- **The run level of layer 4b** (module doc): under the per-item obligation `ItemSim`, every
precise Arm run from related states realizes a source run, with `Refines` (equal kinds, private
set `Priv`, atomic updates the Arm trace's monitor pairs), on the prefix of the Arm run up to
the source's termination (all of it when the source does not terminate). -/
theorem refines_of_itemSim (hsim : ItemSim P f ok S Rel Term μ Priv) {ls : List Lab}
    {t t' : ArmState × Mon} {c : C} (hr : PRun P f ok t ls t') (hR : Rel t c) :
    ∃ n trS cE ψ, n ≤ ls.length ∧ SRun S c trS cE ∧
      Refines (· = ·) Priv (MonPair (evTr (ls.take n))) (conv trS) (conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ Term cE) := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refA_run hsim ls.length (μ c) ls t t' c (Nat.le_refl _) (Nat.le_refl _) hr hR
  exact ⟨n, trS, cE, ψ, hn, hs, href.refines, hend⟩

end run

end Concurrency.ArmAllocThread
