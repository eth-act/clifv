module

public import FV.Concurrency.ProgramE2E

@[expose] public section

/-!
# Per-thread refinement with interference: the reduction of `Realizes` (T2h, #311, layer 0)

`ProgE2E.program_correct*` take the program-level contract `Realizes` (the CLIF threads' traces
embed into the Arm threads' traces). This file reduces it to a **per-thread** obligation, the
statement each backend layer has to provide with interference (`docs/plans/atomics.md` §3e):

`Refines MK Priv pairT trS trT ψ` — the source trace `trS` (a thread's steps, each a list of
memory events) is realized by the target trace `trT` through the position map `ψ`
(step, index) ↦ (step, index):

* `ev`: each source event has an image with the same direction, location, size and value, and
  kinds related by `MK` (for CLIF → Arm: Cranelift's table `Maps`);
* `mono`: `ψ` is strictly increasing on the source events (program order is preserved and
  reflected; positions without events are unconstrained);
* `shared`/`priv` (the **footprint guarantee**): the source accesses no private location (a
  fence, direction `.F`, is exempt: it accesses no memory — the Arm `dmb` event sits at address 0
  with size 0 and no bytes — so it cannot touch private data); every
  target write that is no source event's image (spills, saved registers, the frame) writes a
  private location `Priv`. Target reads outside the image (a failed LL/SC iteration's `ldaxr`)
  may read anything;
* `len`/`pair`/`pair_inv`: source steps have at most two events; the two events of an atomic update
  map to a pair of the target's atomic pairs `pairT` (the Arm thread's successful exclusive
  pairs), and those pairs between images come only from atomic updates.

Interference is part of the statement: the target trace is any run of the thread against the
shared memory (`ArmThread.TStep` reads arbitrary values), and the source trace must read the same
values. **`realizes_of_threads`**: if every Arm thread's trace refines (`Refines`) some run of the
CLIF thread from its initial state, with outcomes related by `Obs`, the Arm execution's `rmw` are
the threads' pairs, the CLIF initial locations are a prefix of the Arm ones (the rest private) with
the same initial values, then `Realizes` holds for the CLIF traces assembled from the threads'.
-/

namespace Concurrency.ThreadRefine

open Rel Prog ClifThread ProgE2E

/-! ## Positions of a thread trace -/

/-- The event at a position (step, index) of a thread trace. -/
def evAt {α : Type} (tr : List (List α)) (p : Nat × Nat) : Option α := (tr[p.1]?).bind (·[p.2]?)

/-- The order of positions (lexicographic). -/
def Lt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem Lt.irrefl (p : Nat × Nat) : ¬ Lt p p := by
  rintro (h | ⟨-, h⟩) <;> omega

theorem Lt.asymm {p q : Nat × Nat} (h : Lt p q) : ¬ Lt q p := by
  rcases h with h | ⟨h1, h2⟩ <;> rintro (h' | ⟨h1', h2'⟩) <;> omega

theorem Lt.total {p q : Nat × Nat} (h : p ≠ q) : Lt p q ∨ Lt q p := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [ne_eq, Prod.mk.injEq, not_and] at h
  simp only [Lt]
  omega

theorem po_thr (i j k i' j' k' : Nat) :
    PEv.po (.thr i j k) (.thr i' j' k') ↔ i = i' ∧ Lt (j, k) (j', k') := Iff.rfl

/-! ## The per-thread obligation -/

variable {K K' V : Type}

/-- **The source trace `trS` is realized by the target trace `trT` through `ψ`** (module doc). -/
structure Refines (MK : K → K' → Prop) (Priv : Nat → Prop) (pairT : Nat × Nat → Nat × Nat → Prop)
    (trS : List (List (Ev K V))) (trT : List (List (Ev K' V))) (ψ : Nat × Nat → Nat × Nat) :
    Prop where
  ev : ∀ p x, evAt trS p = some x → ∃ y, evAt trT (ψ p) = some y ∧ MK x.k y.k ∧ y.dir = x.dir ∧
    y.loc = x.loc ∧ y.n = x.n ∧ y.val = x.val
  mono : ∀ p q, (evAt trS p).isSome → (evAt trS q).isSome → Lt p q → Lt (ψ p) (ψ q)
  shared : ∀ p x, evAt trS p = some x → x.dir ≠ .F → ¬ Priv x.loc
  priv : ∀ p y, evAt trT p = some y → y.dir = .W → (∀ q, (evAt trS q).isSome → ψ q ≠ p) →
    Priv y.loc
  len : ∀ j (h : j < trS.length), (trS[j]).length ≤ 2
  pair : ∀ j (h : j < trS.length), (trS[j]).length = 2 → pairT (ψ (j, 0)) (ψ (j, 1))
  pair_inv : ∀ p q, (evAt trS p).isSome → (evAt trS q).isSome → pairT (ψ p) (ψ q) →
    ∃ j, p = (j, 0) ∧ q = (j, 1)

section refines

variable {MK : K → K' → Prop} {Priv : Nat → Prop} {pairT : Nat × Nat → Nat × Nat → Prop}
  {trS : List (List (Ev K V))} {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}

theorem Refines.inj (h : Refines MK Priv pairT trS trT ψ) {p q : Nat × Nat}
    (hp : (evAt trS p).isSome) (hq : (evAt trS q).isSome) (e : ψ p = ψ q) : p = q := by
  refine Classical.byContradiction fun hne => ?_
  rcases Lt.total hne with hl | hl
  · have := h.mono p q hp hq hl; rw [e] at this; exact Lt.irrefl _ this
  · have := h.mono q p hq hp hl; rw [e] at this; exact Lt.irrefl _ this

theorem Refines.lt_iff (h : Refines MK Priv pairT trS trT ψ) {p q : Nat × Nat}
    (hp : (evAt trS p).isSome) (hq : (evAt trS q).isSome) : Lt p q ↔ Lt (ψ p) (ψ q) := by
  refine ⟨h.mono p q hp hq, fun hl => Classical.byContradiction fun hn => ?_⟩
  by_cases e : p = q
  · subst e; exact Lt.irrefl _ hl
  · rcases Lt.total e with h' | h'
    · exact hn h'
    · exact Lt.asymm hl (h.mono q p hq hp h')

end refines

/-! ## Composition of layers -/

theorem evAt_isSome {α : Type} {tr : List (List α)} {j k : Nat} (h : (evAt tr (j, k)).isSome) :
    ∃ hj : j < tr.length, k < (tr[j]).length := by
  unfold evAt at h
  by_cases hj : j < tr.length
  · rw [List.getElem?_eq_getElem hj] at h
    simp only [Option.bind_some] at h
    refine ⟨hj, Classical.byContradiction fun hk => ?_⟩
    rw [List.getElem?_eq_none (by omega)] at h
    simp at h
  · rw [List.getElem?_eq_none (by simp at hj ⊢; omega)] at h
    simp at h

/-- The atomic updates of an intermediate level: its two-event steps. -/
def StepPair {α : Type} (tr : List (List α)) (a b : Nat × Nat) : Prop :=
  ∃ j, a = (j, 0) ∧ b = (j, 1) ∧ ∃ h : j < tr.length, (tr[j]).length = 2

variable {K'' : Type}

theorem Refines.img {MK : K → K' → Prop} {Priv : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : Refines MK Priv pairT trS trT ψ) {p : Nat × Nat} (hp : (evAt trS p).isSome) :
    (evAt trT (ψ p)).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨y, hy, -⟩ := h.ev p x hx
  rw [hy]; rfl

/-- **Layers compose**: a refinement into an intermediate level whose atomic updates are its
two-event steps, followed by a refinement of that level, is a refinement (kinds related through
the intermediate kinds, private locations of both layers). -/
theorem Refines.trans {MK1 : K → K' → Prop} {MK2 : K' → K'' → Prop} {P1 P2 : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trU : List (List (Ev K' V))} {trT : List (List (Ev K'' V))} {ψ1 ψ2 : Nat × Nat → Nat × Nat}
    (h1 : Refines MK1 P1 (StepPair trU) trS trU ψ1) (h2 : Refines MK2 P2 pairT trU trT ψ2) :
    Refines (fun a c => ∃ b, MK1 a b ∧ MK2 b c) (fun l => P1 l ∨ P2 l) pairT trS trT
      (fun p => ψ2 (ψ1 p)) where
  ev p x hx := by
    obtain ⟨u, hu, m1, d1, l1, n1, v1⟩ := h1.ev p x hx
    obtain ⟨y, hy, m2, d2, l2, n2, v2⟩ := h2.ev _ u hu
    exact ⟨y, hy, ⟨u.k, m1, m2⟩, d2.trans d1, l2.trans l1, n2.trans n1, v2.trans v1⟩
  mono p q hp hq hl := h2.mono _ _ (h1.img hp) (h1.img hq) (h1.mono p q hp hq hl)
  shared p x hx hF hP := by
    rcases hP with hP | hP
    · exact h1.shared p x hx hF hP
    · obtain ⟨u, hu, -, d1, hl, -⟩ := h1.ev p x hx
      exact h2.shared _ u hu (by rw [d1]; exact hF) (hl ▸ hP)
  priv p y hy hW hn := by
    by_cases hi : ∃ u, (evAt trU u).isSome ∧ ψ2 u = p
    · obtain ⟨u, hu, rfl⟩ := hi
      obtain ⟨ux, hux⟩ := Option.isSome_iff_exists.mp hu
      obtain ⟨y', hy', -, d2, l2, -⟩ := h2.ev u ux hux
      rw [hy] at hy'
      cases hy'
      refine .inl (l2 ▸ h1.priv u ux hux (d2 ▸ hW) fun q hq e => hn q hq ?_)
      rw [e]
    · exact .inr (h2.priv p y hy hW fun u hu e => hi ⟨u, hu, e⟩)
  len := h1.len
  pair j hj h2' := by
    obtain ⟨jj, e0, e1, hjj, hl⟩ := h1.pair j hj h2'
    show pairT (ψ2 (ψ1 (j, 0))) (ψ2 (ψ1 (j, 1)))
    rw [e0, e1]
    exact h2.pair jj hjj hl
  pair_inv p q hp hq hpr := by
    obtain ⟨jj, e0, e1⟩ := h2.pair_inv _ _ (h1.img hp) (h1.img hq) hpr
    have hqU := h1.img hq
    rw [e1] at hqU
    obtain ⟨hjj, hk⟩ := evAt_isSome hqU
    exact h1.pair_inv p q hp hq
      ⟨jj, e0, e1, hjj, Nat.le_antisymm (h2.len jj hjj) hk⟩

/-! ## Assembling the threads: `Realizes` -/

theorem evAt_thr_lt {σ K V : Type} {P : Traces σ K V} {i : Nat} (h : i < P.n) (j k : Nat) :
    P.evAt (.thr i j k) = evAt (P.tr i) (j, k) := by
  simp [Traces.evAt, h, evAt]

theorem evAt_thr_ge {σ K V : Type} {P : Traces σ K V} {i : Nat} (h : ¬ i < P.n) (j k : Nat) :
    P.evAt (.thr i j k) = none := by
  simp [Traces.evAt, h]

theorem getElem?_prefix {α : Type} {l l' : List α} (h : l <+: l') {q : Nat} (hq : q < l.length) :
    l'[q]? = l[q]? := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hq]

/-- **Reduction of the program-level contract to per-thread refinements** (module doc). -/
theorem realizes_of_threads {T : TSem TState SKind BVal} {PA : Traces AState AKind BVal}
    {locsA locsC : List (Nat × Nat)} {MA0 MC0 : Bytes} {rfA coA rmwA : Rel PEv}
    {s0 : Nat → TState} {Priv : Nat → Prop} {pairT : Nat → Nat × Nat → Nat × Nat → Prop}
    {Obs : Nat → AState → TState → Prop}
    (hwf : (PA.exec locsA rfA coA rmwA).Wf)
    (hrmw : ∀ i < PA.n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔ pairT i a b)
    (hlocs : locsC <+: locsA)
    (hpriv0 : ∀ q (h : q < locsA.length), locsC.length ≤ q → Priv (locsA[q]).1)
    (hval0 : ∀ q (h : q < locsC.length),
      bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2)
    (hthr : ∀ i < PA.n, ∃ (trS : List (List (Ev SKind BVal))) (stS : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), stS 0 = s0 i ∧
      (∀ j (h : j < trS.length), T (stS j) trS[j] (stS (j + 1))) ∧
      Refines Maps Priv (pairT i) trS (PA.tr i) ψ ∧
      Obs i (PA.st i (PA.tr i).length) (stS trS.length)) :
    ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = PA.n ∧ (∀ i, PC.st i 0 = s0 i) ∧
      PC.Runs T ∧ Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ Obs := by
  classical
  have hthr' : ∀ i (h : i < PA.n), ∃ c : List (List (Ev SKind BVal)) × (Nat → TState) ×
      (Nat × Nat → Nat × Nat), c.2.1 0 = s0 i ∧
      (∀ j (hj : j < c.1.length), T (c.2.1 j) c.1[j] (c.2.1 (j + 1))) ∧
      Refines Maps Priv (pairT i) c.1 (PA.tr i) c.2.2 ∧
      Obs i (PA.st i (PA.tr i).length) (c.2.1 c.1.length) := by
    intro i h
    obtain ⟨trS, stS, ψ, h1, h2, h3, h4⟩ := hthr i h
    exact ⟨(trS, stS, ψ), h1, h2, h3, h4⟩
  let trS : (i : Nat) → i < PA.n → List (List (Ev SKind BVal)) := fun i h =>
    (Classical.choose (hthr' i h)).1
  let stS : (i : Nat) → i < PA.n → Nat → TState := fun i h => (Classical.choose (hthr' i h)).2.1
  let ψ : (i : Nat) → i < PA.n → Nat × Nat → Nat × Nat := fun i h =>
    (Classical.choose (hthr' i h)).2.2
  have h0 : ∀ i (h : i < PA.n), stS i h 0 = s0 i := fun i h => (Classical.choose_spec (hthr' i h)).1
  have hrun : ∀ i (h : i < PA.n) j (hj : j < (trS i h).length),
      T (stS i h j) (trS i h)[j] (stS i h (j + 1)) := fun i h =>
    (Classical.choose_spec (hthr' i h)).2.1
  have href : ∀ i (h : i < PA.n), Refines Maps Priv (pairT i) (trS i h) (PA.tr i) (ψ i h) :=
    fun i h => (Classical.choose_spec (hthr' i h)).2.2.1
  have hobs : ∀ i (h : i < PA.n), Obs i (PA.st i (PA.tr i).length) (stS i h (trS i h).length) :=
    fun i h => (Classical.choose_spec (hthr' i h)).2.2.2
  let tr : Nat → List (List (Ev SKind BVal)) := fun i => if h : i < PA.n then trS i h else []
  let st : Nat → Nat → TState := fun i j => if h : i < PA.n then stS i h j else s0 i
  let PC : Traces TState SKind BVal := ⟨PA.n, tr, st⟩
  let φ : PEv → PEv := fun e => match e with
    | .init q => .init q
    | .thr i j k => if h : i < PA.n then .thr i (ψ i h (j, k)).1 (ψ i h (j, k)).2 else .thr i j k
  have htr : ∀ i (h : i < PA.n), tr i = trS i h := fun i h => by simp [tr, h]
  have hst : ∀ i (h : i < PA.n) j, st i j = stS i h j := fun i h j => by simp [st, h]
  have hφ : ∀ i (h : i < PA.n) j k,
      φ (.thr i j k) = .thr i (ψ i h (j, k)).1 (ψ i h (j, k)).2 := fun i h j k => by simp [φ, h]
  have hevC : ∀ i (h : i < PA.n) j k, PC.evAt (.thr i j k) = evAt (trS i h) (j, k) :=
    fun i h j k => by rw [evAt_thr_lt (P := PC) h, show PC.tr i = tr i from rfl, htr i h]
  -- a valid CLIF thread event: its thread, its event, its image
  have hvalid : ∀ i j k, Valid PC locsC (.thr i j k) →
      ∃ (h : i < PA.n) (x : Ev SKind BVal), evAt (trS i h) (j, k) = some x := by
    intro i j k hv
    by_cases h : i < PA.n
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (show (PC.evAt (.thr i j k)).isSome from hv)
      exact ⟨h, x, by rw [← hevC i h]; exact hx⟩
    · have : PC.evAt (.thr i j k) = none := evAt_thr_ge (P := PC) h j k
      simp [Valid, this] at hv
  have himg : ∀ i (h : i < PA.n) j k x, evAt (trS i h) (j, k) = some x →
      ∃ y, PA.evAt (φ (.thr i j k)) = some y ∧ Maps x.k y.k ∧ y.dir = x.dir ∧ y.loc = x.loc ∧
        y.n = x.n ∧ y.val = x.val := by
    intro i h j k x hx
    obtain ⟨y, hy, hrest⟩ := (href i h).ev _ x hx
    exact ⟨y, by rw [hφ i h, evAt_thr_lt h]; exact hy, hrest⟩
  have hinit : ∀ q, q < locsC.length → locsA[q]? = locsC[q]? := fun q hq =>
    getElem?_prefix hlocs hq
  have hlen : locsC.length ≤ locsA.length := hlocs.length_le
  refine ⟨PC, φ, rfl, fun i => ?_, ?_, ?_⟩
  · by_cases h : i < PA.n
    · show st i 0 = s0 i
      rw [hst i h]; exact h0 i h
    · show st i 0 = s0 i
      simp [st, h]
  · intro i hi j hj
    show T (st i j) ((tr i)[j]) (st i (j + 1))
    have hj' : j < (trS i hi).length := by rw [← htr i hi]; exact hj
    rw [hst i hi, hst i hi]
    simp only [htr i hi]
    exact hrun i hi j hj'
  -- the data of a valid CLIF thread event and of its image
  have hdata : ∀ i j k, Valid PC locsC (.thr i j k) → ∃ (h : i < PA.n) (x : Ev SKind BVal)
      (y : Ev AKind BVal), evAt (trS i h) (j, k) = some x ∧ PC.evAt (.thr i j k) = some x ∧
      PA.evAt (.thr i (ψ i h (j, k)).1 (ψ i h (j, k)).2) = some y ∧ Maps x.k y.k ∧
      y.dir = x.dir ∧ y.loc = x.loc ∧ y.n = x.n ∧ y.val = x.val := by
    intro i j k hv
    obtain ⟨h, x, hx⟩ := hvalid i j k hv
    obtain ⟨y, hy, hrest⟩ := himg i h j k x hx
    rw [hφ i h] at hy
    exact ⟨h, x, y, hx, by rw [hevC i h]; exact hx, hy, hrest⟩
  have hinitW : ∀ q, q < locsA.length → (PA.exec locsA rfA coA rmwA).dir (.init q) = .W :=
    fun q hq => by simp [Traces.exec, hq]
  refine
    { threads := rfl
      valid := ?_, inj := ?_, po := ?_, init := fun q _ => ⟨q, rfl⟩, dir := ?_, loc := ?_,
      sz := ?_, val := ?_, kind := ?_, rf_src := ?_, shape := ?_, obs := ?_ }
  · -- valid
    intro e he
    cases e with
    | init q => exact show q < locsA.length from Nat.lt_of_lt_of_le he hlen
    | thr i j k =>
      obtain ⟨h, x, y, -, -, hy, -⟩ := hdata i j k he
      rw [hφ i h]
      show (PA.evAt _).isSome
      rw [hy]; rfl
  · -- inj
    intro a b ha hb e
    cases a with
    | init q =>
      cases b with
      | init q' => exact e
      | thr i j k =>
        obtain ⟨h, -⟩ := hvalid i j k hb
        have e' : PEv.init q = φ (.thr i j k) := e
        rw [hφ i h] at e'; cases e'
    | thr i j k =>
      obtain ⟨h, x, hx⟩ := hvalid i j k ha
      cases b with
      | init q' =>
        have e' : φ (.thr i j k) = PEv.init q' := e
        rw [hφ i h] at e'; cases e'
      | thr i' j' k' =>
        obtain ⟨h', x', hx'⟩ := hvalid i' j' k' hb
        have e' : φ (.thr i j k) = φ (.thr i' j' k') := e
        rw [hφ i h, hφ i' h'] at e'
        simp only [PEv.thr.injEq] at e'
        obtain ⟨rfl, e1, e2⟩ := e'
        have := (href i h).inj (p := (j, k)) (q := (j', k')) (by rw [hx]; rfl) (by rw [hx']; rfl)
          (Prod.ext e1 e2)
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2]
  · -- po
    intro a b ha hb
    cases a with
    | init q =>
      cases b with
      | init q' => exact Iff.rfl
      | thr i j k =>
        obtain ⟨h, -⟩ := hvalid i j k hb
        show PEv.po _ _ ↔ PEv.po _ (φ (.thr i j k))
        rw [hφ i h]; exact Iff.rfl
    | thr i j k =>
      obtain ⟨h, x, hx⟩ := hvalid i j k ha
      cases b with
      | init q' =>
        show PEv.po _ _ ↔ PEv.po (φ (.thr i j k)) _
        rw [hφ i h]; exact Iff.rfl
      | thr i' j' k' =>
        obtain ⟨h', x', hx'⟩ := hvalid i' j' k' hb
        show PEv.po _ _ ↔ PEv.po (φ (.thr i j k)) (φ (.thr i' j' k'))
        rw [hφ i h, hφ i' h', po_thr, po_thr]
        constructor
        · rintro ⟨rfl, hl⟩
          exact ⟨rfl, ((href i h).lt_iff (by rw [hx]; rfl) (by rw [hx']; rfl)).mp hl⟩
        · rintro ⟨rfl, hl⟩
          exact ⟨rfl, ((href i h).lt_iff (by rw [hx]; rfl) (by rw [hx']; rfl)).mpr hl⟩
  · -- dir
    intro e he
    cases e with
    | init q =>
      have hq : q < locsC.length := he
      show (PA.exec locsA rfA coA rmwA).dir (.init q) = (PC.exec locsC rfA coA rmwA).dir (.init q)
      simp [Traces.exec, hq, Nat.lt_of_lt_of_le hq hlen]
    | thr i j k =>
      obtain ⟨h, x, y, -, hx, hy, -, hd, -⟩ := hdata i j k he
      show (PA.exec locsA rfA coA rmwA).dir (φ (.thr i j k)) = _
      rw [hφ i h]
      simp only [Traces.exec, hx, hy, hd]
  · -- loc
    intro e he
    cases e with
    | init q =>
      have hq : q < locsC.length := he
      show (PA.exec locsA rfA coA rmwA).loc (.init q) = (PC.exec locsC rfA coA rmwA).loc (.init q)
      simp only [Traces.exec]; rw [hinit q hq]
    | thr i j k =>
      obtain ⟨h, x, y, -, hx, hy, -, -, hl, -⟩ := hdata i j k he
      show (PA.exec locsA rfA coA rmwA).loc (φ (.thr i j k)) = _
      rw [hφ i h]
      simp only [Traces.exec, hx, hy, hl]
  · -- sz
    intro e he
    cases e with
    | init q =>
      have hq : q < locsC.length := he
      show PA.sz locsA (.init q) = PC.sz locsC (.init q)
      simp only [Traces.sz]; rw [hinit q hq]
    | thr i j k =>
      obtain ⟨h, x, y, -, hx, hy, -, -, -, hn, -⟩ := hdata i j k he
      show PA.sz locsA (φ (.thr i j k)) = _
      rw [hφ i h]
      simp only [Traces.sz, hx, hy, hn]
  · -- val
    intro e he
    cases e with
    | init q =>
      have hq : q < locsC.length := he
      show PA.val bytesI MA0 locsA [] (.init q) = PC.val bytesI MC0 locsC [] (.init q)
      simp only [Traces.val]; rw [hinit q hq, List.getElem?_eq_getElem hq]
      exact hval0 q hq
    | thr i j k =>
      obtain ⟨h, x, y, -, hx, hy, -, -, -, -, hv⟩ := hdata i j k he
      show PA.val bytesI MA0 locsA [] (φ (.thr i j k)) = _
      rw [hφ i h]
      simp only [Traces.val, hx, hy, hv]
  · -- kind
    intro e he
    cases e with
    | init q => simp [kindC, kindA, Traces.evAt, Maps, φ]
    | thr i j k =>
      obtain ⟨h, x, y, -, hx, hy, hm, -⟩ := hdata i j k he
      show Maps (kindC PC (.thr i j k)) (kindA PA (φ (.thr i j k)))
      rw [hφ i h]
      simp only [kindC, kindA, hx, hy]; exact hm
  · -- rf_src
    intro w e he hrf
    have hdR := (hwf.rf_dir _ _ hrf)
    have hloc := hwf.rf_loc _ _ hrf
    cases e with
    | init q =>
      have : (PA.exec locsA rfA coA rmwA).dir (φ (.init q)) = .W :=
        hinitW q (Nat.lt_of_lt_of_le (show q < locsC.length from he) hlen)
      rw [this] at hdR; exact absurd hdR.2 (by decide)
    | thr i j k =>
      obtain ⟨h, x, y, hxS, -, hy, -, hd, hl, -⟩ := hdata i j k he
      have hxF : x.dir ≠ .F := by
        have hR := hdR.2
        rw [hφ i h] at hR
        simp only [Traces.exec, hy] at hR
        rw [← hd, hR]; decide
      have hsh := (href i h).shared _ x hxS hxF
      have hlocE : (PA.exec locsA rfA coA rmwA).loc (φ (.thr i j k)) = x.loc := by
        rw [hφ i h]; simp only [Traces.exec, hy, hl]
      rw [hlocE] at hloc
      cases w with
      | init q =>
        by_cases hq : q < locsC.length
        · exact ⟨.init q, hq, rfl⟩
        · exfalso
          have hqA : q < locsA.length := by
            refine Classical.byContradiction fun hqA => ?_
            have := hdR.1
            simp [Traces.exec, hqA] at this
          have hp := hpriv0 q hqA (by omega)
          have : (PA.exec locsA rfA coA rmwA).loc (.init q) = (locsA[q]).1 := by
            simp [Traces.exec, List.getElem?_eq_getElem hqA]
          rw [this] at hloc
          exact hsh (hloc ▸ hp)
      | thr i2 j2 k2 =>
        rcases hy2 : PA.evAt (.thr i2 j2 k2) with _ | y2
        · have := hdR.1
          simp [Traces.exec, hy2] at this
        · have h2 : i2 < PA.n := by
            refine Classical.byContradiction fun h2 => ?_
            rw [evAt_thr_ge h2] at hy2; cases hy2
          have hy2' : evAt (PA.tr i2) (j2, k2) = some y2 := by rw [← evAt_thr_lt h2]; exact hy2
          have hdW : y2.dir = .W := by
            have := hdR.1
            simp only [Traces.exec, hy2] at this; exact this
          by_cases himg2 : ∃ q, (evAt (trS i2 h2) q).isSome ∧ ψ i2 h2 q = (j2, k2)
          · obtain ⟨q, hq, hψ⟩ := himg2
            refine ⟨.thr i2 q.1 q.2, ?_, ?_⟩
            · show (PC.evAt _).isSome
              rw [hevC i2 h2]; exact hq
            · rw [hφ i2 h2, hψ]
          · exfalso
            have hp := (href i2 h2).priv _ y2 hy2' hdW (fun q hq e => himg2 ⟨q, hq, e⟩)
            have : (PA.exec locsA rfA coA rmwA).loc (.thr i2 j2 k2) = y2.loc := by
              simp only [Traces.exec, hy2]
            rw [this] at hloc
            exact hsh (hloc ▸ hp)
  · -- shape
    refine ⟨fun i hi j hj => ?_, fun a b hab => ?_⟩
    · have hi' : i < PA.n := hi
      have hj' : j < (trS i hi').length := by
        have e : PC.tr i = trS i hi' := htr i hi'
        rw [← e]; exact hj
      have hx : (PC.tr i)[j] = (trS i hi')[j] := by
        simp only [show PC.tr i = tr i from rfl, tr, hi', dite_true]
      rw [hx]
      rcases Nat.lt_or_ge ((trS i hi')[j]).length 2 with hl | hl
      · exact .inl (by omega)
      · have h2 : ((trS i hi')[j]).length = 2 := Nat.le_antisymm ((href i hi').len j hj') hl
        refine .inr ⟨h2, ?_, ?_, ?_⟩
        · show (PC.evAt _).isSome
          rw [hevC i hi']; simp [evAt, List.getElem?_eq_getElem hj', h2]
        · show (PC.evAt _).isSome
          rw [hevC i hi']; simp [evAt, List.getElem?_eq_getElem hj', h2]
        · rw [hφ i hi', hφ i hi']
          exact (hrmw i hi' _ _).mpr ((href i hi').pair j hj' h2)
    · obtain ⟨ha, hb, hr⟩ := hab
      have hpo := hwf.rmw_po _ _ hr
      have hdir := hwf.rmw_dir _ _ hr
      cases a with
      | init q =>
        exfalso
        have : (PA.exec locsA rfA coA rmwA).dir (φ (.init q)) = .W :=
          hinitW q (Nat.lt_of_lt_of_le (show q < locsC.length from ha) hlen)
        rw [this] at hdir; exact absurd hdir.1 (by decide)
      | thr i j k =>
        obtain ⟨h, x, hx⟩ := hvalid i j k ha
        cases b with
        | init q =>
          exfalso
          have hpo' : PEv.po (φ (.thr i j k)) (φ (.init q)) := hpo
          rw [hφ i h] at hpo'; exact hpo'
        | thr i' j' k' =>
          obtain ⟨h', x', hx'⟩ := hvalid i' j' k' hb
          have hpo' : PEv.po (φ (.thr i j k)) (φ (.thr i' j' k')) := hpo
          rw [hφ i h, hφ i' h', po_thr] at hpo'
          obtain ⟨rfl, -⟩ := hpo'
          have hr' : rmwA (.thr i (ψ i h (j, k)).1 (ψ i h (j, k)).2)
              (.thr i (ψ i h (j', k')).1 (ψ i h (j', k')).2) := by
            rw [← hφ i h, ← hφ i h]; exact hr
          have hp := (hrmw i h _ _).mp hr'
          obtain ⟨jj, e1, e2⟩ := (href i h).pair_inv (j, k) (j', k') (by rw [hx]; rfl)
            (by rw [hx']; rfl) hp
          simp only [Prod.mk.injEq] at e1 e2
          exact ⟨i, jj, by rw [e1.1, e1.2], by rw [e2.1, e2.2]⟩
  · -- obs
    intro i hi
    have hi' : i < PA.n := hi
    show Obs i _ (st i (tr i).length)
    rw [hst i hi', htr i hi']
    exact hobs i hi'

end Concurrency.ThreadRefine
