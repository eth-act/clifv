module

public import FV.Concurrency.PrivCoh

@[expose] public section

/-!
# Per-thread refinements with time-varying private sets (#473, (iv))

`ThreadRefine.Refines` fixes one private set per thread for the whole run. A thread whose calls
reuse the stack needs a private set that varies along the run: an address that is a callee's spill
slot (an unmatched Arm write: private) is, after the callee returned, another callee's CLIF stack
slot (CLIF events: shared). **`RefinesT MK Priv0 PrivAt`** is `Refines` with a private set
`PrivAt q` per position `q` of the Arm trace and the locations `Priv0` private at the start:

* `shared`: a source event other than a fence avoids the private set at its image's position;
* `priv`: an unmatched Arm write is in the private set at its position;
* `fresh0`/`fresh` (**freshness**): a source read of a location private at the start, or of a
  location an unmatched Arm write wrote before, follows a source write there (after that Arm
  write) — the location was reinitialised by the CLIF thread before it reads it (for CLIF threads
  `ClifThreadI.CStepI`'s mask: a read of an uninitialised slot byte is stuck).

`Refines.toT`: a `Refines` is a `RefinesT` with the constant private set.

**`realizes_of_threads_privT`**: the reduction of the program-level contract to per-thread
`RefinesT` refinements. Its program premises beyond `realizes_of_threads_priv`'s: the Arm
execution is SC per location (`acyclic(po-loc ∪ com)`, Armv8's `internal` axiom) with its
initial writes `co`-first, and the trusted cross-thread premise **`StackDisjoint`**: no thread's
events touch the union over time of another thread's private sets (its stack). The proof: a source
read's Arm `rf` source is an image or a CLIF initial write (`src_of_refinesT`): another thread's
unmatched write is excluded by `StackDisjoint`, an own unmatched write (or an initial write of a
location private at the start) by freshness and coherence (the reinitialising write is `co`-after
it and `po`-before the read). `realizes_of_threads_fn`: `ThreadRefine.realizes_of_threads` with
the threads' runs given as functions and the source property as a premise.
-/

namespace Concurrency.PrivCohT

open Rel Prog ClifThread ProgE2E ThreadRefine PrivCoh

variable {K K' V : Type}

/-- The order- and pair-preserving part of `Refines`. -/
structure RefinesC (MK : K → K' → Prop) (pairT : Nat × Nat → Nat × Nat → Prop)
    (trS : List (List (Ev K V))) (trT : List (List (Ev K' V))) (ψ : Nat × Nat → Nat × Nat) :
    Prop where
  ev : ∀ p x, evAt trS p = some x → ∃ y, evAt trT (ψ p) = some y ∧ MK x.k y.k ∧ y.dir = x.dir ∧
    y.loc = x.loc ∧ y.n = x.n ∧ y.val = x.val
  mono : ∀ p q, (evAt trS p).isSome → (evAt trS q).isSome → Lt p q → Lt (ψ p) (ψ q)
  len : ∀ j (h : j < trS.length), (trS[j]).length ≤ 2
  pair : ∀ j (h : j < trS.length), (trS[j]).length = 2 → pairT (ψ (j, 0)) (ψ (j, 1))
  pair_inv : ∀ p q, (evAt trS p).isSome → (evAt trS q).isSome → pairT (ψ p) (ψ q) →
    ∃ j, p = (j, 0) ∧ q = (j, 1)

/-- No source event maps to the target position `q`. -/
def Unmatched (trS : List (List (Ev K V))) (ψ : Nat × Nat → Nat × Nat) (q : Nat × Nat) : Prop :=
  ∀ p, (evAt trS p).isSome → ψ p ≠ q

/-- **The source trace `trS` is realized by `trT` with time-varying private sets** (module doc). -/
structure RefinesT (MK : K → K' → Prop) (Priv0 : Nat → Prop) (PrivAt : Nat × Nat → Nat → Prop)
    (pairT : Nat × Nat → Nat × Nat → Prop) (trS : List (List (Ev K V)))
    (trT : List (List (Ev K' V))) (ψ : Nat × Nat → Nat × Nat) : Prop
    extends RefinesC MK pairT trS trT ψ where
  shared : ∀ p x, evAt trS p = some x → x.dir ≠ .F → ¬ PrivAt (ψ p) x.loc
  priv : ∀ p y, evAt trT p = some y → y.dir = .W → Unmatched trS ψ p → PrivAt p y.loc
  fresh0 : ∀ p x, evAt trS p = some x → x.dir = .R → Priv0 x.loc →
    ∃ q x', evAt trS q = some x' ∧ x'.dir = .W ∧ x'.loc = x.loc ∧ Lt (ψ q) (ψ p)
  fresh : ∀ p x, evAt trS p = some x → x.dir = .R → ∀ q y, evAt trT q = some y → y.dir = .W →
    y.loc = x.loc → Lt q (ψ p) → Unmatched trS ψ q →
    ∃ q' x', evAt trS q' = some x' ∧ x'.dir = .W ∧ x'.loc = x.loc ∧ Lt q (ψ q') ∧ Lt (ψ q') (ψ p)

/-- **A `Refines` is a `RefinesT`** with the constant private set (private at the start too). -/
theorem Refines.toT {MK : K → K' → Prop} {Priv : Nat → Prop} {pairT : Nat × Nat → Nat × Nat → Prop}
    {trS : List (List (Ev K V))} {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : Refines MK Priv pairT trS trT ψ) : RefinesT MK Priv (fun _ => Priv) pairT trS trT ψ where
  ev := h.ev
  mono := h.mono
  len := h.len
  pair := h.pair
  pair_inv := h.pair_inv
  shared := h.shared
  priv := h.priv
  fresh0 p x hx hR hP := absurd hP (h.shared p x hx (by rw [hR]; decide))
  fresh p x hx hR q y hy hW hl _ hu :=
    absurd (hl ▸ h.priv q y hy hW hu) (h.shared p x hx (by rw [hR]; decide))

theorem RefinesC.inj {MK : K → K' → Prop} {pairT : Nat × Nat → Nat × Nat → Prop}
    {trS : List (List (Ev K V))} {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : RefinesC MK pairT trS trT ψ) {p q : Nat × Nat}
    (hp : (evAt trS p).isSome) (hq : (evAt trS q).isSome) (e : ψ p = ψ q) : p = q := by
  refine Classical.byContradiction fun hne => ?_
  rcases Lt.total hne with hl | hl
  · have := h.mono p q hp hq hl; rw [e] at this; exact Lt.irrefl _ this
  · have := h.mono q p hq hp hl; rw [e] at this; exact Lt.irrefl _ this

theorem RefinesC.lt_iff {MK : K → K' → Prop} {pairT : Nat × Nat → Nat × Nat → Prop}
    {trS : List (List (Ev K V))} {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : RefinesC MK pairT trS trT ψ) {p q : Nat × Nat}
    (hp : (evAt trS p).isSome) (hq : (evAt trS q).isSome) : Lt p q ↔ Lt (ψ p) (ψ q) := by
  refine ⟨h.mono p q hp hq, fun hl => Classical.byContradiction fun hn => ?_⟩
  by_cases e : p = q
  · subst e; exact Lt.irrefl _ hl
  · rcases Lt.total e with h' | h'
    · exact hn h'
    · exact Lt.asymm hl (h.mono q p hq hp h')

/-- **`realizes_of_threads` with the threads' runs given as functions** and the source property
as a premise: every Arm `rf` source of a source read's image is a CLIF initial write or the image
of a source event. -/
theorem realizes_of_threads_fn {T : TSem TState SKind BVal} {PA : Traces AState AKind BVal}
    {locsA locsC : List (Nat × Nat)} {MA0 MC0 : Bytes} {rfA coA rmwA : Rel PEv}
    {s0 : Nat → TState} {pairT : Nat → Nat × Nat → Nat × Nat → Prop}
    {Obs : Nat → AState → TState → Prop}
    (trS : Nat → List (List (Ev SKind BVal))) (stS : Nat → Nat → TState)
    (ψ : Nat → Nat × Nat → Nat × Nat)
    (hwf : (PA.exec locsA rfA coA rmwA).Wf)
    (hrmw : ∀ i < PA.n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔ pairT i a b)
    (hlocs : locsC <+: locsA)
    (hval0 : ∀ q (h : q < locsC.length),
      bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2)
    (h0 : ∀ i < PA.n, stS i 0 = s0 i)
    (hrun : ∀ i < PA.n, ∀ j (h : j < (trS i).length), T (stS i j) (trS i)[j] (stS i (j + 1)))
    (href : ∀ i < PA.n, RefinesC Maps (pairT i) (trS i) (PA.tr i) (ψ i))
    (hobs : ∀ i < PA.n, Obs i (PA.st i (PA.tr i).length) (stS i (trS i).length))
    (hsrc : ∀ i < PA.n, ∀ p x, evAt (trS i) p = some x → ∀ w, rfA w (.thr i (ψ i p).1 (ψ i p).2) →
      (∃ q, w = .init q ∧ q < locsC.length) ∨
      ∃ i2 < PA.n, ∃ q, (evAt (trS i2) q).isSome ∧ w = .thr i2 (ψ i2 q).1 (ψ i2 q).2) :
    ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = PA.n ∧ (∀ i, PC.st i 0 = s0 i) ∧
      PC.Runs T ∧ Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ Obs := by
  classical
  let tr : Nat → List (List (Ev SKind BVal)) := fun i => if h : i < PA.n then trS i else []
  let st : Nat → Nat → TState := fun i j => if h : i < PA.n then stS i j else s0 i
  let PC : Traces TState SKind BVal := ⟨PA.n, tr, st⟩
  let φ : PEv → PEv := fun e => match e with
    | .init q => .init q
    | .thr i j k => if h : i < PA.n then .thr i (ψ i (j, k)).1 (ψ i (j, k)).2 else .thr i j k
  have htr : ∀ i (h : i < PA.n), tr i = trS i := fun i h => by simp [tr, h]
  have hst : ∀ i (h : i < PA.n) j, st i j = stS i j := fun i h j => by simp [st, h]
  have hφ : ∀ i (h : i < PA.n) j k,
      φ (.thr i j k) = .thr i (ψ i (j, k)).1 (ψ i (j, k)).2 := fun i h j k => by simp [φ, h]
  have hevC : ∀ i (h : i < PA.n) j k, PC.evAt (.thr i j k) = evAt (trS i) (j, k) :=
    fun i h j k => by rw [evAt_thr_lt (P := PC) h, show PC.tr i = tr i from rfl, htr i h]
  -- a valid CLIF thread event: its thread, its event, its image
  have hvalid : ∀ i j k, Valid PC locsC (.thr i j k) →
      ∃ (h : i < PA.n) (x : Ev SKind BVal), evAt (trS i) (j, k) = some x := by
    intro i j k hv
    by_cases h : i < PA.n
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (show (PC.evAt (.thr i j k)).isSome from hv)
      exact ⟨h, x, by rw [← hevC i h]; exact hx⟩
    · have : PC.evAt (.thr i j k) = none := evAt_thr_ge (P := PC) h j k
      simp [Valid, this] at hv
  have himg : ∀ i (h : i < PA.n) j k x, evAt (trS i) (j, k) = some x →
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
    have hj' : j < (trS i).length := by rw [← htr i hi]; exact hj
    rw [hst i hi, hst i hi]
    simp only [htr i hi]
    exact hrun i hi j hj'
  -- the data of a valid CLIF thread event and of its image
  have hdata : ∀ i j k, Valid PC locsC (.thr i j k) → ∃ (h : i < PA.n) (x : Ev SKind BVal)
      (y : Ev AKind BVal), evAt (trS i) (j, k) = some x ∧ PC.evAt (.thr i j k) = some x ∧
      PA.evAt (.thr i (ψ i (j, k)).1 (ψ i (j, k)).2) = some y ∧ Maps x.k y.k ∧
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
        rw [hφ i h, hφ i' h', ThreadRefine.po_thr, ThreadRefine.po_thr]
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
    cases e with
    | init q =>
      have hdR := (hwf.rf_dir _ _ hrf)
      have : (PA.exec locsA rfA coA rmwA).dir (φ (.init q)) = .W :=
        hinitW q (Nat.lt_of_lt_of_le (show q < locsC.length from he) hlen)
      rw [this] at hdR; exact absurd hdR.2 (by decide)
    | thr i j k =>
      obtain ⟨h, x, hxS⟩ := hvalid i j k he
      have hrf' : rfA w (.thr i (ψ i (j, k)).1 (ψ i (j, k)).2) := by rw [← hφ i h]; exact hrf
      rcases hsrc i h (j, k) x hxS w hrf' with ⟨q, rfl, hq⟩ | ⟨i2, h2, q, hq, rfl⟩
      · exact ⟨.init q, hq, rfl⟩
      · refine ⟨.thr i2 q.1 q.2, ?_, ?_⟩
        · show (PC.evAt _).isSome
          rw [hevC i2 h2]; exact hq
        · rw [hφ i2 h2]
  · -- shape
    refine ⟨fun i hi j hj => ?_, fun a b hab => ?_⟩
    · have hi' : i < PA.n := hi
      have hj' : j < (trS i).length := by
        have e : PC.tr i = trS i := htr i hi'
        rw [← e]; exact hj
      have hx : (PC.tr i)[j] = (trS i)[j] := by
        simp only [show PC.tr i = tr i from rfl, tr, hi', dite_true]
      rw [hx]
      rcases Nat.lt_or_ge ((trS i)[j]).length 2 with hl | hl
      · exact .inl (by omega)
      · have h2 : ((trS i)[j]).length = 2 := Nat.le_antisymm ((href i hi').len j hj') hl
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
          rw [hφ i h, hφ i' h', ThreadRefine.po_thr] at hpo'
          obtain ⟨rfl, -⟩ := hpo'
          have hr' : rmwA (.thr i (ψ i (j, k)).1 (ψ i (j, k)).2)
              (.thr i (ψ i (j', k')).1 (ψ i (j', k')).2) := by
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
/-! ## Time-varying private sets -/

/-- **The cross-thread premise** (trusted; a program premise beside the race freedom of the
programs, `docs/contracts`): no thread's events other than fences touch the locations `U j` of
another thread `j` — for `U = PrivU …`, the union over time of `j`'s private sets, its stack. -/
def StackDisjoint {σ : Type} (PA : Traces σ AKind BVal) (U : Nat → Nat → Prop) : Prop :=
  ∀ i < PA.n, ∀ j < PA.n, j ≠ i → ∀ q x, evAt (PA.tr i) q = some x → x.dir ≠ .F → ¬ U j x.loc

/-- The union over time of thread `j`'s private sets (and its locations private at the start). -/
def PrivU (Priv0 : Nat → Nat → Prop) (PrivAt : Nat → Nat × Nat → Nat → Prop) (j l : Nat) : Prop :=
  Priv0 j l ∨ ∃ q, PrivAt j q l

/-- **The Arm `rf` sources of a source read are CLIF initial writes or images** (module doc). -/
theorem src_of_refinesT {PA : Traces AState AKind BVal} {locsA locsC : List (Nat × Nat)}
    {rfA coA rmwA : Rel PEv} {Priv0 : Nat → Nat → Prop} {PrivAt : Nat → Nat × Nat → Nat → Prop}
    {pairT : Nat → Nat × Nat → Nat × Nat → Prop} {trS : Nat → List (List (Ev SKind BVal))}
    {ψ : Nat → Nat × Nat → Nat × Nat}
    (hwf : (PA.exec locsA rfA coA rmwA).Wf)
    (hint : Acyclic (union (PA.exec locsA rfA coA rmwA).poLoc (PA.exec locsA rfA coA rmwA).com))
    (hinit : InitFirst (PA.exec locsA rfA coA rmwA))
    (hpriv0 : ∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < PA.n, Priv0 j (locsA[q]).1)
    (hcross : StackDisjoint PA (PrivU Priv0 PrivAt))
    (href : ∀ i < PA.n, RefinesT Maps (Priv0 i) (PrivAt i) (pairT i) (trS i) (PA.tr i) (ψ i)) :
    ∀ i < PA.n, ∀ p x, evAt (trS i) p = some x → ∀ w, rfA w (.thr i (ψ i p).1 (ψ i p).2) →
      (∃ q, w = .init q ∧ q < locsC.length) ∨
      ∃ i2 < PA.n, ∃ q, (evAt (trS i2) q).isSome ∧ w = .thr i2 (ψ i2 q).1 (ψ i2 q).2 := by
  intro i hi p x hx w hw
  let X := PA.exec locsA rfA coA rmwA
  obtain ⟨y, hy, -, hd, hl, -⟩ := (href i hi).ev p x hx
  have hyP : PA.evAt (.thr i (ψ i p).1 (ψ i p).2) = some y := by rw [evAt_thr_lt hi]; exact hy
  have hdR : X.dir (.thr i (ψ i p).1 (ψ i p).2) = .R := (hwf.rf_dir _ _ hw).2
  have hyR : y.dir = .R := by rw [← exec_dir_thr hyP]; exact hdR
  have hxR : x.dir = .R := by rw [← hd]; exact hyR
  have hlR : X.loc (.thr i (ψ i p).1 (ψ i p).2) = x.loc := by rw [exec_loc_thr hyP, hl]
  have hwl : X.loc w = x.loc := (hwf.rf_loc _ _ hw).trans hlR
  have hyF : y.dir ≠ .F := by rw [hyR]; decide
  -- a source write of the thread at `x.loc` between `w` and the read, `co`-after `w`: impossible
  have no_reinit : ∀ q' x', evAt (trS i) q' = some x' → x'.dir = .W → x'.loc = x.loc →
      Lt (ψ i q') (ψ i p) → X.co w (.thr i (ψ i q').1 (ψ i q').2) → False := by
    intro q' x' hx' hW' hl' hlt hco
    obtain ⟨y', hy', -, hd', hl'', -⟩ := (href i hi).ev q' x' hx'
    have hy'P : PA.evAt (.thr i (ψ i q').1 (ψ i q').2) = some y' := by
      rw [evAt_thr_lt hi]; exact hy'
    have hfr : X.fr (.thr i (ψ i p).1 (ψ i p).2) (.thr i (ψ i q').1 (ψ i q').2) := ⟨w, hw, hco⟩
    have hpl : X.poLoc (.thr i (ψ i q').1 (ψ i q').2) (.thr i (ψ i p).1 (ψ i p).2) :=
      ⟨⟨rfl, hlt⟩, by rw [exec_loc_thr hy'P, hlR, hl'', hl'],
        dir_ne_F hy'P (by rw [hd', hW']; decide), by rw [hdR]; decide⟩
    exact hint _ (.tail (.single (.inr (.inr (.inr hfr)))) (.inl hpl))
  -- the image of a source write is a write at its location
  have img_w : ∀ q' x', evAt (trS i) q' = some x' → x'.dir = .W → x'.loc = x.loc →
      X.dir (.thr i (ψ i q').1 (ψ i q').2) = .W ∧ X.loc (.thr i (ψ i q').1 (ψ i q').2) = x.loc := by
    intro q' x' hx' hW' hl'
    obtain ⟨y', hy', -, hd', hl'', -⟩ := (href i hi).ev q' x' hx'
    have hy'P : PA.evAt (.thr i (ψ i q').1 (ψ i q').2) = some y' := by
      rw [evAt_thr_lt hi]; exact hy'
    exact ⟨by rw [exec_dir_thr hy'P, hd', hW'], by rw [exec_loc_thr hy'P, hl'', hl']⟩
  have hwW : X.dir w = .W := (hwf.rf_dir _ _ hw).1
  cases w with
  | init q =>
    by_cases hq : q < locsC.length
    · exact .inl ⟨q, rfl, hq⟩
    · exfalso
      have hqA : q < locsA.length := by
        refine Classical.byContradiction fun hqA => ?_
        have := hwW
        simp [X, Traces.exec, hqA] at this
      obtain ⟨j, hj, hP⟩ := hpriv0 q hqA (by omega)
      have hlq : X.loc (.init q) = (locsA[q]).1 := by
        simp [X, Traces.exec, List.getElem?_eq_getElem hqA]
      rw [hlq] at hwl
      by_cases hji : j = i
      · subst hji
        obtain ⟨q', x', hx', hW', hl', hlt⟩ := (href j hi).fresh0 p x hx hxR (hwl ▸ hP)
        obtain ⟨hd2, hl2⟩ := img_w q' x' hx' hW' hl'
        refine no_reinit q' x' hx' hW' hl' hlt ?_
        rcases hwf.co_total (.init q) _ hwW hd2 (by rw [hl2, hlq, hwl]) (by simp) with h | h
        · exact h
        · exact absurd h (hinit _ q)
      · exact hcross i hi j hj hji _ y hy hyF (.inl (by rw [hl, ← hwl]; exact hP))
  | thr i2 j2 k2 =>
    rcases hy2 : PA.evAt (.thr i2 j2 k2) with _ | y2
    · have : X.dir (.thr i2 j2 k2) = .F := by simp [X, Traces.exec, hy2]
      rw [this] at hwW; cases hwW
    have h2 : i2 < PA.n := evAt_some_lt hy2
    have hy2' : evAt (PA.tr i2) (j2, k2) = some y2 := by rw [← evAt_thr_lt h2]; exact hy2
    have hdW : y2.dir = .W := by rw [← exec_dir_thr hy2]; exact hwW
    have hl2 : y2.loc = x.loc := by rw [← exec_loc_thr hy2]; exact hwl
    by_cases himg2 : ∃ q, (evAt (trS i2) q).isSome ∧ ψ i2 q = (j2, k2)
    · obtain ⟨q, hq, hψ⟩ := himg2
      exact .inr ⟨i2, h2, q, hq, by rw [hψ]⟩
    · exfalso
      have hp := (href i2 h2).priv (j2, k2) y2 hy2' hdW (fun q hq e => himg2 ⟨q, hq, e⟩)
      by_cases hii : i2 = i
      · subst hii
        have hpo : X.po (.thr i2 j2 k2) (.thr i2 (ψ i2 p).1 (ψ i2 p).2) :=
          hwf.com_int_po hint (.inl hw) rfl
        obtain ⟨-, hlt⟩ := hpo
        obtain ⟨q', x', hx', hW', hl', hlt1, hlt2⟩ := (href i2 h2).fresh p x hx hxR (j2, k2) y2 hy2'
          hdW hl2 hlt (fun q hq e => himg2 ⟨q, hq, e⟩)
        obtain ⟨hd3, hl3⟩ := img_w q' x' hx' hW' hl'
        have hne : PEv.thr i2 j2 k2 ≠ .thr i2 (ψ i2 q').1 (ψ i2 q').2 := by
          intro e
          simp only [PEv.thr.injEq] at e
          obtain ⟨-, e1, e2⟩ := e
          rcases hlt1 with h | ⟨h, h'⟩ <;> simp_all
        refine no_reinit q' x' hx' hW' hl' hlt2 ?_
        rcases hwf.co_total _ _ hwW hd3 (by rw [hl3, hwl]) hne with h | h
        · exact h
        · exfalso
          have hpl : X.poLoc (.thr i2 j2 k2) (.thr i2 (ψ i2 q').1 (ψ i2 q').2) :=
            ⟨⟨rfl, hlt1⟩, by rw [hl3, hwl], by rw [hwW]; decide, by rw [hd3]; decide⟩
          exact hint _ (.tail (.single (.inl hpl)) (.inr (.inr (.inl h))))
      · exact hcross i hi i2 h2 hii _ y hy hyF (.inr ⟨(j2, k2), by rw [hl, ← hl2]; exact hp⟩)

/-- **`realizes_of_threads` with time-varying private sets** (module doc). -/
theorem realizes_of_threads_privT {T : TSem TState SKind BVal} {PA : Traces AState AKind BVal}
    {locsA locsC : List (Nat × Nat)} {MA0 MC0 : Bytes} {rfA coA rmwA : Rel PEv}
    {s0 : Nat → TState} {Priv0 : Nat → Nat → Prop} {PrivAt : Nat → Nat × Nat → Nat → Prop}
    {pairT : Nat → Nat × Nat → Nat × Nat → Prop} {Obs : Nat → AState → TState → Prop}
    (hwf : (PA.exec locsA rfA coA rmwA).Wf)
    (hint : Acyclic (union (PA.exec locsA rfA coA rmwA).poLoc (PA.exec locsA rfA coA rmwA).com))
    (hinit : InitFirst (PA.exec locsA rfA coA rmwA))
    (hrmw : ∀ i < PA.n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔ pairT i a b)
    (hlocs : locsC <+: locsA)
    (hpriv0 : ∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < PA.n, Priv0 j (locsA[q]).1)
    (hval0 : ∀ q (h : q < locsC.length),
      bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2)
    (hcross : StackDisjoint PA (PrivU Priv0 PrivAt))
    (hthr : ∀ i < PA.n, ∃ (trS : List (List (Ev SKind BVal))) (stS : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), stS 0 = s0 i ∧
      (∀ j (h : j < trS.length), T (stS j) trS[j] (stS (j + 1))) ∧
      RefinesT Maps (Priv0 i) (PrivAt i) (pairT i) trS (PA.tr i) ψ ∧
      Obs i (PA.st i (PA.tr i).length) (stS trS.length)) :
    ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = PA.n ∧ (∀ i, PC.st i 0 = s0 i) ∧
      PC.Runs T ∧ Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ Obs := by
  classical
  have hthr' : ∀ i, ∃ c : List (List (Ev SKind BVal)) × (Nat → TState) × (Nat × Nat → Nat × Nat),
      i < PA.n → c.2.1 0 = s0 i ∧
      (∀ j (hj : j < c.1.length), T (c.2.1 j) c.1[j] (c.2.1 (j + 1))) ∧
      RefinesT Maps (Priv0 i) (PrivAt i) (pairT i) c.1 (PA.tr i) c.2.2 ∧
      Obs i (PA.st i (PA.tr i).length) (c.2.1 c.1.length) := by
    intro i
    by_cases h : i < PA.n
    · obtain ⟨trS, stS, ψ, h1, h2, h3, h4⟩ := hthr i h
      exact ⟨(trS, stS, ψ), fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨([], fun _ => s0 i, id), fun h' => absurd h' h⟩
  let c := fun i => Classical.choose (hthr' i)
  have hc : ∀ i (h : i < PA.n), _ := fun i h => Classical.choose_spec (hthr' i) h
  refine realizes_of_threads_fn (fun i => (c i).1) (fun i => (c i).2.1) (fun i => (c i).2.2) hwf hrmw
    hlocs hval0 (fun i h => (hc i h).1) (fun i h => (hc i h).2.1)
    (fun i h => (hc i h).2.2.1.toRefinesC) (fun i h => (hc i h).2.2.2) ?_
  exact src_of_refinesT hwf hint hinit hpriv0 hcross fun i h => (hc i h).2.2.1

/-- **Private coherence on a thread's stack** from the cross-thread premise: in a well-formed
execution, SC per location, its initial writes `co`-first, reads reading their writes' values and
no partially overlapping accesses, every read of thread `i` at a location of `U i` reads the
`po`-latest write of thread `i` there, or the initial value (`PrivCoh.privCoh_of_consistent`; only
thread `i` writes `U i` by `StackDisjoint`). This is what justifies the threads' run condition
(reads of their stack return their own bytes). -/
theorem privCoh_of_stackDisjoint {PA : Traces AState AKind BVal} {locs : List (Nat × Nat)}
    {M0 : Bytes} {rf co rmw : Rel PEv} (hwf : (PA.exec locs rf co rmw).Wf)
    (hint : Acyclic (union (PA.exec locs rf co rmw).poLoc (PA.exec locs rf co rmw).com))
    (hinit : InitFirst (PA.exec locs rf co rmw))
    (hval : ∀ w r, rf w r → PA.val bytesI M0 locs [] w = PA.val bytesI M0 locs [] r)
    (hov : NoOverlap (PA.exec locs rf co rmw) (PA.sz locs)) {U : Nat → Nat → Prop}
    (hcross : StackDisjoint PA U) :
    ∀ i < PA.n, PrivCoh (U i) (fun l n => bytesI.get M0 l n) (PA.tr i) := by
  intro i hi p y hy hR hP
  refine privCoh_of_consistent (Priv := fun i l => i < PA.n ∧ U i l) hwf hint hinit hval hov
    (fun i j k x hx hW i' hP' => ?_) i hi p y hy hR ⟨hi, hP⟩
  have hi2 := evAt_some_lt hx
  refine Classical.byContradiction fun hne => ?_
  have hx' : evAt (PA.tr i) (j, k) = some x := by rw [← evAt_thr_lt hi2]; exact hx
  exact hcross i hi2 i' hP'.1 hne (j, k) x hx' (by rw [hW]; decide) hP'.2

end Concurrency.PrivCohT
