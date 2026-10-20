import FV.Concurrency.ThreadRefine
import FV.Concurrency.Armv8

/-!
# Private reads read the thread's own writes (T2h, #311)

A compiled thread reads locations no CLIF event touches: the frame record (`stp`/`ldp` of fp/lr
in every prologue/epilogue), spill slots, saved registers. In an arbitrary run of the per-thread
semantics (`ArmThread.TStep`) such a read returns any value, so the per-thread refinement
(`ThreadRefine.Refines`) needs the premise that it returns the thread's own last write there (or
the initial value): **private coherence** `PrivCoh`. This file derives it from the execution:

* `privCoh_of_consistent`: in a well-formed execution that is SC per location
  (`acyclic(po-loc ∪ com)`, Armv8's `internal` axiom), whose initial writes are `co`-first and
  whose reads read their writes' values, with no partially overlapping accesses, **if only thread
  `i` writes the locations `Priv i`, every read of thread `i` there reads the `po`-latest write
  of thread `i` there, or the initial value when there is none** (`PrivCoh (Priv i)`);
* `realizes_of_threads_priv`: `ThreadRefine.realizes_of_threads` with a **private set per
  thread** (`Priv i`, e.g. thread `i`'s stack), the source events avoiding all of them;
* `ownWrites_of_refines`: the premise of `privCoh_of_consistent` (only thread `i` writes
  `Priv i`) is what the threads' guarantees say (`Refines.priv`: writes outside the image are in
  the thread's own set; `shared`: images are outside every set) when the sets are pairwise
  disjoint.

The per-thread obligation thus becomes: a thread whose private reads are coherent refines its
CLIF thread. The cross-thread premise (no thread writes another's private set) stays explicit at
the program level: deriving it from the refinements would be circular (thread `j`'s guarantee
needs `j`'s coherence, which needs every other thread's guarantee), and the fragment model allows
load buffering (no dependency ordering, §2), so no induction over the execution breaks the cycle.
-/

namespace Concurrency.PrivCoh

open Rel Prog ClifThread ProgE2E ThreadRefine

variable {K V : Type}

/-- **Private coherence of a thread trace**: every read of a location in `Priv` reads the value of
the latest earlier write of the trace there (no write to that location in between), or, when
there is no earlier write there, the initial value `init loc n`. -/
def PrivCoh (Priv : Nat → Prop) (init : Nat → Nat → V) (tr : List (List (Ev K V))) : Prop :=
  ∀ p y, evAt tr p = some y → y.dir = .R → Priv y.loc →
    (∃ q x, Lt q p ∧ evAt tr q = some x ∧ x.dir = .W ∧ x.loc = y.loc ∧ x.val = y.val ∧
      ∀ q' x', Lt q q' → Lt q' p → evAt tr q' = some x' → x'.dir = .W → x'.loc ≠ y.loc) ∨
    ((∀ q x, Lt q p → evAt tr q = some x → x.dir = .W → x.loc ≠ y.loc) ∧ y.val = init y.loc y.n)

section exec

variable {σ : Type} {P : Traces σ K BVal} {locs : List (Nat × Nat)} {rf co rmw : Rel PEv}

theorem exec_dir_thr {i j k : Nat} {x : Ev K BVal} (h : P.evAt (.thr i j k) = some x) :
    (P.exec locs rf co rmw).dir (.thr i j k) = x.dir := by
  simp only [Traces.exec, h]

theorem exec_loc_thr {i j k : Nat} {x : Ev K BVal} (h : P.evAt (.thr i j k) = some x) :
    (P.exec locs rf co rmw).loc (.thr i j k) = x.loc := by
  simp only [Traces.exec, h]

theorem sz_thr {i j k : Nat} {x : Ev K BVal} (h : P.evAt (.thr i j k) = some x) :
    P.sz locs (.thr i j k) = x.n := by
  simp only [Traces.sz, h]

theorem val_thr {M0 : Bytes} {i j k : Nat} {x : Ev K BVal} (h : P.evAt (.thr i j k) = some x) :
    P.val bytesI M0 locs [] (.thr i j k) = x.val := by
  simp only [Traces.val, h]

theorem evAt_some_lt {i j k : Nat} {x : Ev K BVal} (h : P.evAt (.thr i j k) = some x) : i < P.n := by
  refine Classical.byContradiction fun hi => ?_
  rw [evAt_thr_ge hi] at h; cases h

theorem dir_ne_F {i j k : Nat} {x : Ev K BVal} (h : P.evAt (.thr i j k) = some x)
    (hd : x.dir ≠ .F) : (P.exec locs rf co rmw).dir (.thr i j k) ≠ .F := by
  rw [exec_dir_thr h]; exact hd

end exec

/-- **Private coherence from the execution** (module doc). -/
theorem privCoh_of_consistent {σ : Type} {P : Traces σ K BVal} {locs : List (Nat × Nat)}
    {M0 : Bytes} {rf co rmw : Rel PEv}
    (hwf : (P.exec locs rf co rmw).Wf)
    (hint : Acyclic (union (P.exec locs rf co rmw).poLoc (P.exec locs rf co rmw).com))
    (hinit : InitFirst (P.exec locs rf co rmw))
    (hval : ∀ w r, rf w r → P.val bytesI M0 locs [] w = P.val bytesI M0 locs [] r)
    (hov : NoOverlap (P.exec locs rf co rmw) (P.sz locs))
    {Priv : Nat → Nat → Prop}
    (hown : ∀ i j k x, P.evAt (.thr i j k) = some x → x.dir = .W → ∀ i', Priv i' x.loc → i' = i) :
    ∀ i < P.n, PrivCoh (Priv i) (fun l n => bytesI.get M0 l n) (P.tr i) := by
  intro i hi p y hy hR hP
  let X := P.exec locs rf co rmw
  obtain ⟨j, k⟩ := p
  have hyP : P.evAt (.thr i j k) = some y := by rw [evAt_thr_lt hi]; exact hy
  have hdR : X.dir (.thr i j k) = .R := by rw [exec_dir_thr hyP]; exact hR
  have hlR : X.loc (.thr i j k) = y.loc := exec_loc_thr hyP
  obtain ⟨w, hw⟩ := hwf.rf_total _ hdR
  have hwW := (hwf.rf_dir _ _ hw).1
  have hwl : X.loc w = y.loc := (hwf.rf_loc _ _ hw).trans hlR
  -- an own write at `y.loc` before the read, coherence-after `w`, is impossible
  have no_later : ∀ q x, Lt q (j, k) → evAt (P.tr i) q = some x → x.dir = .W → x.loc = y.loc →
      X.co w (.thr i q.1 q.2) → False := by
    intro q x hq hx hxW hxl hco
    have hxP : P.evAt (.thr i q.1 q.2) = some x := by rw [evAt_thr_lt hi]; exact hx
    have hfr : X.fr (.thr i j k) (.thr i q.1 q.2) := ⟨w, hw, hco⟩
    have hpl : X.poLoc (.thr i q.1 q.2) (.thr i j k) :=
      ⟨⟨rfl, hq⟩, by rw [exec_loc_thr hxP, hlR, hxl],
        dir_ne_F hxP (by rw [hxW]; decide), by rw [hdR]; decide⟩
    exact hint _ (.tail (.single (.inr (.inr (.inr hfr)))) (.inl hpl))
  cases w with
  | init q =>
    right
    refine ⟨fun q' x hq' hx hxW hxl => ?_, ?_⟩
    · have hxP : P.evAt (.thr i q'.1 q'.2) = some x := by rw [evAt_thr_lt hi]; exact hx
      refine no_later q' x hq' hx hxW hxl ?_
      rcases hwf.co_total (.init q) (.thr i q'.1 q'.2) hwW (by rw [exec_dir_thr hxP]; exact hxW)
          (by rw [exec_loc_thr hxP, hwl]; exact hxl.symm) (by simp) with h | h
      · exact h
      · exact absurd h (hinit _ q)
    · have hv := hval _ _ hw
      rw [val_thr hyP] at hv
      rw [← hv]
      have hsz := (hov (.init q) (.thr i j k) (by rw [hwW]; decide) (by rw [hdR]; decide)).1
        (hwl.trans hlR.symm)
      rw [sz_thr hyP] at hsz
      have hl0 : X.loc (.init q) = (locs[q]?.getD (0, 0)).1 := rfl
      simp only [Traces.val]
      rw [← hsz]
      simp only [Traces.sz]
      rw [← hl0, hwl]
  | thr i2 j2 k2 =>
    rcases hx2 : P.evAt (.thr i2 j2 k2) with _ | x2
    · have : X.dir (.thr i2 j2 k2) = .F := by simp [X, Traces.exec, hx2]
      rw [this] at hwW; cases hwW
    have hx2W : x2.dir = .W := by rw [← exec_dir_thr hx2]; exact hwW
    have hx2l : x2.loc = y.loc := by rw [← exec_loc_thr hx2]; exact hwl
    have hi2 : i2 = i := (hown i2 j2 k2 x2 hx2 hx2W i (hx2l ▸ hP)).symm
    subst hi2
    have hpo : X.po (.thr i2 j2 k2) (.thr i2 j k) :=
      hwf.com_int_po hint (.inl hw) rfl
    obtain ⟨-, hlt⟩ := hpo
    left
    refine ⟨(j2, k2), x2, hlt, by rw [← evAt_thr_lt hi]; exact hx2, hx2W, hx2l, ?_, ?_⟩
    · have hv := hval _ _ hw
      rwa [val_thr hyP, val_thr hx2] at hv
    · intro q' x' h1 h2 hx' hxW hxl
      have hxP : P.evAt (.thr i2 q'.1 q'.2) = some x' := by rw [evAt_thr_lt hi]; exact hx'
      have hne : PEv.thr i2 j2 k2 ≠ .thr i2 q'.1 q'.2 := by
        intro e; simp only [PEv.thr.injEq] at e
        obtain ⟨-, e1, e2⟩ := e
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> simp at * <;> omega
      rcases hwf.co_total _ _ hwW (by rw [exec_dir_thr hxP]; exact hxW)
          (by rw [exec_loc_thr hxP, hwl, hxl]) hne with h | h
      · exact no_later q' x' h2 hx' hxW hxl h
      · have hpl : X.poLoc (.thr i2 j2 k2) (.thr i2 q'.1 q'.2) :=
          ⟨⟨rfl, h1⟩, by rw [exec_loc_thr hxP, hwl, hxl], by rw [hwW]; decide,
            dir_ne_F hxP (by rw [hxW]; decide)⟩
        exact hint _ (.tail (.single (.inl hpl)) (.inr (.inr (.inl h))))

/-! ## Per-thread private sets -/

variable {K' : Type}

/-- A refinement with a larger private set, when the source events avoid it. -/
theorem Refines.mono_priv {MK : K → K' → Prop} {P P' : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : Refines MK P pairT trS trT ψ) (hP : ∀ l, P l → P' l)
    (hsh : ∀ p x, evAt trS p = some x → ¬ P' x.loc) : Refines MK P' pairT trS trT ψ :=
  { h with
    shared := hsh
    priv := fun p y hy hW hn => hP _ (h.priv p y hy hW hn) }

/-- **`realizes_of_threads` with a private set per thread**: thread `i` refines its CLIF thread
with its own private set `PrivT i` (`Refines.priv`: its writes outside the image), its source
events avoid every thread's set, and the Arm initial locations beyond the CLIF ones are private to
some thread. -/
theorem realizes_of_threads_priv {T : TSem TState SKind BVal} {PA : Traces AState AKind BVal}
    {locsA locsC : List (Nat × Nat)} {MA0 MC0 : Bytes} {rfA coA rmwA : Rel PEv}
    {s0 : Nat → TState} {PrivT : Nat → Nat → Prop} {pairT : Nat → Nat × Nat → Nat × Nat → Prop}
    {Obs : Nat → AState → TState → Prop}
    (hwf : (PA.exec locsA rfA coA rmwA).Wf)
    (hrmw : ∀ i < PA.n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔ pairT i a b)
    (hlocs : locsC <+: locsA)
    (hpriv0 : ∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j, PrivT j (locsA[q]).1)
    (hval0 : ∀ q (h : q < locsC.length),
      bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2)
    (hthr : ∀ i < PA.n, ∃ (trS : List (List (Ev SKind BVal))) (stS : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), stS 0 = s0 i ∧
      (∀ j (h : j < trS.length), T (stS j) trS[j] (stS (j + 1))) ∧
      Refines Maps (PrivT i) (pairT i) trS (PA.tr i) ψ ∧
      (∀ p x, evAt trS p = some x → ∀ j, ¬ PrivT j x.loc) ∧
      Obs i (PA.st i (PA.tr i).length) (stS trS.length)) :
    ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = PA.n ∧ (∀ i, PC.st i 0 = s0 i) ∧
      PC.Runs T ∧ Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ Obs := by
  refine realizes_of_threads (Priv := fun l => ∃ j, PrivT j l) hwf hrmw hlocs hpriv0 hval0
    fun i hi => ?_
  obtain ⟨trS, stS, ψ, h0, hrun, href, hsh, hobs⟩ := hthr i hi
  exact ⟨trS, stS, ψ, h0, hrun,
    Refines.mono_priv href (fun l h => ⟨i, h⟩) (fun p x hx ⟨j, hj⟩ => hsh p x hx j hj), hobs⟩

/-- **Only thread `i` writes `PrivT i`**, from the threads' guarantees: a write of thread `i` is
an image of a source write (outside every private set, `Refines.shared`) or in `PrivT i`
(`Refines.priv`); the sets are pairwise disjoint. The premise `hown` of `privCoh_of_consistent`. -/
theorem ownWrites_of_refines {σ : Type} {PA : Traces σ AKind BVal} {PrivT : Nat → Nat → Prop}
    (hdisj : ∀ i i' l, PrivT i l → PrivT i' l → i = i')
    (hthr : ∀ i < PA.n, ∃ (trS : List (List (Ev SKind BVal))) (pairT : Nat × Nat → Nat × Nat → Prop)
      (ψ : Nat × Nat → Nat × Nat), Refines Maps (PrivT i) pairT trS (PA.tr i) ψ ∧
      (∀ p x, evAt trS p = some x → ∀ j, ¬ PrivT j x.loc)) :
    ∀ i j k x, PA.evAt (.thr i j k) = some x → x.dir = .W → ∀ i', PrivT i' x.loc → i' = i := by
  intro i j k x hx hW i' hP
  have hi := evAt_some_lt hx
  obtain ⟨trS, pairT, ψ, href, hsh⟩ := hthr i hi
  have hx' : evAt (PA.tr i) (j, k) = some x := by rw [← evAt_thr_lt hi]; exact hx
  by_cases himg : ∃ q, (evAt trS q).isSome ∧ ψ q = (j, k)
  · obtain ⟨q, hq, hψ⟩ := himg
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hq
    obtain ⟨y, hy, -, -, hl, -⟩ := href.ev q u hu
    rw [hψ, hx'] at hy
    cases hy
    exact absurd (hl ▸ hP) (hsh q u hu i')
  · exact hdisj _ _ _ hP (href.priv (j, k) x hx' hW fun q hq e => himg ⟨q, hq, e⟩)

end Concurrency.PrivCoh
