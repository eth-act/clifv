import FV.Concurrency.CStepSConv
import FV.Concurrency.ThreadCompose
import FV.Concurrency.RealizeCompiled

/-!
# A segment's realization with masks and dirty sets (#473, step (4))

The layers realize an activation's segment by a `CRun` of `CStep` steps refined with the
activation's private set (`Refines Maps P`). `CallComposeT.SegOkG` asks for `RealizedT`: a
`CRunS` run between states carrying the own-initialisation mask, refined from the segment's
start-dirty set. Here:

* `crun_split`: a run of a concatenation splits;
* `ReadsMasked U evs`: a step reads a masked byte; **`readsAvoid_or_cut`**: the reads of a run
  avoid the evolving mask, or there is a first step reading a masked byte;
* `Uniform.take`, `RefinesT.mono0` (a smaller start-dirty set), **`notClean_sub`** (a location
  not clean at a segment's end was dirty at its start or is private), **`notClean_dirtyEnd`**
  (`DirtyEnd D P trS`: private, or dirty at the start and written by no source write there);
* **`realizedT_segW`**: a segment whose reads avoid the mask `U` and whose start-dirty set `D`
  lies in `P ∪ U ∪ NS` (`NS`: addresses at which no CLIF read of the segment starts) is a
  `RealizedT` from `encT U` to `encT (maskAfter U trS)`, ending dirty in `DirtyEnd D P trS`
  (`realizedT_seg`: in `D ∪ P`);
* **`realizedT_cutW`**/`realizedT_cut`: any segment, truncated before the first CLIF step
  reading a masked byte (`Refines.take`, an Arm label having at most one event, `prun_len`): the
  whole segment, or a prefix ending where the next CLIF step reads a masked byte.
-/

namespace Concurrency.CallSegT

open Prog ClifThread ClifThreadI ThreadRefine PrivCohT CallComposeT ArmThread ArmAllocThread
  PrepThread ClifCStepTerm RealizeCompiled ThreadCompose

/-! ## Runs and masks -/

/-- A run of a concatenation splits. -/
theorem crun_split {env : Clif.Env} {p : Clif.Program} :
    ∀ {t t' : TState} (A B : List (List (Ev SKind BVal))), CRun env p t (A ++ B) t' →
      ∃ m, CRun env p t A m ∧ CRun env p m B t'
  | t, _, [], _, h => ⟨t, .nil, h⟩
  | _, _, _ :: A, B, .cons hs hr => by
    obtain ⟨m, h1, h2⟩ := crun_split A B hr
    exact ⟨m, .cons hs h1, h2⟩

/-- **A step reads a byte of the mask `U`.** -/
def ReadsMasked (U : Nat → Prop) (evs : List (Ev SKind BVal)) : Prop :=
  ∃ e ∈ evs, e.dir = .R ∧ ∃ k < e.n, U (e.loc + k)

open Classical in
/-- **The reads avoid the evolving mask, or a first step reads a masked byte.** -/
theorem readsAvoid_or_cut : ∀ (U : Nat → Prop) (trS : List (List (Ev SKind BVal))),
    ReadsAvoid U trS ∨ ∃ j evs, trS[j]? = some evs ∧ ReadsAvoid U (trS.take j) ∧
      ReadsMasked (maskAfter U (trS.take j)) evs
  | _, [] => .inl trivial
  | U, evs :: tr => by
    by_cases h : ∀ e ∈ evs, e.dir = .R → ∀ k < e.n, ¬ U (e.loc + k)
    · rcases readsAvoid_or_cut (fun a => U a ∧ ¬ writes evs a) tr with h2 | ⟨j, e', hj, h2, h3⟩
      · exact .inl ⟨h, h2⟩
      · refine .inr ⟨j + 1, e', by simpa using hj, ⟨h, by simpa using h2⟩, ?_⟩
        simpa [maskAfter] using h3
    · refine .inr ⟨0, evs, rfl, trivial, ?_⟩
      simp only [not_forall, Classical.not_not] at h
      obtain ⟨e, he, hR, k, hk, hU⟩ := h
      exact ⟨e, he, hR, k, hk, by simpa [maskAfter] using hU⟩

theorem uniform_take {trS : List (List (Ev SKind BVal))} (h : Uniform trS) (j : Nat) :
    Uniform (trS.take j) := fun p x q y hp hq =>
  h p x q y (evAt_take_some hp).2 (evAt_take_some hq).2

/-! ## Start-dirty sets -/

variable {K K' V : Type}

/-- **A smaller start-dirty set.** -/
theorem _root_.Concurrency.PrivCohT.RefinesT.mono0 {MK : K → K' → Prop} {D D' : Nat → Prop} {PA : Nat × Nat → Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : RefinesT MK D' PA pairT trS trT ψ) (hD : ∀ a, D a → D' a) :
    RefinesT MK D PA pairT trS trT ψ where
  toRefinesC := h.toRefinesC
  shared := h.shared
  priv := h.priv
  fresh0 p x hx hR hd := h.fresh0 p x hx hR (hD _ hd)
  fresh := h.fresh

/-- **A location not clean at a segment's end** was dirty at its start or is private (an
unmatched Arm write there). -/
theorem notClean_sub {MK : K → K' → Prop} {D : Nat → Prop} {P : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : RefinesT MK D (fun _ => P) pairT trS trT ψ) {a : Nat} (ha : ¬ Clean D trS trT ψ a) :
    D a ∨ P a := by
  classical
  refine Classical.byContradiction fun hn => ha ⟨fun hd => absurd (.inl hd) hn,
    fun q y hy hW hl hu => absurd (.inr (hl ▸ h.priv q y hy hW hu)) hn⟩

/-- **Dirty at a segment's end**: private, or dirty at its start and written by no source write
at that location. -/
def DirtyEnd (D P : Nat → Prop) (trS : List (List (Ev K V))) (a : Nat) : Prop :=
  P a ∨ (D a ∧ ¬ ∃ q x, evAt trS q = some x ∧ x.dir = .W ∧ x.loc = a)

/-- **A location not clean at a segment's end is `DirtyEnd`.** -/
theorem notClean_dirtyEnd {MK : K → K' → Prop} {D : Nat → Prop} {P : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : RefinesT MK D (fun _ => P) pairT trS trT ψ) {a : Nat} (ha : ¬ Clean D trS trT ψ a) :
    DirtyEnd D P trS a := by
  classical
  refine Classical.byContradiction fun hn => ha ⟨fun hd => ?_,
    fun q y hy hW hl hu => absurd (.inl (hl ▸ h.priv q y hy hW hu)) hn⟩
  exact Classical.byContradiction fun hw => hn (.inr ⟨hd, hw⟩)

theorem DirtyEnd.sub {D P : Nat → Prop} {trS : List (List (Ev K V))} {a : Nat}
    (h : DirtyEnd D P trS a) : D a ∨ P a :=
  h.elim .inr fun h => .inl h.1

/-- **A larger end-dirty set.** -/
theorem _root_.Concurrency.CallComposeT.RealizedT.mono_out {env : Clif.Env} {p : Clif.Program}
    {Bnd : Nat → Prop} {ls : List Lab} {k : Nat} {c c' : TState} {D D' D'' : Nat → Prop}
    (h : RealizedT env p Bnd ls k c c' D D') (hD : ∀ a, D' a → D'' a) :
    RealizedT env p Bnd ls k c c' D D'' := by
  obtain ⟨hk, trS, ψ, P, hr, hx, hf, hb, hd⟩ := h
  exact ⟨hk, trS, ψ, P, hr, hx, hf, hb, fun a ha => hD a (hd a ha)⟩

/-! ## The realization of a segment -/

variable {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}

/-- **A segment whose reads avoid the mask, ending dirty in `DirtyEnd`** (module doc). -/
theorem realizedT_segW {ls : List Lab} {k : Nat} (hk : k ≤ ls.length) {s s1 : Clif.State}
    {trS : List (List (Ev SKind BVal))} {ψ : Nat × Nat → Nat × Nat} {P : Nat → Prop}
    (hrun : CRun env p (.run s) trS (.run s1)) (hx : CallCompose.XClosed (evTr (ls.take k)))
    (href : Refines Maps P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D NS : Nat → Prop} (hra : ReadsAvoid U trS) (hD : ∀ a, D a → P a ∨ U a ∨ NS a)
    (hu : Uniform trS) (hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n)
    (hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ NS x.loc) (hb : ∀ l, P l → Bnd l) :
    RealizedT env p Bnd ls k (encT U (.run s)) (encT (maskAfter U trS) (.run s1)) D
      (DirtyEnd D P trS) := by
  have hT := (Refines.toT_dirty href hra hu hpos hns).mono0 hD
  exact ⟨hk, trS, ψ, fun _ => P, crunS_of_crun hrun rfl hra, hx, hT, fun _ l h => hb l h,
    fun a ha => notClean_dirtyEnd hT ha⟩

/-- **A segment whose reads avoid the mask** (module doc). -/
theorem realizedT_seg {ls : List Lab} {k : Nat} (hk : k ≤ ls.length) {s s1 : Clif.State}
    {trS : List (List (Ev SKind BVal))} {ψ : Nat × Nat → Nat × Nat} {P : Nat → Prop}
    (hrun : CRun env p (.run s) trS (.run s1)) (hx : CallCompose.XClosed (evTr (ls.take k)))
    (href : Refines Maps P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D NS : Nat → Prop} (hra : ReadsAvoid U trS) (hD : ∀ a, D a → P a ∨ U a ∨ NS a)
    (hu : Uniform trS) (hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n)
    (hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ NS x.loc) (hb : ∀ l, P l → Bnd l) :
    RealizedT env p Bnd ls k (encT U (.run s)) (encT (maskAfter U trS) (.run s1)) D
      (fun a => D a ∨ P a) :=
  (realizedT_segW hk hrun hx href hra hD hu hpos hns hb).mono_out fun _ h => h.sub

/-- **A segment, truncated before the first CLIF step reading a masked byte, ending dirty in
`DirtyEnd`** (module doc): the whole segment, or a prefix whose next CLIF step reads a masked
byte. -/
theorem realizedT_cutW {f : Arm.ArmState → Arm.ArmState} {ok : Arm.ArmState → Lab → Prop}
    {u t' : Arm.ArmState × Mon}
    {ls : List Lab} (hr : PRun Policy.arm f ok u ls t') {k : Nat} (hk : k ≤ ls.length)
    {s s1 : Clif.State} {trS : List (List (Ev SKind BVal))} {ψ : Nat × Nat → Nat × Nat}
    {P : Nat → Prop} (hrun : CRun env p (.run s) trS (.run s1))
    (hx : ∀ k' ≤ k, CallCompose.XClosed (evTr (ls.take k')))
    (href : Refines Maps P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D NS : Nat → Prop} (hD : ∀ a, D a → P a ∨ U a ∨ NS a)
    (hu : Uniform trS) (hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n)
    (hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ NS x.loc) (hb : ∀ l, P l → Bnd l) :
    (RealizedT env p Bnd ls k (encT U (.run s)) (encT (maskAfter U trS) (.run s1)) D
        (DirtyEnd D P trS)) ∨
      ∃ k' ≤ k, ∃ j evs, trS[j]? = some evs ∧ ∃ sj : Clif.State, ∃ t'' : TState,
        RealizedT env p Bnd ls k' (encT U (.run s)) (encT (maskAfter U (trS.take j)) (.run sj))
          D (DirtyEnd D P (trS.take j)) ∧
        CStep env p (.run sj) evs t'' ∧ ReadsMasked (maskAfter U (trS.take j)) evs := by
  rcases readsAvoid_or_cut U trS with hra | ⟨j, evs, hjs, hra, hmask⟩
  · exact .inl (realizedT_segW hk hrun (hx k (Nat.le_refl _)) href hra hD hu hpos hns hb)
  · right
    -- the CLIF run up to step `j`, and step `j`
    have hj : j < trS.length := (List.getElem?_eq_some_iff.mp hjs).1
    have hjv : trS[j] = evs := (List.getElem?_eq_some_iff.mp hjs).2
    have e : trS = trS.take j ++ trS.drop j := (List.take_append_drop j trS).symm
    obtain ⟨m, h1, h2⟩ := crun_split (trS.take j) (trS.drop j) (e ▸ hrun)
    have hd : trS.drop j = trS[j] :: trS.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [hd] at h2
    rw [hjv] at h2
    obtain ⟨t'', hstep⟩ : ∃ t'', CStep env p m evs t'' := by
      cases h2 with
      | cons hs hr' => exact ⟨_, hs⟩
    obtain ⟨sj, rfl⟩ : ∃ sj, m = .run sj := by
      cases m with
      | run sj => exact ⟨sj, rfl⟩
      | ret v => exact hstep.elim
    -- the Arm prefix holding the images of the kept CLIF steps
    have h1' : ∀ i (hi : i < (conv (evTr (ls.take k))).length),
        (conv (evTr (ls.take k)))[i].length ≤ 1 := by
      intro i hi
      have hl := prun_len hr i (by simp [conv, evTr] at hi ⊢; omega)
      simp only [conv, evTr, List.getElem_map, List.length_map, List.getElem_take] at hl ⊢
      exact hl
    obtain ⟨k', hk', hAk, -⟩ := Refines.take href h1' j
    have hlen : (conv (evTr (ls.take k))).length = k := by simp [conv, evTr]; omega
    rw [hlen] at hk'
    have htk : (conv (evTr (ls.take k))).take k' = conv (evTr (ls.take k')) := by
      simp only [conv, evTr, ← List.map_take, List.take_take]
      rw [Nat.min_eq_left hk']
    rw [htk] at hAk
    have hpair : ∀ a b, (evAt (conv (evTr (ls.take k'))) a).isSome →
        (evAt (conv (evTr (ls.take k'))) b).isSome →
        (MonPair (evTr (ls.take k)) a b ↔ MonPair (evTr (ls.take k')) a b) := by
      intro a b _ hb'
      refine monPair_take hk' ?_
      obtain ⟨hb1, -⟩ := evAt_isSome hb'
      have := hb1; simp [conv, evTr] at this; omega
    have href' := Refines.pairT_congr hAk hpair
    refine ⟨k', hk', j, evs, hjs, sj, t'', ?_, hstep, hmask⟩
    have hpos' : ∀ q x, evAt (trS.take j) q = some x → x.dir = .R → 0 < x.n :=
      fun q x h => hpos q x (evAt_take_some h).2
    have hns' : ∀ q x, evAt (trS.take j) q = some x → x.dir = .R → ¬ NS x.loc :=
      fun q x h => hns q x (evAt_take_some h).2
    exact realizedT_segW (by omega) h1 (hx k' hk') href' hra hD (uniform_take hu j) hpos' hns' hb

/-- **A segment, truncated before the first CLIF step reading a masked byte** (module doc): the
whole segment, or a prefix whose next CLIF step reads a masked byte. -/
theorem realizedT_cut {f : Arm.ArmState → Arm.ArmState} {ok : Arm.ArmState → Lab → Prop}
    {u t' : Arm.ArmState × Mon}
    {ls : List Lab} (hr : PRun Policy.arm f ok u ls t') {k : Nat} (hk : k ≤ ls.length)
    {s s1 : Clif.State} {trS : List (List (Ev SKind BVal))} {ψ : Nat × Nat → Nat × Nat}
    {P : Nat → Prop} (hrun : CRun env p (.run s) trS (.run s1))
    (hx : ∀ k' ≤ k, CallCompose.XClosed (evTr (ls.take k')))
    (href : Refines Maps P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D NS : Nat → Prop} (hD : ∀ a, D a → P a ∨ U a ∨ NS a)
    (hu : Uniform trS) (hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n)
    (hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ NS x.loc) (hb : ∀ l, P l → Bnd l) :
    (RealizedT env p Bnd ls k (encT U (.run s)) (encT (maskAfter U trS) (.run s1)) D
        (fun a => D a ∨ P a)) ∨
      ∃ k' ≤ k, ∃ j evs, trS[j]? = some evs ∧ ∃ sj : Clif.State, ∃ t'' : TState,
        RealizedT env p Bnd ls k' (encT U (.run s)) (encT (maskAfter U (trS.take j)) (.run sj))
          D (fun a => D a ∨ P a) ∧
        CStep env p (.run sj) evs t'' ∧ ReadsMasked (maskAfter U (trS.take j)) evs :=
  (realizedT_cutW hr hk hrun hx href hD hu hpos hns hb).imp (fun h => h.mono_out fun _ h => h.sub)
    fun ⟨k', hk', j, evs, hj, sj, t'', hR, hs, hm⟩ =>
      ⟨k', hk', j, evs, hj, sj, t'', hR.mono_out fun _ h => h.sub, hs, hm⟩

end Concurrency.CallSegT
