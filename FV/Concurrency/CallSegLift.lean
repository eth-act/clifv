import FV.Concurrency.CallSegT
import FV.Concurrency.ClifLift
import FV.Concurrency.CallRetsN

/-!
# An activation's segment as a `RealizedT` of the thread (#473, step (4))

The layers (`CallSegAbi.arm_isel_refines_abiCRNX`, `CallRetsN.arm_isel_refinesCRNX`) realize an
activation's segment by a `CRun` from the activation's own CLIF state (no callers). In the
thread the activation runs below the suspended frames of its callers (`ClifLift.pushC ext`):

* `evAt_prefix_nil`, **`Refines.prefixNil`**: a prefix of a source trace dropping only
  event-free steps has the same events, so it refines the same target;
* **`realizedT_lift`**: the segment, lifted below `ext` (`ClifLift.crun_pushC`: a last return of
  the bottom frame, event-free, is left out) and truncated before the first CLIF step reading a
  masked byte (`CallSegT.realizedT_cut`), is a `RealizedT` from the lifted start state carrying
  the mask `U`: the whole segment (ending at the lifted end state, or before the bottom frame's
  return when the activation returned), or a prefix whose next lifted CLIF step reads a masked
  byte.
-/

namespace Concurrency.CallSegLift

open Prog ClifThread ClifThreadI ThreadRefine PrivCohT CallComposeT ArmThread ArmAllocThread
  PrepThread ClifCStepTerm RealizeCompiled ThreadCompose CallSegT ClifLift

variable {K K' V : Type}

/-- A prefix of a trace dropping only empty steps has the same events. -/
theorem evAt_prefix_nil {A B : List (List K)} (hp : A <+: B) (hd : ∀ e ∈ B.drop A.length, e = []) :
    ∀ q, evAt A q = evAt B q := by
  intro q
  obtain ⟨C, rfl⟩ := hp
  by_cases hq : q.1 < A.length
  · rw [evAt_append_lt _ _ hq]
  · rw [evAt_append_ge _ _ (by omega)]
    have hC : ∀ e ∈ C, e = [] := by simpa using hd
    unfold evAt
    rw [List.getElem?_eq_none (by omega)]
    cases h : C[q.1 - A.length]? with
    | none => rfl
    | some x => rw [hC x (List.mem_of_getElem? h)]; simp

/-- **A prefix dropping only event-free source steps refines the same target.** -/
theorem Refines.prefixNil {MK : K → K' → Prop} {P : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {A B : List (List (Ev K V))} {T : List (List (Ev K' V))}
    {ψ : Nat × Nat → Nat × Nat} (h : Refines MK P pairT B T ψ) (hp : A <+: B)
    (hd : ∀ e ∈ B.drop A.length, e = []) : Refines MK P pairT A T ψ where
  ev q x hx := h.ev q x (by rw [← evAt_prefix_nil hp hd]; exact hx)
  mono q r hq hr := h.mono q r (by rw [← evAt_prefix_nil hp hd]; exact hq)
    (by rw [← evAt_prefix_nil hp hd]; exact hr)
  shared q x hx := h.shared q x (by rw [← evAt_prefix_nil hp hd]; exact hx)
  priv q y hy hW hn := h.priv q y hy hW fun r hr => hn r (by rw [evAt_prefix_nil hp hd]; exact hr)
  len j hj := by
    obtain ⟨C, rfl⟩ := hp
    have := h.len j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  pair j hj h2 := by
    obtain ⟨C, rfl⟩ := hp
    exact h.pair j (by simp; omega) (by rwa [List.getElem_append_left hj])
  pair_inv q r hq hr hpr := h.pair_inv q r (by rw [← evAt_prefix_nil hp hd]; exact hq)
    (by rw [← evAt_prefix_nil hp hd]; exact hr) hpr

variable {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}

/-- **An activation's segment, lifted below its callers and cut before a masked read, ending
dirty in `DirtyEnd`** (module doc). -/
theorem realizedT_liftW {f : Arm.ArmState → Arm.ArmState} {ok : Arm.ArmState → Lab → Prop}
    {u t' : Arm.ArmState × Mon} {ls : List Lab} (hr : PRun Policy.arm f ok u ls t') {k : Nat}
    (hk : k ≤ ls.length) (ext : List (Clif.Frame × List Clif.ValueId)) {s : Clif.State}
    {trS : List (List (Ev SKind BVal))} {t : TState} {ψ : Nat × Nat → Nat × Nat}
    {P : Nat → Prop} (hrun : CRun env p (.run s) trS t)
    (hx : CallCompose.XClosed (evTr (ls.take k)))
    (href : Refines Maps P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D NS : Nat → Prop} (hD : ∀ a, D a → P a ∨ U a ∨ NS a)
    (hu : Uniform trS) (hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n)
    (hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ NS x.loc) (hb : ∀ l, P l → Bnd l) :
    (∃ (trS' : List (List (Ev SKind BVal))) (s1 : Clif.State), trS' <+: trS ∧
        RealizedT env p Bnd ls k (encT U (.run (pushC ext s)))
          (encT (maskAfter U trS') (.run (pushC ext s1))) D (DirtyEnd D P trS') ∧
        (∀ s', t = .run s' → s1 = s') ∧ (∀ v, t = .ret v → CStep env p (.run s1) [] (.ret v))) ∨
      ∃ k' ≤ k, ∃ (trS' : List (List (Ev SKind BVal))) (j : Nat) (evs : List (Ev SKind BVal)),
        trS' <+: trS ∧
        trS'[j]? = some evs ∧ ∃ sj : Clif.State, ∃ t'' : TState,
        RealizedT env p Bnd ls k' (encT U (.run (pushC ext s)))
          (encT (maskAfter U (trS'.take j)) (.run sj)) D (DirtyEnd D P (trS'.take j)) ∧
        CStep env p (.run sj) evs t'' ∧ ReadsMasked (maskAfter U (trS'.take j)) evs := by
  obtain ⟨trS', t1, hrun', hp, hd, -, hrunE, hretE⟩ := crun_pushC (ext := ext) hrun
  -- the lifted run ends running
  obtain ⟨s1, hs1, hend⟩ : ∃ s1, t1 = .run (pushC ext s1) ∧
      (∀ s', t = .run s' → s1 = s') ∧ (∀ v, t = .ret v → CStep env p (.run s1) [] (.ret v)) := by
    cases t with
    | run s' =>
      obtain ⟨h1, -⟩ := hrunE s' rfl
      refine ⟨s', h1, fun s'' h => ?_, fun v' h => ?_⟩
      · cases h; rfl
      · cases h
    | ret v =>
      obtain ⟨s', h1, h2⟩ := hretE v rfl
      refine ⟨s', h1, fun s'' h => ?_, fun v' h => ?_⟩
      · cases h
      · cases h; exact h2
  subst hs1
  have href' := Refines.prefixNil href hp hd
  have hu' : Uniform trS' := fun q x r y hq hr' =>
    hu q x r y (by rw [← evAt_prefix_nil hp hd]; exact hq) (by rw [← evAt_prefix_nil hp hd]; exact hr')
  have hpos' : ∀ q x, evAt trS' q = some x → x.dir = .R → 0 < x.n := fun q x h =>
    hpos q x (by rw [← evAt_prefix_nil hp hd]; exact h)
  have hns' : ∀ q x, evAt trS' q = some x → x.dir = .R → ¬ NS x.loc := fun q x h =>
    hns q x (by rw [← evAt_prefix_nil hp hd]; exact h)
  have hxk : ∀ k' ≤ k, CallCompose.XClosed (evTr (ls.take k')) := fun k' h' => by
    rw [CallRetsN.evTr_take_take h']; exact CallRetsN.xClosed_take hx k'
  rcases realizedT_cutW (Bnd := Bnd) hr hk hrun' hxk href' hD hu' hpos' hns' hb with h | h
  · exact .inl ⟨trS', s1, hp, h, hend⟩
  · obtain ⟨k', hk', j, evs, hj, sj, t'', hR, hst, hm⟩ := h
    exact .inr ⟨k', hk', trS', j, evs, hp, hj, sj, t'', hR, hst, hm⟩

/-- **An activation's segment, lifted below its callers and cut before a masked read**
(module doc). -/
theorem realizedT_lift {f : Arm.ArmState → Arm.ArmState} {ok : Arm.ArmState → Lab → Prop}
    {u t' : Arm.ArmState × Mon} {ls : List Lab} (hr : PRun Policy.arm f ok u ls t') {k : Nat}
    (hk : k ≤ ls.length) (ext : List (Clif.Frame × List Clif.ValueId)) {s : Clif.State}
    {trS : List (List (Ev SKind BVal))} {t : TState} {ψ : Nat × Nat → Nat × Nat}
    {P : Nat → Prop} (hrun : CRun env p (.run s) trS t)
    (hx : CallCompose.XClosed (evTr (ls.take k)))
    (href : Refines Maps P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D NS : Nat → Prop} (hD : ∀ a, D a → P a ∨ U a ∨ NS a)
    (hu : Uniform trS) (hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n)
    (hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ NS x.loc) (hb : ∀ l, P l → Bnd l) :
    (∃ (trS' : List (List (Ev SKind BVal))) (s1 : Clif.State), trS' <+: trS ∧
        RealizedT env p Bnd ls k (encT U (.run (pushC ext s)))
          (encT (maskAfter U trS') (.run (pushC ext s1))) D (fun a => D a ∨ P a) ∧
        (∀ s', t = .run s' → s1 = s') ∧ (∀ v, t = .ret v → CStep env p (.run s1) [] (.ret v))) ∨
      ∃ k' ≤ k, ∃ (trS' : List (List (Ev SKind BVal))) (j : Nat) (evs : List (Ev SKind BVal)),
        trS' <+: trS ∧
        trS'[j]? = some evs ∧ ∃ sj : Clif.State, ∃ t'' : TState,
        RealizedT env p Bnd ls k' (encT U (.run (pushC ext s)))
          (encT (maskAfter U (trS'.take j)) (.run sj)) D (fun a => D a ∨ P a) ∧
        CStep env p (.run sj) evs t'' ∧ ReadsMasked (maskAfter U (trS'.take j)) evs :=
  (realizedT_liftW hr hk ext hrun hx href hD hu hpos hns hb).imp
    (fun ⟨trS', s1, hp, hR, h1, h2⟩ => ⟨trS', s1, hp, hR.mono_out fun _ h => h.sub, h1, h2⟩)
    fun ⟨k', hk', trS', j, evs, hp, hj, sj, t'', hR, hs, hm⟩ =>
      ⟨k', hk', trS', j, evs, hp, hj, sj, t'', hR.mono_out fun _ h => h.sub, hs, hm⟩

end Concurrency.CallSegLift
