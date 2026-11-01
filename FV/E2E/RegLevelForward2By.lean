import FV.E2E.RegLevelForward2
import FV.E2E.PerEdgeSimulationS

/-!
# Joint forward realization over any deterministic code step

The joint (two-run) realization lemmas of FV/E2E/RegLevelForward2 (`IsSimulationS.blkEq`,
`IsSimulationS.step2`, `forward2`, `forward2_op`) with the two code steps as parameters, over
`IsSimulationSBy` and the pair step `PStepBy`. The legacy statements are unchanged; the
specializations `forward2By_perEdge`/`forward2By_op_perEdge` serve per-successor code (`VStepAt`).
-/

namespace Backend.Proof

open Backend

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- **A pair step** over two code steps: each run steps, to configurations at the same place
satisfying the pair invariant `PI`. -/
def PStepBy (vstep vstep' : VConf V W → VConf V W → Prop) (PI : VConf V W → VConf V W → Prop)
    (p p' : VConf V W × VConf V W) : Prop :=
  vstep p.1 p'.1 ∧ vstep' p.2 p'.2 ∧ VConf.SameAt p'.1 p'.2 ∧ PI p'.1 p'.2

theorem PStep.toBy {sem sem' : ISem V W} {PI : VConf V W → VConf V W → Prop}
    {p p' : VConf V W × VConf V W} (h : PStep vc sem sem' PI p p') :
    PStepBy (VStep vc sem) (VStep vc sem') PI p p' := h

/-- Configurations related to VCode configurations at the same place are at the same block. -/
theorem IsSimulationSBy.blkEq {sem sem' : ISem V W} {vstep vstep' : VConf V W → VConf V W → Prop}
    {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationSBy vc rf keep vstep sem R) (hR' : IsSimulationSBy vc rf keep vstep' sem' R')
    {c c' : MConf V W} {v v' : VConf V W} (h : R c v) (h' : R' c' v')
    (hs : VConf.SameAt v v') : MConf.BlkEq c c' := by
  cases c with
  | run s =>
    obtain ⟨vs, rfl, hb⟩ := hR.blk h
    cases c' with
    | run s' =>
      obtain ⟨vs', rfl, hb'⟩ := hR'.blk h'
      show s.b = s'.b
      rw [← hb, ← hb']; exact hs.1
    | ret => rw [hR'.ret h'] at hs; exact hs.elim
    | halt => rw [hR'.halt h'] at hs; exact hs.elim
  | ret =>
    rw [hR.ret h] at hs
    cases c' with
    | run s' => obtain ⟨vs', rfl, -⟩ := hR'.blk h'; exact hs.elim
    | ret => trivial
    | halt => rw [hR'.halt h'] at hs; exact hs.elim
  | halt =>
    rw [hR.halt h] at hs
    cases c' with
    | run s' => obtain ⟨vs', rfl, -⟩ := hR'.blk h'; exact hs.elim
    | ret => rw [hR'.ret h'] at hs; exact hs.elim
    | halt => trivial

/-- **One step of both allocated-code runs**: from shape-equal configurations related to `v`,
`v'`, whose VCode steps reach `x`, `x'` at the same place, two `MStep` successors are shape-equal,
and either both were moves (related to `v`, `v'`, smaller measure) or both ops (related to `x`,
`x'`). -/
theorem IsSimulationSBy.step2 {sem sem' : ISem V W} {vstep vstep' : VConf V W → VConf V W → Prop}
    (det : ∀ v v1 v2,vstep v v1 → vstep v v2 → v1 = v2) (det' : ∀ v v1 v2,vstep' v v1 → vstep' v v2 → v1 = v2)
    {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationSBy vc rf keep vstep sem R) (hR' : IsSimulationSBy vc rf keep vstep' sem' R')
    {c c' : MConf V W} {v v' x x' : VConf V W} (h : R c v) (h' : R' c' v')
    (hsh : MConf.ShapeEq c c') (hx : vstep v x) (hx' : vstep' v' x')
    (hsa : VConf.SameAt x x') {e e' : MConf V W} (he : MStep vc sem keep rf c e)
    (he' : MStep vc sem' keep rf c' e') :
    MConf.ShapeEq e e' ∧
      ((R e v ∧ R' e' v' ∧ e.measure < c.measure) ∨ (R e x ∧ R' e' x')) := by
  cases he with
  | @move b src dst its m w =>
    cases c' with
    | run s' =>
      obtain ⟨b', its', m', w'⟩ := s'
      obtain ⟨rfl, rfl⟩ := hsh
      cases he' with
      | move =>
        exact ⟨⟨rfl, rfl⟩, .inl ⟨hR.move h, hR'.move h', by simp [MConf.measure]⟩⟩
    | ret => exact hsh.elim
    | halt => exact hsh.elim
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 e hvb hi hops hsz hsem hlen hho hcl hn =>
    have hs0 : MStep vc sem keep rf (.run ⟨b, .op k allocs :: its, m, w⟩) e :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    cases c' with
    | run s' =>
      obtain ⟨b', its', m', w''⟩ := s'
      obtain ⟨rfl, rfl⟩ := hsh
      obtain ⟨y, hy, hry⟩ := hR.opStep h hs0
      obtain ⟨y', hy', hry'⟩ := hR'.opStep h' he'
      rw [det _ _ _ hy hx] at hry
      rw [det' _ _ _ hy' hx'] at hry'
      have hsh0 : MConf.ShapeEq (.run ⟨b, .op k allocs :: its, m, w⟩ : MConf V W)
          (.run ⟨b, .op k allocs :: its, m', w''⟩) := ⟨rfl, rfl⟩
      exact ⟨MStep.shapeEq_of_blkEq hsh0 hs0 he' (IsSimulationSBy.blkEq hR hR' hry hry' hsa), .inr ⟨hry, hry'⟩⟩
    | ret => exact hsh.elim
    | halt => exact hsh.elim

end

section
variable {V W S : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

theorem forward2By_aux {sem sem' : ISem V W} {vstep vstep' : VConf V W → VConf V W → Prop}
    (det : ∀ v v1 v2,vstep v v1 → vstep v v2 → v1 = v2) (det' : ∀ v v1 v2,vstep' v v1 → vstep' v v2 → v1 = v2)
    {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationSBy vc rf keep vstep sem R) (hR' : IsSimulationSBy vc rf keep vstep' sem' R')
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {p p' : VConf V W × VConf V W} (hp : Star (PStepBy vstep vstep' PI) p p') :
    ∀ k (c c' : MConf V W) s s', c.measure ≤ k → R c p.1 → R' c' p.2 → PI p.1 p.2 →
      MConf.ShapeEq c c' → J s c s' c' →
      ∃ n d d', J (iterN step n s) d (iterN step' n s') d' ∧ R d p'.1 ∧ R' d' p'.2 ∧
        MConf.ShapeEq d d' ∧ ∀ i < n, T (iterN step i s) (iterN step' i s') := by
  induction hp with
  | refl =>
    exact fun _ c c' s s' _ hr hr' _ hsh hj =>
      ⟨0, c, c', hj, hr, hr', hsh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | @step p p1 p' h1 _ ih =>
    obtain ⟨hx, hx', hsa, hpi⟩ := h1
    intro k
    induction k with
    | zero =>
      intro c c' s s' hk hr hr' hpi0 hsh hj
      obtain ⟨e, he⟩ := hR.progress hr hx
      obtain ⟨e', he'⟩ := hR'.progress hr' hx'
      obtain ⟨n1, d, d', hd, hd', hj', ht1⟩ := hJ s c s' c' e e' hj he he' fun e e' a b => by
        obtain ⟨hs, hc⟩ := IsSimulationSBy.step2 det det' hR hR' hr hr' hsh hx hx' hsa a b
        refine ⟨hs, ?_⟩
        rcases hc with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
        · exact hK _ _ _ _ h1 h2 hpi0
        · exact hK _ _ _ _ h1 h2 hpi
      obtain ⟨hsh', hc⟩ := IsSimulationSBy.step2 det det' hR hR' hr hr' hsh hx hx' hsa hd hd'
      rcases hc with ⟨-, -, hlt⟩ | ⟨hrd, hrd'⟩
      · omega
      · obtain ⟨n2, f, f', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ih d.measure d d' _ _ (Nat.le_refl _) hrd hrd' hpi hsh' hj'
        exact ⟨n1 + n2, f, f', by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2,
          trace_add2 ht1 ht2⟩
    | succ k ihk =>
      intro c c' s s' hk hr hr' hpi0 hsh hj
      obtain ⟨e, he⟩ := hR.progress hr hx
      obtain ⟨e', he'⟩ := hR'.progress hr' hx'
      obtain ⟨n1, d, d', hd, hd', hj', ht1⟩ := hJ s c s' c' e e' hj he he' fun e e' a b => by
        obtain ⟨hs, hc⟩ := IsSimulationSBy.step2 det det' hR hR' hr hr' hsh hx hx' hsa a b
        refine ⟨hs, ?_⟩
        rcases hc with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
        · exact hK _ _ _ _ h1 h2 hpi0
        · exact hK _ _ _ _ h1 h2 hpi
      obtain ⟨hsh', hc⟩ := IsSimulationSBy.step2 det det' hR hR' hr hr' hsh hx hx' hsa hd hd'
      rcases hc with ⟨hrd, hrd', hlt⟩ | ⟨hrd, hrd'⟩
      · obtain ⟨n2, f, f', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ihk d d' _ _ (by omega) hrd hrd' hpi0 hsh' hj'
        exact ⟨n1 + n2, f, f', by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2,
          trace_add2 ht1 ht2⟩
      · obtain ⟨n2, f, f', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ih d.measure d d' _ _ (Nat.le_refl _) hrd hrd' hpi hsh' hj'
        exact ⟨n1 + n2, f, f', by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2,
          trace_add2 ht1 ht2⟩

/-- **Joint forward simulation.** Along a run of pair steps from configurations related to the
allocated-code configurations (shape-equal, the pair invariant at the start), both machines
realise both runs jointly: after the same number of steps they reach states satisfying `J` at
shape-equal configurations related to the pair run's end. -/
theorem forward2By {sem sem' : ISem V W} {vstep vstep' : VConf V W → VConf V W → Prop}
    (det : ∀ v v1 v2,vstep v v1 → vstep v v2 → v1 = v2) (det' : ∀ v v1 v2,vstep' v v1 → vstep' v v2 → v1 = v2)
    {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationSBy vc rf keep vstep sem R) (hR' : IsSimulationSBy vc rf keep vstep' sem' R')
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {v v' x x' : VConf V W} (hp : Star (PStepBy vstep vstep' PI) (v, v') (x, x'))
    {c c' : MConf V W} {s s' : S} (hr : R c v) (hr' : R' c' v') (hpi : PI v v')
    (hsh : MConf.ShapeEq c c') (hj : J s c s' c') :
    ∃ n d d', J (iterN step n s) d (iterN step' n s') d' ∧ R d x ∧ R' d' x' ∧
      MConf.ShapeEq d d' ∧ ∀ i < n, T (iterN step i s) (iterN step' i s') :=
  forward2By_aux det det' hR hR' hK hJ hp _ c c' s s' (Nat.le_refl _) hr hr' hpi hsh hj

/-- **Both machines advanced past the pending moves**: at a pair state with a pair step, from
related shape-equal configurations, the machines reach (after the same number of steps) states
satisfying `J` at shape-equal instruction items related to the pair state. -/
theorem forward2By_op {sem sem' : ISem V W} {vstep vstep' : VConf V W → VConf V W → Prop}
    (det : ∀ v v1 v2,vstep v v1 → vstep v v2 → v1 = v2) (det' : ∀ v v1 v2,vstep' v v1 → vstep' v v2 → v1 = v2)
    {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationSBy vc rf keep vstep sem R) (hR' : IsSimulationSBy vc rf keep vstep' sem' R')
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {v v' x x' : VConf V W} (hx : vstep v x) (hx' : vstep' v' x')
    (hsa : VConf.SameAt x x') (hpi : PI v v') :
    ∀ k (c c' : MConf V W) s s', c.measure ≤ k → R c v → R' c' v' → MConf.ShapeEq c c' →
      J s c s' c' →
      ∃ n b k a its m w a' its' m' w', J (iterN step n s) (.run ⟨b, .op k a :: its, m, w⟩)
          (iterN step' n s') (.run ⟨b, .op k a' :: its', m', w'⟩) ∧
        R (.run ⟨b, .op k a :: its, m, w⟩) v ∧ R' (.run ⟨b, .op k a' :: its', m', w'⟩) v' ∧
        MConf.ShapeEq (.run ⟨b, .op k a :: its, m, w⟩) (.run ⟨b, .op k a' :: its', m', w'⟩) ∧
        ∀ i < n, T (iterN step i s) (iterN step' i s') := by
  intro k
  induction k with
  | zero =>
    intro c c' s s' hk hr hr' hsh hj
    obtain ⟨e, he⟩ := hR.progress hr hx
    cases he with
    | move => simp [MConf.measure] at hk
    | op =>
      cases c' with
      | run s1 =>
        obtain ⟨b', its', m', w'⟩ := s1
        obtain ⟨rfl, rfl⟩ := hsh
        exact ⟨0, _, _, _, _, _, _, _, _, _, _, hj, hr, hr', ⟨rfl, rfl⟩,
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      | ret => exact hsh.elim
      | halt => exact hsh.elim
  | succ k ihk =>
    intro c c' s s' hk hr hr' hsh hj
    obtain ⟨e, he⟩ := hR.progress hr hx
    cases he with
    | @move b src dst its m w =>
      cases c' with
      | run s1 =>
        obtain ⟨b', its', m', w'⟩ := s1
        obtain ⟨rfl, rfl⟩ := hsh
        have hm : MStep vc sem keep rf (.run ⟨b, .move src dst :: its, m, w⟩)
            (.run ⟨b, its, upd m dst (m src), w⟩) := MStep.move
        have hm' : MStep vc sem' keep rf (.run ⟨b, .move src dst :: its, m', w'⟩)
            (.run ⟨b, its, upd m' dst (m' src), w'⟩) := MStep.move
        obtain ⟨n1, d, d', hd, hd', hj', ht1⟩ := hJ s _ s' _ _ _ hj hm hm' fun e e' a b' => by
          obtain ⟨hs, -⟩ := IsSimulationSBy.step2 det det' hR hR' hr hr' ⟨rfl, rfl⟩ hx hx' hsa a b'
          refine ⟨hs, ?_⟩
          cases a with
          | move =>
            cases b' with
            | move => exact hK _ _ _ _ (hR.move hr) (hR'.move hr') hpi
        obtain ⟨hsh', -⟩ := IsSimulationSBy.step2 det det' hR hR' hr hr' ⟨rfl, rfl⟩ hx hx' hsa hd hd'
        have hrd : R d v ∧ R' d' v' ∧ d.measure < (MConf.run ⟨b, .move src dst :: its, m, w⟩ :
            MConf V W).measure := by
          cases hd with
          | move => cases hd' with
            | move => exact ⟨hR.move hr, hR'.move hr', by simp [MConf.measure]⟩
        obtain ⟨hrd, hrd', hlt⟩ := hrd
        obtain ⟨n2, b2, k2, a2, its2, m2, w2, a2', its2', m2', w2', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ihk d d' _ _ (by omega) hrd hrd' hsh' hj'
        exact ⟨n1 + n2, b2, k2, a2, its2, m2, w2, a2', its2', m2', w2',
          by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2, trace_add2 ht1 ht2⟩
      | ret => exact hsh.elim
      | halt => exact hsh.elim
    | op =>
      cases c' with
      | run s1 =>
        obtain ⟨b', its', m', w'⟩ := s1
        obtain ⟨rfl, rfl⟩ := hsh
        exact ⟨0, _, _, _, _, _, _, _, _, _, _, hj, hr, hr', ⟨rfl, rfl⟩,
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      | ret => exact hsh.elim
      | halt => exact hsh.elim

/-- The joint forward simulation for per-successor code runs. -/
theorem forward2By_perEdge {edges : Array (Array (Array Reg))} {sem sem' : ISem V W}
    {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationSBy vc rf keep (VStepAt vc edges sem) sem R)
    (hR' : IsSimulationSBy vc rf keep (VStepAt vc edges sem') sem' R')
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x',R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {v v' x x' : VConf V W}
    (hp : Star (PStepBy (VStepAt vc edges sem) (VStepAt vc edges sem') PI) (v,v') (x,x'))
    {c c' : MConf V W} {s s' : S} (hr : R c v) (hr' : R' c' v') (hpi : PI v v')
    (hsh : MConf.ShapeEq c c') (hj : J s c s' c') :
    ∃ n d d',J (iterN step n s) d (iterN step' n s') d' ∧ R d x ∧ R' d' x' ∧
      MConf.ShapeEq d d' ∧ ∀ i < n,T (iterN step i s) (iterN step' i s') :=
  forward2By (vstep := VStepAt vc edges sem) (vstep' := VStepAt vc edges sem')
    (fun _ _ _ => PerEdge.VStepAt_det) (fun _ _ _ => PerEdge.VStepAt_det) hR hR' hK hJ hp hr hr' hpi hsh hj

end

end Backend.Proof
