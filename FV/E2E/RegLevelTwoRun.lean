import FV.E2E.RegLevelJointC

/-!
# The two-run induction (SEM1 #537, item (3))

`forward2` on the counted joint realisation (`RealizesJCP.countedRun2`): along a run of pair steps
of the counted semantics, from related shape-equal configurations at counter `0`, the two
machines realise both allocated-code runs jointly, the same number of steps, ending at
shape-equal configurations related to the pair run's end (`forward2C`), or at the instruction
item of a pair state that steps (`forward2C_op`); the joint trace holds at every index.
-/

namespace Backend.Proof

open Backend E2E

section
variable {V W S : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- **The two-run induction**, counted (module doc). -/
theorem forward2C {sem sem' : Nat → ISem V W} {step step' : S → S}
    {K : MConf V W → MConf V W → Prop} {J : S → MConf V W → S → MConf V W → Prop}
    {T : S → S → Prop} {C C' : S → Prop} {P P' : Nat → S → Prop} {s0 s0' : S}
    (h : ∀ n n', RealizesJCP vc rf (sem n) (sem' n') keep step step' K J T C C' (P n) (P' n'))
    (hP : ∀ i, P (countIn C step s0 i) (iterN step i s0))
    (hP' : ∀ i, P' (countIn C' step' s0' i) (iterN step' i s0'))
    {R R' : MConf V (W × Nat) → VConf V (W × Nat) → Prop}
    (hR : IsSimulationS vc rf keep (ISem.counted sem) R)
    (hR' : IsSimulationS vc rf keep (ISem.counted sem') R')
    {PI : VConf V (W × Nat) → VConf V (W × Nat) → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K (e.mapW Prod.fst) (e'.mapW Prod.fst))
    {v v' x x' : VConf V (W × Nat)}
    (hp : Star (PStep vc (ISem.counted sem) (ISem.counted sem') PI) (v, v') (x, x'))
    {c c' : MConf V (W × Nat)} (hr : R c v) (hr' : R' c' v') (hpi : PI v v')
    (hsh : MConf.ShapeEq c c') (hc0 : c.world.2 = 0) (hc0' : c'.world.2 = 0)
    (hj : J s0 (c.mapW Prod.fst) s0' (c'.mapW Prod.fst)) :
    ∃ N d d', J (iterN step N s0) (d.mapW Prod.fst) (iterN step' N s0') (d'.mapW Prod.fst) ∧
      countIn C step s0 N = d.world.2 ∧ countIn C' step' s0' N = d'.world.2 ∧
      R d x ∧ R' d' x' ∧ MConf.ShapeEq d d' ∧ ∀ i < N, T (iterN step i s0) (iterN step' i s0') := by
  have hJ := RealizesJCP.countedRun2 h hP hP'
  obtain ⟨N, d, d', ⟨hj', hk, hk', i, hi, hi'⟩, hrd, hrd', hsh', ht⟩ :=
    forward2 (s := (s0, 0)) (s' := (s0', 0)) hR hR' hK hJ hp hr hr' hpi hsh
      ⟨hj, hc0.symm, hc0'.symm, 0, rfl, rfl⟩
  rw [iterN_stepC, iterN_stepC] at hj'
  rw [iterN_stepC] at hk
  rw [iterN_stepC] at hk'
  refine ⟨N, d, d', hj', ?_, ?_, hrd, hrd', hsh', fun j hj => ?_⟩
  · simpa using hk
  · simpa using hk'
  · have := ht j hj
    rw [iterN_stepC, iterN_stepC] at this
    exact this

/-- **The two-run induction to an instruction item**, counted: at a pair state with a pair step,
both machines advanced past the pending moves. -/
theorem forward2C_op {sem sem' : Nat → ISem V W} {step step' : S → S}
    {K : MConf V W → MConf V W → Prop} {J : S → MConf V W → S → MConf V W → Prop}
    {T : S → S → Prop} {C C' : S → Prop} {P P' : Nat → S → Prop} {s0 s0' : S}
    (h : ∀ n n', RealizesJCP vc rf (sem n) (sem' n') keep step step' K J T C C' (P n) (P' n'))
    (hP : ∀ i, P (countIn C step s0 i) (iterN step i s0))
    (hP' : ∀ i, P' (countIn C' step' s0' i) (iterN step' i s0'))
    {R R' : MConf V (W × Nat) → VConf V (W × Nat) → Prop}
    (hR : IsSimulationS vc rf keep (ISem.counted sem) R)
    (hR' : IsSimulationS vc rf keep (ISem.counted sem') R')
    {PI : VConf V (W × Nat) → VConf V (W × Nat) → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K (e.mapW Prod.fst) (e'.mapW Prod.fst))
    {v v' x x' y y' : VConf V (W × Nat)}
    (hp : Star (PStep vc (ISem.counted sem) (ISem.counted sem') PI) (v, v') (x, x'))
    (hy : PStep vc (ISem.counted sem) (ISem.counted sem') PI (x, x') (y, y'))
    (hpix : PI x x')
    {c c' : MConf V (W × Nat)} (hr : R c v) (hr' : R' c' v') (hpi : PI v v')
    (hsh : MConf.ShapeEq c c') (hc0 : c.world.2 = 0) (hc0' : c'.world.2 = 0)
    (hj : J s0 (c.mapW Prod.fst) s0' (c'.mapW Prod.fst)) :
    ∃ N b k a its m w a' its' m' w',
      J (iterN step N s0) ((MConf.run ⟨b, .op k a :: its, m, w⟩ : MConf V (W × Nat)).mapW Prod.fst)
        (iterN step' N s0') ((MConf.run ⟨b, .op k a' :: its', m', w'⟩ : MConf V (W × Nat)).mapW
          Prod.fst) ∧
      countIn C step s0 N = w.2 ∧ countIn C' step' s0' N = w'.2 ∧
      R (.run ⟨b, .op k a :: its, m, w⟩) x ∧ R' (.run ⟨b, .op k a' :: its', m', w'⟩) x' ∧
      ∀ i < N, T (iterN step i s0) (iterN step' i s0') := by
  have hJ := RealizesJCP.countedRun2 h hP hP'
  obtain ⟨N, d, d', hjd, hrd, hrd', hshd, ht⟩ :=
    forward2 (s := (s0, 0)) (s' := (s0', 0)) hR hR' hK hJ hp hr hr' hpi hsh
      ⟨hj, hc0.symm, hc0'.symm, 0, rfl, rfl⟩
  obtain ⟨hx, hx', hsa, -⟩ := hy
  obtain ⟨N2, b, k, a, its, m, w, a', its', m', w', ⟨hj2, hk, hk', -⟩, hr2, hr2', -, ht2⟩ :=
    forward2_op hR hR' hK hJ hx hx' hsa hpix _ d d' _ _ (Nat.le_refl _) hrd hrd' hshd hjd
  have e1 : iterN (stepC C step) N2 (iterN (stepC C step) N (s0, 0)) =
      (iterN step (N + N2) s0, countIn C step s0 (N + N2)) := by
    rw [← iterN_add, iterN_stepC, Nat.zero_add]
  have e2 : iterN (stepC C' step') N2 (iterN (stepC C' step') N (s0', 0)) =
      (iterN step' (N + N2) s0', countIn C' step' s0' (N + N2)) := by
    rw [← iterN_add, iterN_stepC, Nat.zero_add]
  rw [e1, e2] at hj2
  rw [e1] at hk
  rw [e2] at hk'
  refine ⟨N + N2, b, k, a, its, m, w, a', its', m', w', hj2, hk, hk', hr2, hr2', ?_⟩
  have htt := trace_add2 (T := fun (p p' : S × Nat) => T p.1 p'.1) ht ht2
  intro j hj
  have := htt j hj
  rw [iterN_stepC, iterN_stepC] at this
  exact this

end

end Backend.Proof
