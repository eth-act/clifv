import FV.E2E.RegLevelTwoRunT

/-!
# Two activations in lock-step up to a pair state (SEM1 #537, #713, determinism step)

`RL.twoRunCT` needs a pair run that returns, in one counted semantics for each activation whose
call contracts hold at every index. The prefix two-run route (#713) runs the second activation
with the contracts of its first `N` calls only (`ExtSemI.upTo`), so the pair run is cut at a pair
state `(x, x')`: the step out of it (the call number `N`) is one of the *full* semantics, not of
the cut one. The joint realisation needs that step only to know that the machines reach the
instruction item of `x` past the pending moves (`forward2_op`), and the moves do not depend on
the semantics:

* `forward2_opB`, `forward2C_opB`: `forward2_op`, `forward2C_op` with the step out of `(x, x')`
  in other semantics (`semB`, `semB'`, with simulations by the same relations);
* **`RL.twoRunCTN`**: `RL.twoRunCT` up to such a pair state: the prologues, the joint trace at
  every index before the instruction item of `x`, the joint invariant `JR` there, the machine call
  count there equal to the counter of `x`.
-/

namespace Backend.Proof

open Backend E2E

section
variable {V W S : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- **`forward2_op` with the step out of the first configuration in another semantics** (module
doc; the second run reaches its instruction item by the shape equality). -/
theorem forward2_opB {sem sem' semB : ISem V W} {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationS vc rf keep sem R) (hR' : IsSimulationS vc rf keep sem' R')
    (hRB : IsSimulationS vc rf keep semB R)
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {v v' x : VConf V W} (hx : VStep vc semB v x)
    (hpi : PI v v') :
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
    obtain ⟨e, he⟩ := hRB.progress hr hx
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
    obtain ⟨e, he⟩ := hRB.progress hr hx
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
          cases a with
          | move =>
            cases b' with
            | move => exact ⟨⟨rfl, rfl⟩, hK _ _ _ _ (hR.move hr) (hR'.move hr') hpi⟩
        have hrd : R d v ∧ R' d' v' ∧ MConf.ShapeEq d d' ∧
            d.measure < (MConf.run ⟨b, .move src dst :: its, m, w⟩ : MConf V W).measure := by
          cases hd with
          | move => cases hd' with
            | move => exact ⟨hR.move hr, hR'.move hr', ⟨rfl, rfl⟩, by simp [MConf.measure]⟩
        obtain ⟨hrd, hrd', hsh', hlt⟩ := hrd
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

/-- **`forward2C_op` with the step out of the first configuration in other semantics** (module
doc). -/
theorem forward2C_opB {sem sem' semB : Nat → ISem V W} {step step' : S → S}
    {K : MConf V W → MConf V W → Prop} {J : S → MConf V W → S → MConf V W → Prop}
    {T : S → S → Prop} {C C' : S → Prop} {P P' : Nat → S → Prop} {s0 s0' : S}
    (h : ∀ n n', RealizesJCP vc rf (sem n) (sem' n') keep step step' K J T C C' (P n) (P' n'))
    (hP : ∀ i, P (countIn C step s0 i) (iterN step i s0))
    (hP' : ∀ i, P' (countIn C' step' s0' i) (iterN step' i s0'))
    {R R' : MConf V (W × Nat) → VConf V (W × Nat) → Prop}
    (hR : IsSimulationS vc rf keep (ISem.counted sem) R)
    (hR' : IsSimulationS vc rf keep (ISem.counted sem') R')
    (hRB : IsSimulationS vc rf keep (ISem.counted semB) R)
    {PI : VConf V (W × Nat) → VConf V (W × Nat) → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K (e.mapW Prod.fst) (e'.mapW Prod.fst))
    {v v' x x' y : VConf V (W × Nat)}
    (hp : Star (PStep vc (ISem.counted sem) (ISem.counted sem') PI) (v, v') (x, x'))
    (hy : VStep vc (ISem.counted semB) x y)
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
  obtain ⟨N2, b, k, a, its, m, w, a', its', m', w', ⟨hj2, hk, hk', -⟩, hr2, hr2', -, ht2⟩ :=
    forward2_opB hR hR' hRB hK hJ hy hpix _ d d' _ _ (Nat.le_refl _) hrd hrd' hshd hjd
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

set_option maxHeartbeats 2000000 in
/-- **`RL.twoRunCT` up to a pair state** (module doc): along a pair run to `(x, x')` whose first
configuration steps in some counted guarded semantics (`XB`, `OkB`; the step itself is not
realised), both machines run the prologue, are jointly realised to the instruction item of
`(x, x')` (index `N` after the prologue, the joint trace `Lk` before it, `JR` at it), where the
machine call counts of both runs are the counters of `x`, `x'`. -/
theorem RL.twoRunCTN {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
    (hRn : ∀ n, ({ R with X := XI.at n } : RL).Wf)
    (hRn' : ∀ n, ({ R with s0 := t0, G := G', X := XI'.at n } : RL).Wf)
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hcheck : CheckedAt R.vc R.rf cc ins a0) (ρ₀ : Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ ρ₀ (fun r => m₀ (.reg r)))
    {ra ra' : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hent' : AbiCall R.fb R.base ra' t0) {w₀ w₀' : Arm.ArmState}
    (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (hbe' : BodyEntryW ({ R with s0 := t0, G := G' } : RL).F R.vc.EntryArg R.af t0 w₀')
    (OkG OkG' : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : ∀ n, CalleeOkGP (fun u => OnCall ({ R with X := XI.at 0 } : RL).step R.fa R.base R.s0 n u ∧
        spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) (XI.at n) R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → ∀ n, CalleeTryOkGP
      (fun u => OnCall ({ R with X := XI.at 0 } : RL).step R.fa R.base R.s0 n u ∧ spOf u = R.spB)
      R.F R.K R.G R.s0 (CallAt R.fa R.base) (XI.at n) R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → ∀ n, TlsOk R.F R.K (XI.at n) R.H)
    (hC' : ∀ n, CalleeOkGP (fun u =>
        OnCall ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step R.fa R.base t0 n u ∧
        spOf u = ({ R with s0 := t0, G := G' } : RL).spB)
      ({ R with s0 := t0, G := G' } : RL).F R.K G' t0 (CallAt R.fa R.base) (XI'.at n) R.H
      R.vc.CallSite R.gv)
    (hT' : R.vc.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        OnCall ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step R.fa R.base t0 n u ∧
        spOf u = ({ R with s0 := t0, G := G' } : RL).spB)
      ({ R with s0 := t0, G := G' } : RL).F R.K G' t0 (CallAt R.fa R.base) (XI'.at n) R.H
      R.vc.TrySite R.gv)
    (hTls' : R.vc.hasTls = true → ∀ n,
      TlsOk ({ R with s0 := t0, G := G' } : RL).F R.K (XI'.at n) R.H)
    (hcov : FormsCovered R.ctx R.vc)
    (K : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Prop)
    (LB : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Arm.ArmState → Arm.ArmState → Prop)
    (OkS OkS' : MConf CV Arm.ArmState → MConf CV Arm.ArmState →
      Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hG : ∀ n c c' d, K c c' →
      MStep R.vc (({ R with X := XI.at n } : RL).semGS OkG) ckeep R.rf c d →
      MStep R.vc (({ R with X := XI.at n } : RL).semGS (OkS c c')) ckeep R.rf c d)
    (hG' : ∀ n c c' d, K c c' →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semGS OkG') ckeep R.rf c' d →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semGS (OkS' c c')) ckeep R.rf
        c' d)
    (Lk : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ c c' i u u', Lk c c' i u u' → Arm.r .PC u = Arm.r .PC u')
    (hstart : ∀ c c' s s', K c c' → LB c c' s s' → Lk c c' 0 s s')
    (hstep : ∀ n n' c c' i u u', K c c' →
      ({ R with X := XI.at n } : RL).InSeg (OkS c c') c i u →
      ({ R with s0 := t0, G := G', X := XI'.at n' } : RL).InSeg (OkS' c c') c' i u' →
      (({ R with X := XI.at n } : RL).GoodX u ∧
        ({ R with X := XI.at n } : RL).WReadsIn (OkS c c') u) →
      (({ R with s0 := t0, G := G', X := XI'.at n' } : RL).GoodX u' ∧
        ({ R with s0 := t0, G := G', X := XI'.at n' } : RL).WReadsIn (OkS' c c') u') →
      Lk c c' i u u' → Lk c c' (i + 1) (({ R with X := XI.at 0 } : RL).step u)
        (({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step u'))
    (hend : ∀ c c' d d' i u u', K c c' → K d d' → MConf.ShapeEq d d' →
      (∃ W : Nat × PState × List Line, QWA R u W.1 W.2.1 W.2.2 d ∧
        QWA ({ R with s0 := t0, G := G' } : RL) u' W.1 W.2.1 W.2.2 d') →
      Lk c c' i u u' → LB d d' u u')
    {PI : VConf CV (Arm.ArmState × Nat) → VConf CV (Arm.ArmState × Nat) → Prop}
    (hK : ∀ e e' x x',
      Match cc ins ckeep (fun r => locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0) (.reg r)) e x →
      Match cc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
        RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0) (.reg r)) e' x' →
      PI x x' → K (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0))
    {x x' y : VConf CV (Arm.ArmState × Nat)}
    (hp : Star (PStep R.vc (csemVIGS R.gv R.F R.ctx XI OkG)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI)
      (VConf.init ρ₀ (w₀, 0), VConf.init ρ₀ (w₀', 0)) (x, x'))
    (hpi0 : PI (VConf.init ρ₀ (w₀, 0)) (VConf.init ρ₀ (w₀', 0))) (hpix : PI x x')
    {XB : ExtSemI} {OkB : Arm.ArmState → (BitVec 64 → Prop) → Prop}
    (hy : VStep R.vc (csemVIGS R.gv R.F R.ctx XB OkB) x y) :
    ∃ N b k a its m w ρ a' its' m' w' ρ' nc nc',
      (∀ i < (prologueSteps R.af.saves R.af.frameSize R.af.isCaller),
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) K LB
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) R.s0)
        (.run ⟨b, .op k a :: its, m, w⟩)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) t0) (.run ⟨b, .op k a' :: its', m', w'⟩) ∧
      countIn (RL.CallSt R) ({ R with X := XI.at 0 } : RL).step R.s0
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) = nc ∧
      countIn (RL.CallSt R) ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step t0
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) = nc' ∧
      x = .run ⟨b, k, ρ, (w, nc)⟩ ∧ x' = .run ⟨b, k, ρ', (w', nc')⟩ := by
  let R0 : RL := { R with X := XI.at 0 }
  let R0' : RL := { R with s0 := t0, G := G', X := XI'.at 0 }
  let R'' : RL := { R with s0 := t0, G := G' }
  have hR0 : R0.Wf := hRn 0
  have hR0' : R0'.Wf := hRn' 0
  obtain ⟨n0, hn0, ht0, hq0, hA0, -⟩ := q_initNA (R := R0) (Y := fun _ => True) hR0 hent hbe
  obtain ⟨n0', hn0', ht0', hq0', hA0', -⟩ :=
    q_initNA (R := R0') (Y := fun _ => True) hR0' hent' hbe'
  have e0 : n0 = (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) := hn0
  have e0' : n0' = (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) := hn0'
  subst e0 e0'
  let s₁ := iterN R0.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0
  let s₁' := iterN R0'.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0
  obtain ⟨hSim, hinit⟩ := isSimulationS_match (sem := csemVIGS R.gv R.F R.ctx XI OkG)
    (keep := ckeep) hcheck (locVal R.fr s₁) ρ₀ (w₀, 0) (hsel _)
  obtain ⟨hSim', hinit'⟩ := isSimulationS_match (sem := csemVIGS R.gv R''.F R.ctx XI' OkG')
    (keep := ckeep) hcheck (locVal R.fr s₁') ρ₀ (w₀', 0) (hsel _)
  obtain ⟨hSimB, -⟩ := isSimulationS_match (sem := csemVIGS R.gv R.F R.ctx XB OkB)
    (keep := ckeep) hcheck (locVal R.fr s₁) ρ₀ (w₀, 0) (hsel _)
  have hP0 : countIn (RL.CallSt R) R0.step R.s0 (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) = 0 :=
    countIn_zero_of fun i hi => (ht0 i hi).1.2
  have hP0' : countIn (RL.CallSt R) R0'.step t0 (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) = 0 :=
    countIn_zero_of fun i hi => (ht0' i hi).1.2
  -- the prologue does not read the external semantics
  have hRw : R.Wf := ⟨hR0.check, hR0.alloc, hR0.emit, hR0.layout, hR0.lm, hR0.fit, hR0.stack,
    hR0.psF, hR0.prog0, hR0.gfree⟩
  have hRw'' : R''.Wf := ⟨hR0'.check, hR0'.alloc, hR0'.emit, hR0'.layout, hR0'.lm, hR0'.fit,
    hR0'.stack, hR0'.psF, hR0'.prog0, hR0'.gfree⟩
  have hsP : ∀ n, ({ R with X := XI.at n } : RL).sP = R.sP := fun n => RL.sP_withX hRw hent (XI.at n)
  have hsP' : ∀ n, ({ R with s0 := t0, G := G', X := XI'.at n } : RL).sP = R''.sP :=
    fun n => RL.sP_withX hRw'' hent' (XI'.at n)
  have hPX : R0.sP = R.sP := hsP 0
  have hPX' : R0'.sP = R''.sP := hsP' 0
  have hJ := RL.realizesJCPT (R := R) (t0 := t0) (G' := G') (XI := XI) (XI' := XI') hRn hRn' hsP hsP'
    (P := fun n u => OnCall R0.step R.fa R.base R.s0 n u)
    (P' := fun n u => OnCall R0'.step R.fa R.base t0 n u) OkG OkG' hC hT hTls hC' hT' hTls' hcov
    K LB OkS OkS' hG hG' Lk hLpc hstart hstep hend
  have hsc : R0.SameCode R0' := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hW : R0'.initW = R0.initW := RL.initW_congr hsc
  have hq1 : QW R s₁ R0.initW.1 R0.initW.2.1 R0.initW.2.2
      (MConf.init R.rf (locVal R.fr s₁) w₀) := QW.ofWithX (R := R) (X := XI.at 0) hPX hq0
  have hq1' : QW R'' s₁' R0.initW.1 R0.initW.2.1 R0.initW.2.2
      (MConf.init R.rf (locVal R.fr s₁') w₀') := by
    have := QW.ofWithX (R := R'') (X := XI'.at 0) hPX' hq0'
    rw [hW] at this
    exact this
  obtain ⟨N, b, k, a, its, m, w, a', its', m', w', hjN, hcN, hcN', hrN, hrN', htN⟩ :=
    forward2C_opB (sem := fun n => csemVGS R.gv R.F R.ctx (XI.at n) OkG)
      (sem' := fun n => csemVGS R.gv R''.F R.ctx (XI'.at n) OkG')
      (semB := fun n => csemVGS R.gv R.F R.ctx (XB.at n) OkB)
      (s0 := s₁) (s0' := s₁') hJ (onCall_of_run hP0) (onCall_of_run hP0') hSim hSim' hSimB
      (hK := hK) hp hy hpix hinit hinit' hpi0 ⟨rfl, rfl⟩ rfl rfl
      ⟨⟨R0.initW, .inl ⟨hq1, hA0⟩, .inl ⟨hq1', hA0'⟩⟩, ⟨rfl, rfl⟩,
        hK _ _ _ _ hinit hinit' hpi0, hpro⟩
  obtain ⟨vs, rfl⟩ := hSim.run hrN
  obtain ⟨vs', rfl⟩ := hSim'.run hrN'
  obtain ⟨hb1, hk1, hw1⟩ := hSim.at_op hrN
  obtain ⟨hb2, hk2, hw2⟩ := hSim'.at_op hrN'
  obtain ⟨b1, k1, ρ1, wx1⟩ := vs
  obtain ⟨b2, k2, ρ2, wx2⟩ := vs'
  dsimp only at hb1 hk1 hw1 hb2 hk2 hw2
  rw [hb1, hk1, hw1, hb2, hk2, hw2]
  have hs : ∀ j, iterN R0.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + j) R.s0 =
      iterN R0.step j s₁ := fun j => iterN_add ..
  have hs' : ∀ j, iterN R0'.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + j) t0 =
      iterN R0'.step j s₁' := fun j => iterN_add ..
  refine ⟨N, b, k, a, its, m, w.1, ρ1, a', its', m', w'.1, ρ2, w.2, w'.2,
    fun i hi => ⟨ht0 i hi, ht0' i hi⟩, fun i hi => ?_, ?_, ?_, ?_, rfl, rfl⟩
  · rw [hs, hs']; exact htN i hi
  · rw [hs N, hs' N]; exact hjN
  · rw [countIn_add, hP0, Nat.zero_add]; exact hcN
  · rw [countIn_add, hP0', Nat.zero_add]; exact hcN'

set_option maxHeartbeats 2000000 in
/-- **`RL.twoRunPRT` up to a pair state** (`RL.twoRunCTN` from the two `ActEntryPR` entries). -/
theorem RL.twoRunPRTN {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {XI XI' : ExtSemI} {H : ArmHooks} {K : Nat} {F F' G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 w₀ w₀' : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he' : ActEntryPR vcp rf af fa fb K F' G' XI' H base ra' Kp' cc' P' Rr' t0 w₀')
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc) (ρ₀ : Nat → CV)
    (OkG OkG' : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (KJ : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Prop)
    (LB : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Arm.ArmState → Arm.ArmState → Prop)
    (OkS OkS' : MConf CV Arm.ArmState → MConf CV Arm.ArmState →
      Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hG : ∀ n c c' d, KJ c c' →
      MStep R.vc (({ R with X := XI.at n } : RL).semGS OkG) ckeep R.rf c d →
      MStep R.vc (({ R with X := XI.at n } : RL).semGS (OkS c c')) ckeep R.rf c d)
    (hG' : ∀ n c c' d, KJ c c' →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semGS OkG') ckeep R.rf c' d →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semGS (OkS' c c')) ckeep R.rf
        c' d)
    (Lk : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ c c' i u u', Lk c c' i u u' → Arm.r .PC u = Arm.r .PC u')
    (hstart : ∀ c c' s s', KJ c c' → LB c c' s s' → Lk c c' 0 s s')
    (hstep : ∀ n n' c c' i u u', KJ c c' →
      ({ R with X := XI.at n } : RL).InSeg (OkS c c') c i u →
      ({ R with s0 := t0, G := G', X := XI'.at n' } : RL).InSeg (OkS' c c') c' i u' →
      (({ R with X := XI.at n } : RL).GoodX u ∧
        ({ R with X := XI.at n } : RL).WReadsIn (OkS c c') u) →
      (({ R with s0 := t0, G := G', X := XI'.at n' } : RL).GoodX u' ∧
        ({ R with s0 := t0, G := G', X := XI'.at n' } : RL).WReadsIn (OkS' c c') u') →
      Lk c c' i u u' → Lk c c' (i + 1) (({ R with X := XI.at 0 } : RL).step u)
        (({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step u'))
    (hend : ∀ c c' d d' i u u', KJ c c' → KJ d d' → MConf.ShapeEq d d' →
      (∃ W : Nat × PState × List Line, QWA R u W.1 W.2.1 W.2.2 d ∧
        QWA ({ R with s0 := t0, G := G' } : RL) u' W.1 W.2.1 W.2.2 d') →
      Lk c c' i u u' → LB d d' u u')
    {PI : VConf CV (Arm.ArmState × Nat) → VConf CV (Arm.ArmState × Nat) → Prop}
    (hK : ∀ (ckc : CheckCtx) (ins : Array (Option AState)) (a0 : AState),
      CheckedAt R.vc R.rf ckc ins a0 → ∀ e e' x x',
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0) (.reg r)) e x →
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
        RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0) (.reg r)) e' x' →
      PI x x' → KJ (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0))
    {x x' y : VConf CV (Arm.ArmState × Nat)}
    (hp : Star (PStep R.vc (csemVIGS R.gv R.F R.ctx XI OkG)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI)
      (VConf.init ρ₀ (w₀, 0), VConf.init ρ₀ (w₀', 0)) (x, x'))
    (hpi0 : PI (VConf.init ρ₀ (w₀, 0)) (VConf.init ρ₀ (w₀', 0))) (hpix : PI x x')
    {XB : ExtSemI} {OkB : Arm.ArmState → (BitVec 64 → Prop) → Prop}
    (hy : VStep R.vc (csemVIGS R.gv R.F R.ctx XB OkB) x y) :
    ∃ N b k a its m w ρ a' its' m' w' ρ' nc nc',
      (∀ i < (prologueSteps R.af.saves R.af.frameSize R.af.isCaller),
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) KJ LB
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) R.s0)
        (.run ⟨b, .op k a :: its, m, w⟩)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) t0) (.run ⟨b, .op k a' :: its', m', w'⟩) ∧
      countIn (RL.CallSt R) ({ R with X := XI.at 0 } : RL).step R.s0
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) = nc ∧
      countIn (RL.CallSt R) ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step t0
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) = nc' ∧
      x = .run ⟨b, k, ρ, (w, nc)⟩ ∧ x' = .run ⟨b, k, ρ', (w', nc')⟩ := by
  subst hR
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hemit
  subst hk
  obtain ⟨ckc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  have hF := he.hF
  have hF' := he'.hF
  subst hF hF'
  exact RL.twoRunCTN (R := actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)) (t0 := t0)
    (G' := G') (XI := XI) (XI' := XI')
    (fun _ => ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hpsF⟩,
      he.abi.program, he.gfree⟩)
    (fun _ => ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he'.abi.fits; omega, he'.stack, ⟨body, hpsF⟩,
      he'.abi.program, he'.gfree⟩)
    hat ρ₀ (fun _ => Inv_mono hle Inv_entryState) he.abi he'.abi he.body he'.body OkG OkG'
    (fun n => (he.calls n).mono fun _ h => ⟨onCallPR_of he.proph he.regp h.1, h.2⟩)
    (fun h n => (he.tries h n).mono fun _ h => ⟨onCallPR_of he.proph he.regp h.1, h.2⟩) he.tls
    (fun n => (he'.calls n).mono fun _ h => ⟨onCallPR_of he'.proph he'.regp h.1, h.2⟩)
    (fun h n => (he'.tries h n).mono fun _ h => ⟨onCallPR_of he'.proph he'.regp h.1, h.2⟩) he'.tls
    hcov KJ LB OkS OkS' hG hG' Lk hLpc hstart hstep hend (hK ckc ins a0 hat) hpro hp hpi0 hpix hy

end Backend.Proof
