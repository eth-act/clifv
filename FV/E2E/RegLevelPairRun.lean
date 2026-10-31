import FV.E2E.RegLevelTwoRunW

/-!
# Pair steps from one run on paired worlds (SEM1 #537, item (3))

A VCode run of a semantics `semP` on paired worlds that projects (`ISem.ProjW`) along `π₁`, `π₂`
to `sem₁`, `sem₂` is a run of pair steps (`PStep`) of the two projections: one configuration of
`semP` maps to two configurations at the same place with the same vreg file, so the pair
invariant is `PairOf π₁ π₂` (both are projections of one paired configuration).

* `PairOf`, `VConf.sameAt_mapW`, **`pstep_of_proj`**, **`pstar_of_proj`**;
* `pairFst`, `pairSnd` (counted paired worlds `((w, w'), n)`, one counter), `pairFst_proj`,
  `pairSnd_proj` (the counted `pairSem` family projects to each world's counted semantics);
* **`RL.twoRunC_pair`**: `RL.twoRunC` from one returning paired run.
-/

namespace Backend.Proof

open Backend E2E

section
variable {V W W₁ W₂ : Type} {vc : VCode}

/-- **Two configurations are the projections of one paired configuration.** -/
def PairOf (π₁ : W → W₁) (π₂ : W → W₂) (x : VConf V W₁) (x' : VConf V W₂) : Prop :=
  ∃ c : VConf V W, x = c.mapW π₁ ∧ x' = c.mapW π₂

theorem VConf.sameAt_mapW (π₁ : W → W₁) (π₂ : W → W₁) (c : VConf V W) :
    VConf.SameAt (c.mapW π₁) (c.mapW π₂) := by
  cases c with
  | run s => exact ⟨rfl, rfl⟩
  | ret => trivial
  | halt => trivial

/-- **One paired step is a pair step of the projections.** -/
theorem pstep_of_proj {semP : ISem V W} {sem₁ sem₂ : ISem V W₁} {π₁ π₂ : W → W₁}
    (h₁ : ISem.ProjW π₁ semP sem₁) (h₂ : ISem.ProjW π₂ semP sem₂) {c c' : VConf V W}
    (h : VStep vc semP c c') :
    PStep vc sem₁ sem₂ (PairOf π₁ π₂) (c.mapW π₁, c.mapW π₂) (c'.mapW π₁, c'.mapW π₂) :=
  ⟨VStep_mapW h₁ h, VStep_mapW h₂ h, VConf.sameAt_mapW π₁ π₂ c', c', rfl, rfl⟩

/-- **A paired run is a run of pair steps of the projections.** -/
theorem pstar_of_proj {semP : ISem V W} {sem₁ sem₂ : ISem V W₁} {π₁ π₂ : W → W₁}
    (h₁ : ISem.ProjW π₁ semP sem₁) (h₂ : ISem.ProjW π₂ semP sem₂) {c c' : VConf V W}
    (h : Star (VStep vc semP) c c') :
    Star (PStep vc sem₁ sem₂ (PairOf π₁ π₂)) (c.mapW π₁, c.mapW π₂) (c'.mapW π₁, c'.mapW π₂) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (pstep_of_proj h₁ h₂ hs) ih

end

/-! ## Counted paired worlds -/

/-- The first world of a counted pair, with the counter. -/
def pairFst {W : Type} (p : (W × W) × Nat) : W × Nat := (p.1.1, p.2)

/-- The second world of a counted pair, with the counter. -/
def pairSnd {W : Type} (p : (W × W) × Nat) : W × Nat := (p.1.2, p.2)

/-- **The counted paired semantics projects to the first world's counted semantics.** -/
theorem pairFst_proj (semF : Nat → Sem) :
    ISem.ProjW pairFst (ISem.counted fun n => pairSem (semF n)) (ISem.counted semF) := by
  intro i uses w outs w' ctl h
  obtain ⟨hs, hn⟩ := ISem.counted_some h
  obtain ⟨h1, -⟩ := pairSem_inv hs
  simp only [ISem.counted, pairFst, h1, Option.map_some, hn]

/-- **The counted paired semantics projects to the second world's counted semantics.** -/
theorem pairSnd_proj (semF : Nat → Sem) :
    ISem.ProjW pairSnd (ISem.counted fun n => pairSem (semF n)) (ISem.counted semF) := by
  intro i uses w outs w' ctl h
  obtain ⟨hs, hn⟩ := ISem.counted_some h
  obtain ⟨-, h2⟩ := pairSem_inv hs
  simp only [ISem.counted, pairSnd, h2, Option.map_some, hn]

set_option maxHeartbeats 2000000 in
/-- **`RL.twoRunC` from one returning paired run** (one counter for both worlds): a run of a
semantics `semP` on counted paired worlds projecting to the two activations' counted guarded
semantics, from the initial configuration with the two body-entry worlds to a step that returns.
The pair invariant is `PairOf pairFst pairSnd`; `hK` derives the pair facts from it. -/
theorem RL.twoRunC_pair {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
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
    (hG : ∀ n c c' d, K c c' → MStep R.vc (({ R with X := XI.at n } : RL).semG OkG) ckeep R.rf c d →
      MStep R.vc (({ R with X := XI.at n } : RL).semG (OkS c c')) ckeep R.rf c d)
    (hG' : ∀ n c c' d, K c c' →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semG OkG') ckeep R.rf c' d →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semG (OkS' c c')) ckeep R.rf
        c' d)
    (Lk : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ c c' i u u', Lk c c' i u u' → Arm.r .PC u = Arm.r .PC u')
    (hstart : ∀ c c' s s', K c c' → LB c c' s s' → Lk c c' 0 s s')
    (hstep : ∀ n n' c c' i u u', K c c' →
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
    (hK : ∀ e e' x x',
      Match cc ins ckeep (fun r => locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0) (.reg r)) e x →
      Match cc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
        RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0) (.reg r)) e' x' →
      PairOf pairFst pairSnd x x' → K (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0))
    {semP : ISem CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (hp₁ : ISem.ProjW pairFst semP (csemVIG R.gv R.F R.ctx XI OkG))
    (hp₂ : ISem.ProjW pairSnd semP (csemVIG R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG'))
    {x : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)} {vals : List CV}
    {wr : (Arm.ArmState × Arm.ArmState) × Nat}
    (hrun : Star (VStep R.vc semP) (VConf.init ρ₀ ((w₀, w₀'), 0)) x)
    (hlast : VStep R.vc semP x (.ret vals wr)) :
    ∃ N e e',
      (∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) K LB
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) t0) e' ∧
      (∀ i < R.retLen,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' :=
  RL.twoRunC hRn hRn' hcheck ρ₀ hsel hent hent' hbe hbe' OkG OkG' hC hT hTls hC' hT' hTls' hcov
    K LB OkS OkS' hG hG' Lk hLpc hstart hstep hend hK hpro (pstar_of_proj hp₁ hp₂ hrun)
    ⟨VConf.init ρ₀ ((w₀, w₀'), 0), rfl, rfl⟩ ⟨x, rfl, rfl⟩ (pstep_of_proj hp₁ hp₂ hlast)

end Backend.Proof
