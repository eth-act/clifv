import FV.E2E.RegLevelTwoRunW
import FV.E2E.BackendWorldI
import FV.E2E.RegLevelCorrectCYS

/-!
# Two activations in lock-step on the reads-only guard (SEM1 #537, #699)

`RL.jointSeg`, `RL.realizesJCP`, `RL.twoRunC`, `RL.twoRunPR` on the guarded semantics `RL.semGS`
/ `csemVIGS` (`RegLevelCorrectCYS.lean`: the world-read guard constrains reads only, so a store
into a byte of the guard set is admitted). Same proofs, on `realizes_allCWS`.

* `RL.jointSegS`, `RL.realizesJCPS`, **`RL.twoRunCS`**, **`RL.twoRunPRS`**.
-/

namespace Backend.Proof

open Backend E2E

/-- **`RL.jointSeg` on the reads-only guard.** -/
theorem RL.jointSegS {R R' : RL} (hR : R.Wf) (hR' : R'.Wf) (hsc : R.SameCode R')
    {P P' : Arm.ArmState → Prop} (Ok Ok' : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hC' : CalleeOkGP P' R'.F R'.K R'.G R'.s0 (CallAt R'.fa R'.base) R'.X R'.H R'.vc.CallSite R'.gv)
    (hT' : R'.vc.hasTryCall = true →
      CalleeTryOkGP P' R'.F R'.K R'.G R'.s0 (CallAt R'.fa R'.base) R'.X R'.H R'.vc.TrySite R'.gv)
    (hTls' : R'.vc.hasTls = true → TlsOk R'.F R'.K R'.X R'.H)
    (hcov : FormsCovered R.ctx R.vc) (hcov' : FormsCovered R'.ctx R'.vc)
    {s s' : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' e e' : MConf CV Arm.ArmState} (hq : QWA R s j ps1 T c) (hq' : QWA R' s' j ps1 T c')
    (hP : P s) (hP' : P' s') (hc : MConf.ShapeEq c c')
    (he : MStep R.vc (R.semGS Ok) ckeep R.rf c e)
    (he' : MStep R'.vc (R'.semGS Ok') ckeep R'.rf c' e')
    (hsh : ∀ d d', MStep R.vc (R.semGS Ok) ckeep R.rf c d →
      MStep R'.vc (R'.semGS Ok') ckeep R'.rf c' d' → MConf.ShapeEq d d')
    (Lk : Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ i u u', Lk i u u' → Arm.r .PC u = Arm.r .PC u') (h0 : Lk 0 s s')
    (hstep : ∀ i u u', (R.GoodX u ∧ R.WReadsIn Ok u) → (R'.GoodX u' ∧ R'.WReadsIn Ok' u') →
      Lk i u u' → Lk (i + 1) (R.step u) (R'.step u')) :
    ∃ n d d', MStep R.vc (R.semGS Ok) ckeep R.rf c d ∧
      MStep R'.vc (R'.semGS Ok') ckeep R'.rf c' d' ∧
      MConf.ShapeEq d d' ∧
      QWA R (iterN R.step n s) (R.nextW j ps1 T c d).1 (R.nextW j ps1 T c d).2.1
        (R.nextW j ps1 T c d).2.2 d ∧
      QWA R' (iterN R'.step n s') (R.nextW j ps1 T c d).1 (R.nextW j ps1 T c d).2.1
        (R.nextW j ps1 T c d).2.2 d' ∧
      (∀ i < n, (R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        (R'.GoodX (iterN R'.step i s') ∧ R'.WReadsIn Ok' (iterN R'.step i s'))) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧
      countIn R'.CallSt R'.step s' n = opCalls R'.vc c' ∧
      R.SegLenA j ps1 T c d s n ∧ R'.SegLenA j ps1 T c' d' s' n ∧
      ∀ i ≤ n, Lk i (iterN R.step i s) (iterN R'.step i s') := by
  obtain ⟨n, d, hm, -, hqd, ht, hcnt, hs⟩ := realizes_allCWS hR Ok hC hT hTls hcov hq hP he
  obtain ⟨n', d', hm', -, hqd', ht', hcnt', hs'⟩ :=
    realizes_allCWS hR' Ok' hC' hT' hTls' hcov' hq' hP' he'
  have hd := hsh d d' hm hm'
  obtain ⟨rfl, hL⟩ := RL.seg_lock hsc hc hd hs hs' Lk hLpc h0 fun i hi hi' hl =>
    hstep i _ _ (ht i hi) (ht' i hi') hl
  have hW := RL.nextW_shape hsc j ps1 T hc hd
  rw [hW] at hqd'
  exact ⟨n, d, d', hm, hm', hd, hqd, hqd', fun i hi => ⟨ht i hi, ht' i hi⟩, hcnt, hcnt',
    hs, hs', hL⟩

set_option maxHeartbeats 1000000 in
/-- **`RL.realizesJCP` on the reads-only guard.** -/
theorem RL.realizesJCPS {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
    (hRn : ∀ n, ({ R with X := XI.at n } : RL).Wf)
    (hRn' : ∀ n, ({ R with s0 := t0, G := G', X := XI'.at n } : RL).Wf)
    (hsP : ∀ n, ({ R with X := XI.at n } : RL).sP = R.sP)
    (hsP' : ∀ n, ({ R with s0 := t0, G := G', X := XI'.at n } : RL).sP =
      ({ R with s0 := t0, G := G' } : RL).sP)
    {P P' : Nat → Arm.ArmState → Prop}
    (OkG OkG' : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : ∀ n, CalleeOkGP (fun u => P n u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base)
      (XI.at n) R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u => P n u ∧ spOf u = R.spB) R.F R.K
      R.G R.s0 (CallAt R.fa R.base) (XI.at n) R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → ∀ n, TlsOk R.F R.K (XI.at n) R.H)
    (hC' : ∀ n, CalleeOkGP (fun u => P' n u ∧ spOf u = ({ R with s0 := t0, G := G' } : RL).spB)
      ({ R with s0 := t0, G := G' } : RL).F R.K G' t0 (CallAt R.fa R.base) (XI'.at n) R.H
      R.vc.CallSite R.gv)
    (hT' : R.vc.hasTryCall = true → ∀ n, CalleeTryOkGP
      (fun u => P' n u ∧ spOf u = ({ R with s0 := t0, G := G' } : RL).spB)
      ({ R with s0 := t0, G := G' } : RL).F R.K G' t0 (CallAt R.fa R.base) (XI'.at n) R.H
      R.vc.TrySite R.gv)
    (hTls' : R.vc.hasTls = true → ∀ n, TlsOk ({ R with s0 := t0, G := G' } : RL).F R.K (XI'.at n) R.H)
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
      (({ R with X := XI.at n } : RL).GoodX u ∧
        ({ R with X := XI.at n } : RL).WReadsIn (OkS c c') u) →
      (({ R with s0 := t0, G := G', X := XI'.at n' } : RL).GoodX u' ∧
        ({ R with s0 := t0, G := G', X := XI'.at n' } : RL).WReadsIn (OkS' c c') u') →
      Lk c c' i u u' → Lk c c' (i + 1) (({ R with X := XI.at 0 } : RL).step u)
        (({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step u'))
    (hend : ∀ c c' d d' i u u', K c c' → K d d' → MConf.ShapeEq d d' →
      (∃ W : Nat × PState × List Line, QWA R u W.1 W.2.1 W.2.2 d ∧
        QWA ({ R with s0 := t0, G := G' } : RL) u' W.1 W.2.1 W.2.2 d') →
      Lk c c' i u u' → LB d d' u u') :
    ∀ n n', RealizesJCP R.vc R.rf (({ R with X := XI.at n } : RL).semGS OkG)
      (({ R with s0 := t0, G := G', X := XI'.at n' } : RL).semGS OkG') ckeep
      ({ R with X := XI.at 0 } : RL).step ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step K
      (JR R ({ R with s0 := t0, G := G' } : RL) K LB)
      (fun u u' => ∃ c c' i, Lk c c' i u u') (RL.CallSt R) (RL.CallSt R) (P n) (P' n') := by
  intro n n' s c s' c' d d' ⟨⟨W, hq, hq'⟩, hsh, hK, hLB⟩ hP hP' hd hd' hshK
  let Rn : RL := { R with X := XI.at n }
  let Rn' : RL := { R with s0 := t0, G := G', X := XI'.at n' }
  have hsc : Rn.SameCode Rn' := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hPn : Rn.sP = R.sP := hsP n
  have hPn' : Rn'.sP = ({ R with s0 := t0, G := G' } : RL).sP := hsP' n'
  have hqn : QWA Rn s W.1 W.2.1 W.2.2 c := QWA.withX (R := R) hPn hq
  have hqn' : QWA Rn' s' W.1 W.2.1 W.2.2 c' :=
    QWA.withX (R := ({ R with s0 := t0, G := G' } : RL)) hPn' hq'
  have lift : ∀ e, MStep R.vc (Rn.semGS (OkS c c')) ckeep R.rf c e →
      MStep R.vc (Rn.semGS OkG) ckeep R.rf c e := fun e h => MStep.guardLift h hd RL.semGS_agree
  have lift' : ∀ e, MStep R.vc (Rn'.semGS (OkS' c c')) ckeep R.rf c' e →
      MStep R.vc (Rn'.semGS OkG') ckeep R.rf c' e := fun e h => MStep.guardLift h hd' RL.semGS_agree
  obtain ⟨m, e, e', he, he', hse, hqe, hqe', ht, hcnt, hcnt', -, -, hL⟩ :=
    RL.jointSegS (R := Rn) (R' := Rn') (hRn n) (hRn' n') hsc (OkS c c') (OkS' c c')
      (hC n) (fun h => hT h n) (fun h => hTls h n) (hC' n') (fun h => hT' h n')
      (fun h => hTls' h n') hcov hcov hqn hqn' ⟨hP, QWA.sp_of_mstep (R := Rn) hqn hd⟩
      ⟨hP', QWA.sp_of_mstep (R := Rn') hqn' hd'⟩ hsh (hG n c c' d hK hd) (hG' n' c c' d' hK hd')
      (fun a b ha hb => (hshK a b (lift a ha) (lift' b hb)).1) (Lk c c') (hLpc c c')
      (hstart c c' s s' hK hLB) fun i u u' h1 h2 hl => hstep n n' c c' i u u' hK h1 h2 hl
  have hE := lift e he
  have hE' := lift' e' he'
  obtain ⟨-, hKe⟩ := hshK e e' hE hE'
  have hq1 := QWA.ofWithX (R := R) hPn hqe
  have hq1' := QWA.ofWithX (R := ({ R with s0 := t0, G := G' } : RL)) hPn' hqe'
  exact ⟨m, e, e', hE, hE', ⟨⟨_, hq1, hq1'⟩, hse, hKe,
    hend c c' e e' m _ _ hK hKe hse ⟨_, hq1, hq1'⟩ (hL m (Nat.le_refl _))⟩,
    fun i hi => ⟨c, c', i, hL i (Nat.le_of_lt hi)⟩, hcnt, hcnt'⟩

set_option maxHeartbeats 2000000 in
/-- **`RL.twoRunC` on the reads-only guard** (same proof, on `RL.realizesJCPS`). -/
theorem RL.twoRunCS {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
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
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0) (.reg r)) e x →
      Match cc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
        RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0) (.reg r)) e' x' →
      PI x x' → K (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0))
    {x x' : VConf CV (Arm.ArmState × Nat)} {vals vals' : List CV} {wr wr' : Arm.ArmState × Nat}
    (hp : Star (PStep R.vc (csemVIGS R.gv R.F R.ctx XI OkG)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI)
      (VConf.init ρ₀ (w₀, 0), VConf.init ρ₀ (w₀', 0)) (x, x'))
    (hpi0 : PI (VConf.init ρ₀ (w₀, 0)) (VConf.init ρ₀ (w₀', 0))) (hpix : PI x x')
    (hy : PStep R.vc (csemVIGS R.gv R.F R.ctx XI OkG)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI (x, x')
      (.ret vals wr, .ret vals' wr')) :
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
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' := by
  let R0 : RL := { R with X := XI.at 0 }
  let R0' : RL := { R with s0 := t0, G := G', X := XI'.at 0 }
  let R'' : RL := { R with s0 := t0, G := G' }
  have hR0 : R0.Wf := hRn 0
  have hR0' : R0'.Wf := hRn' 0
  obtain ⟨n0, hn0, ht0, hq0, hA0, -⟩ := q_initNA (R := R0) (Y := fun _ => True) hR0 hent hbe
  obtain ⟨n0', hn0', ht0', hq0', hA0', -⟩ :=
    q_initNA (R := R0') (Y := fun _ => True) hR0' hent' hbe'
  have e0 : n0 = (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length := hn0
  have e0' : n0' = (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length := hn0'
  subst e0 e0'
  let s₁ := iterN R0.step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0
  let s₁' := iterN R0'.step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0
  obtain ⟨hSim, hinit⟩ := isSimulationS_match (sem := csemVIGS R.gv R.F R.ctx XI OkG)
    (keep := ckeep) hcheck (locVal R.fr s₁) ρ₀ (w₀, 0) (hsel _)
  obtain ⟨hSim', hinit'⟩ := isSimulationS_match (sem := csemVIGS R.gv R''.F R.ctx XI' OkG')
    (keep := ckeep) hcheck (locVal R.fr s₁') ρ₀ (w₀', 0) (hsel _)
  have hP0 : countIn (RL.CallSt R) R0.step R.s0 (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length = 0 :=
    countIn_zero_of fun i hi => (ht0 i hi).1.2
  have hP0' : countIn (RL.CallSt R) R0'.step t0 (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length = 0 :=
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
  have hJ := RL.realizesJCPS (R := R) (t0 := t0) (G' := G') (XI := XI) (XI' := XI') hRn hRn' hsP hsP'
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
  obtain ⟨N, b, k, a, its, m, w, a', its', m', w', hjN, -, -, hrN, hrN', htN⟩ :=
    forward2C_op (sem := fun n => csemVGS R.gv R.F R.ctx (XI.at n) OkG)
      (sem' := fun n => csemVGS R.gv R''.F R.ctx (XI'.at n) OkG')
      (s0 := s₁) (s0' := s₁') hJ (onCall_of_run hP0) (onCall_of_run hP0') hSim hSim'
      (hK := hK) hp hy hpix hinit hinit' hpi0 ⟨rfl, rfl⟩ rfl rfl
      ⟨⟨R0.initW, .inl ⟨hq1, hA0⟩, .inl ⟨hq1', hA0'⟩⟩, ⟨rfl, rfl⟩,
        hK _ _ _ _ hinit hinit' hpi0, hpro⟩
  obtain ⟨hx, hx', -, -⟩ := hy
  obtain ⟨b1, k1, ρ1, wx1, vb, rs, rfl, hvb, hi⟩ := VStep.rets_of_ret hx
  obtain ⟨b2, k2, ρ2, wx2, vb2, rs2, rfl, hvb2, hi2⟩ := VStep.rets_of_ret hx'
  obtain ⟨hb1, hk1, -⟩ := hSim.at_op hrN
  obtain ⟨hb2, hk2, -⟩ := hSim'.at_op hrN'
  dsimp only at hb1 hk1 hb2 hk2
  subst hb1 hk1 hb2 hk2
  obtain ⟨⟨W, hqA, hqB⟩, hJr⟩ := hjN
  have hqA0 : QA R0 _ _ := (RL.QA_withX R (XI.at 0) hPX _ _).2 hqA.qa
  have hqB0 : QA R0' _ _ := (RL.QA_withX R'' (XI'.at 0) hPX' _ _).2 hqB.qa
  obtain ⟨n3, hn3, ht3, hpc3, -⟩ := ret_machineNA (R := R0) (Y := fun _ => True) hR0 hent hqA0 hvb hi
  obtain ⟨n3', hn3', ht3', hpc3', -⟩ :=
    ret_machineNA (R := R0') (Y := fun _ => True) hR0' hent' hqB0 hvb2 hi2
  have e3 : n3 = R.retLen := hn3
  have e3' : n3' = R.retLen := hn3'
  subst e3 e3'
  have hs : ∀ j, iterN R0.step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + j) R.s0 =
      iterN R0.step j s₁ := fun j => iterN_add ..
  have hs' : ∀ j, iterN R0'.step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + j) t0 =
      iterN R0'.step j s₁' := fun j => iterN_add ..
  have hJ2 := (⟨⟨W, hqA, hqB⟩, hJr⟩ : JR R R'' K LB _ _ _ _)
  rw [← hs N, ← hs' N] at hJ2
  refine ⟨N, _, _, fun i hi => ⟨ht0 i hi, ht0' i hi⟩, fun i hi => ?_, hJ2, fun i hi => ?_, ?_, ?_⟩
  · rw [hs, hs']; exact htN i hi
  · rw [Nat.add_assoc, hs, hs', iterN_add, iterN_add]
    exact ⟨ht3 i hi, ht3' i hi⟩
  · rw [Nat.add_assoc, hs, iterN_add]; exact hpc3
  · rw [Nat.add_assoc, hs', iterN_add]; exact hpc3'

set_option maxHeartbeats 2000000 in
/-- **`RL.twoRunPR` on the reads-only guard** (same proof, on `RL.twoRunCS`). -/
theorem RL.twoRunPRS {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
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
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0) (.reg r)) e x →
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
        RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0) (.reg r)) e' x' →
      PI x x' → KJ (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0))
    {x x' : VConf CV (Arm.ArmState × Nat)} {vals vals' : List CV} {wr wr' : Arm.ArmState × Nat}
    (hp : Star (PStep R.vc (csemVIGS R.gv R.F R.ctx XI OkG)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI)
      (VConf.init ρ₀ (w₀, 0), VConf.init ρ₀ (w₀', 0)) (x, x'))
    (hpi0 : PI (VConf.init ρ₀ (w₀, 0)) (VConf.init ρ₀ (w₀', 0))) (hpix : PI x x')
    (hy : PStep R.vc (csemVIGS R.gv R.F R.ctx XI OkG)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI (x, x')
      (.ret vals wr, .ret vals' wr')) :
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
      JR R ({ R with s0 := t0, G := G' } : RL) KJ LB
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
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' := by
  subst hR
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hemit
  subst hk
  obtain ⟨ckc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  have hF := he.hF
  have hF' := he'.hF
  subst hF hF'
  exact RL.twoRunCS (R := actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)) (t0 := t0)
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
