import FV.E2E.RegLevelLock2
import FV.E2E.RegLevelJointC
import FV.E2E.RegLevelCorrectPRSW

/-!
# Two activations of one compiled function realised jointly (SEM1 #537, item (3))

`RL.jointSeg` at every pair of call numbers, as a `RealizesJCP`: the activation `R` (external
semantics `XI.at n` at call number `n`) and `R'` = `R` entered at `t0` with kept set `G'`
(external semantics `XI'.at n'`), at one witness, shape-equal configurations, with a boundary
lock `LB` and the pair facts `K`. Each segment runs on the activation's guarded semantics at a
guard chosen per segment (`OkS c c'`, from the pair facts at the segment's configurations: `hG`);
inside it the segment lock `Lk c c'` holds at every index (`hstart`, `hstep`); at its end the
boundary lock is re-established from the next configurations' pair facts (`hend`).

* `JR`: the joint invariant;
* **`RL.realizesJCP`**.
-/

namespace Backend.Proof

open Backend E2E

/-- **The joint invariant of two activations** at one witness: `QWA` of both at it (`QW ∧ AInv`
or a return tail), shape-equal configurations, the pair facts `K` and the boundary lock `LB`. -/
def JR (R R' : RL) (K : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Prop)
    (LB : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Arm.ArmState → Arm.ArmState → Prop)
    (s : Arm.ArmState) (c : MConf CV Arm.ArmState) (s' : Arm.ArmState)
    (c' : MConf CV Arm.ArmState) : Prop :=
  (∃ W : Nat × PState × List Line, QWA R s W.1 W.2.1 W.2.2 c ∧ QWA R' s' W.1 W.2.1 W.2.2 c') ∧
    MConf.ShapeEq c c' ∧ K c c' ∧ LB c c' s s'

/-- A `QW` state from which an `MStep` is taken is at the body `sp`. -/
theorem QW.sp_of_mstep {R : RL} {sem : ISem CV Arm.ArmState} {u : Arm.ArmState} {j : Nat}
    {ps1 : PState} {T : List Line} {e e' : MConf CV Arm.ArmState} (h : QW R u j ps1 T e)
    (hm : MStep R.vc sem ckeep R.rf e e') : spOf u = R.spB := by
  cases e with
  | run st => obtain ⟨b, its, m, w⟩ := st; exact (q_stRel h.q).sp
  | ret => cases hm
  | halt => cases hm

/-- A `QWA` state from which an `MStep` is taken is at the body `sp`. -/
theorem QWA.sp_of_mstep {R : RL} {sem : ISem CV Arm.ArmState} {u : Arm.ArmState} {j : Nat}
    {ps1 : PState} {T : List Line} {e e' : MConf CV Arm.ArmState} (h : QWA R u j ps1 T e)
    (hm : MStep R.vc sem ckeep R.rf e e') : spOf u = R.spB := by
  cases e with
  | run st =>
    obtain ⟨b, its, m, w⟩ := st
    obtain ⟨mt, hq⟩ := qa_q h.qa
    exact (q_stRel hq).sp
  | ret => cases hm
  | halt => cases hm

/-- Two guarded semantics of one activation agree where both are defined. -/
theorem RL.semG_agree {R : RL} {Ok Ok' : Arm.ArmState → (BitVec 64 → Prop) → Prop} :
    ∀ i us w r r', R.semG Ok' i us w = some r → R.semG Ok i us w = some r' →
      R.semG Ok' i us w = some r' := by
  intro i us w r r' h h'
  have e : r = r' := by
    have a := (RL.semG_inv h).2
    have b := (RL.semG_inv h').2
    rw [a] at b
    exact Option.some.inj b
  rw [h, e]

set_option maxHeartbeats 1000000 in
/-- **Two activations realise their steps jointly at every pair of call numbers** (module doc). -/
theorem RL.realizesJCP {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
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
      Lk c c' i u u' → LB d d' u u') :
    ∀ n n', RealizesJCP R.vc R.rf (({ R with X := XI.at n } : RL).semG OkG)
      (({ R with s0 := t0, G := G', X := XI'.at n' } : RL).semG OkG') ckeep
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
  have lift : ∀ e, MStep R.vc (Rn.semG (OkS c c')) ckeep R.rf c e →
      MStep R.vc (Rn.semG OkG) ckeep R.rf c e := fun e h => MStep.guardLift h hd RL.semG_agree
  have lift' : ∀ e, MStep R.vc (Rn'.semG (OkS' c c')) ckeep R.rf c' e →
      MStep R.vc (Rn'.semG OkG') ckeep R.rf c' e := fun e h => MStep.guardLift h hd' RL.semG_agree
  obtain ⟨m, e, e', he, he', hse, hqe, hqe', ht, hcnt, hcnt', -, -, hL⟩ :=
    RL.jointSeg (R := Rn) (R' := Rn') (hRn n) (hRn' n') hsc (OkS c c') (OkS' c c')
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

end Backend.Proof
