import FV.E2E.RegLevelTwoRunT
import FV.E2E.RegLevelCallStart

/-!
# Two activations in lock-step, the lock step told the first run's segment start (SEM1 #537,
#713, #729)

`RL.jointSegT`, `RL.realizesJCPT`, `RL.twoRunCT`, `RL.twoRunPRT` hand the lock-step obligation
`hstep` the segment position (`RL.InSeg`), but not *which* state of the first run the segment
starts at. A call hook of the first run at `u` (a program callee's machine run) can be related to
the callee's CLIF run only at the first run's call state of the count `n` that the step's
semantics `XI.at n` answers for (#729): the realisation knows it (`hP : P s` at the segment start
`s`, `P n = OnCall … n`, and the segment's call count `hcnt`), the old theorems pass it away.

* `RL.SegFrom` (`u` is `i` steps after a segment start satisfying `P`, before the end; the
  segment's machine calls are the step's, and a call state of the segment is its start, so a call
  hook at `u` is at the start, `i = 0`, where `P` holds: `RL.SegFrom.call`); `RL.segStart_of_qw`,
  `RL.segStart_of_qwa` (the same from `QWA`, the alignment of the Cranelift-frame realisation);
* `RL.jointSegTP`, `RL.realizesJCPTP`, **`RL.twoRunCTP`**, **`RL.twoRunPRTP`**: the same theorems
  with `hstep` also receiving `SegFrom` for the first run (same proofs); their joint trace also
  carries `RL.Good` of both runs' body states (a state after a call has the body's `sp`, what
  `PostTrace` asks; `realizes_allCWSF` gives it at every segment state, the old trace drops it).
-/

namespace Backend.Proof

open Backend E2E

/-- **`u` is `i` steps after a segment start satisfying `P`**, strictly before the segment's end,
the segment's machine calls are the step's (`opCalls`), and its call states are its start. -/
def RL.SegFrom (R : RL) (P : Arm.ArmState → Prop) (c : MConf CV Arm.ArmState) (i : Nat)
    (u : Arm.ArmState) : Prop :=
  ∃ s n, P s ∧ u = iterN R.step i s ∧ i < n ∧ countIn R.CallSt R.step s n = opCalls R.vc c ∧
    ∀ k < n, R.CallSt (iterN R.step k s) → k = 0

/-- **The call states of a realised segment are its start** (`realizes_allC0`'s argument, from
the alignment `QW` at the start and the segment's call count). -/
theorem RL.segStart_of_qw {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c : MConf CV Arm.ArmState} (hq : QW R s j ps1 T c) {n : Nat}
    (hcnt : countIn R.CallSt R.step s n = opCalls R.vc c) :
    ∀ k < n, R.CallSt (iterN R.step k s) → k = 0 := by
  intro k hk hck
  refine Classical.byContradiction fun hne => ?_
  have h1 : 1 ≤ countIn R.CallSt R.step s n := by
    obtain ⟨n', rfl⟩ : ∃ n', n = k + n' := ⟨n - k, by omega⟩
    rw [countIn_add]
    have := countIn_one_le (step := R.step) (s := iterN R.step k s) (n := n') (by omega) hck
    omega
  rw [hcnt] at h1
  obtain ⟨b, k', allocs, its, m, w, vb, ins, rfl, hvb, hi', hcI⟩ := opCalls_pos (vc := R.vc) h1
  have hcs := RL.callSt_of_q_call hq.q hvb hi' hcI
  have h2 := countIn_two_le hcs (Nat.pos_of_ne_zero hne) hk hck
  rw [hcnt] at h2
  simp [opCalls, hvb, hi', hcI] at h2

/-- **`RL.segStart_of_qw` from `QWA`** (the alignment `realizes_allCWSF` carries since the
Cranelift frame, #479: `QW ∧ AInv` or a return tail). -/
theorem RL.segStart_of_qwa {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c : MConf CV Arm.ArmState} (hq : QWA R s j ps1 T c) {n : Nat}
    (hcnt : countIn R.CallSt R.step s n = opCalls R.vc c) :
    ∀ k < n, R.CallSt (iterN R.step k s) → k = 0 := by
  intro k hk hck
  refine Classical.byContradiction fun hne => ?_
  have h1 : 1 ≤ countIn R.CallSt R.step s n := by
    obtain ⟨n', rfl⟩ : ∃ n', n = k + n' := ⟨n - k, by omega⟩
    rw [countIn_add]
    have := countIn_one_le (step := R.step) (s := iterN R.step k s) (n := n') (by omega) hck
    omega
  rw [hcnt] at h1
  obtain ⟨b, k', allocs, its, m, w, vb, ins, rfl, hvb, hi', hcI⟩ := opCalls_pos (vc := R.vc) h1
  have hcs := RL.callSt_of_q_call (qa_q hq.qa).choose_spec hvb hi' hcI
  have h2 := countIn_two_le hcs (Nat.pos_of_ne_zero hne) hk hck
  rw [hcnt] at h2
  simp [opCalls, hvb, hi', hcI] at h2

/-- **A call state in `SegFrom` is the segment start**: `P` holds there. -/
theorem RL.SegFrom.call {R : RL} {P : Arm.ArmState → Prop} {c : MConf CV Arm.ArmState} {i : Nat}
    {u : Arm.ArmState} (h : R.SegFrom P c i u) (hc : R.CallSt u) : i = 0 ∧ P u := by
  obtain ⟨s, n, hP, rfl, hi, -, hst⟩ := h
  obtain rfl := hst i hi hc
  exact ⟨rfl, hP⟩

/-- **`RL.jointSegT` with the first run's segment start handed to the lock step.** -/
theorem RL.jointSegTP {R R' : RL} (hR : R.Wf) (hR' : R'.Wf) (hsc : R.SameCode R')
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
    (hstep : ∀ i u u', R.InSeg Ok c i u → R.SegFrom P c i u → R'.InSeg Ok' c' i u' →
      (R.GoodX u ∧ R.WReadsIn Ok u) → (R'.GoodX u' ∧ R'.WReadsIn Ok' u') →
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
  obtain ⟨n, d, hm, -, hqd, ht, hcnt, hs, hf⟩ :=
    realizes_allCWSF hR Ok hC hT hTls hcov hq hP he
  obtain ⟨n', d', hm', -, hqd', ht', hcnt', hs', hf'⟩ :=
    realizes_allCWSF hR' Ok' hC' hT' hTls' hcov' hq' hP' he'
  have hd := hsh d d' hm hm'
  obtain ⟨rfl, hL⟩ := RL.seg_lock hsc hc hd hs hs' Lk hLpc h0 fun i hi hi' hl =>
    hstep i _ _ ⟨s, j, ps1, T, d, n, hq, hm, hs, hi, rfl, hf⟩
      ⟨s, n, hP, rfl, hi, hcnt, RL.segStart_of_qwa hq hcnt⟩
      ⟨s', j, ps1, T, d', n', hq', hm', hs', hi', rfl, hf'⟩
      (ht i hi) (ht' i hi') hl
  have hW := RL.nextW_shape hsc j ps1 T hc hd
  rw [hW] at hqd'
  exact ⟨n, d, d', hm, hm', hd, hqd, hqd', fun i hi => ⟨ht i hi, ht' i hi⟩, hcnt, hcnt',
    hs, hs', hL⟩

set_option maxHeartbeats 1000000 in
/-- **`RL.realizesJCPT` with the first run's segment start handed to the lock step.** -/
theorem RL.realizesJCPTP {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
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
      ({ R with X := XI.at n } : RL).InSeg (OkS c c') c i u →
      ({ R with X := XI.at n } : RL).SegFrom (fun u => P n u ∧ spOf u = R.spB) c i u →
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
      Lk c c' i u u' → LB d d' u u') :
    ∀ n n', RealizesJCP R.vc R.rf (({ R with X := XI.at n } : RL).semGS OkG)
      (({ R with s0 := t0, G := G', X := XI'.at n' } : RL).semGS OkG') ckeep
      ({ R with X := XI.at 0 } : RL).step ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step K
      (JR R ({ R with s0 := t0, G := G' } : RL) K LB)
      (fun u u' => (∃ c c' i, Lk c c' i u u') ∧ R.Good u ∧ ({ R with s0 := t0, G := G' } : RL).Good u')
      (RL.CallSt R) (RL.CallSt R) (P n) (P' n') := by
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
    RL.jointSegTP (R := Rn) (R' := Rn') (hRn n) (hRn' n') hsc (OkS c c') (OkS' c c')
      (hC n) (fun h => hT h n) (fun h => hTls h n) (hC' n') (fun h => hT' h n')
      (fun h => hTls' h n') hcov hcov hqn hqn' ⟨hP, QWA.sp_of_mstep (R := Rn) hqn hd⟩
      ⟨hP', QWA.sp_of_mstep (R := Rn') hqn' hd'⟩ hsh (hG n c c' d hK hd) (hG' n' c c' d' hK hd')
      (fun a b ha hb => (hshK a b (lift a ha) (lift' b hb)).1) (Lk c c') (hLpc c c')
      (hstart c c' s s' hK hLB) fun i u u' hi hp hi' h1 h2 hl =>
        hstep n n' c c' i u u' hK hi hp hi' h1 h2 hl
  have hE := lift e he
  have hE' := lift' e' he'
  obtain ⟨-, hKe⟩ := hshK e e' hE hE'
  have hq1 := QWA.ofWithX (R := R) hPn hqe
  have hq1' := QWA.ofWithX (R := ({ R with s0 := t0, G := G' } : RL)) hPn' hqe'
  exact ⟨m, e, e', hE, hE', ⟨⟨_, hq1, hq1'⟩, hse, hKe,
    hend c c' e e' m _ _ hK hKe hse ⟨_, hq1, hq1'⟩ (hL m (Nat.le_refl _))⟩,
    fun i hi => ⟨⟨c, c', i, hL i (Nat.le_of_lt hi)⟩, (ht i hi).1.1.good, (ht i hi).2.1.good⟩,
    hcnt, hcnt'⟩

set_option maxHeartbeats 2000000 in
/-- **`RL.twoRunCT` with the first run's segment start handed to the lock step** (same proof,
on `RL.realizesJCPTP`). -/
theorem RL.twoRunCTP {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
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
      ({ R with X := XI.at n } : RL).SegFrom (fun u =>
        OnCall ({ R with X := XI.at 0 } : RL).step R.fa R.base R.s0 n u ∧ spOf u = R.spB) c i u →
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
      (∀ i < N, (∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
        R.Good (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0) ∧
        ({ R with s0 := t0, G := G' } : RL).Good (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
          RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
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
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' ∧
      R.RetsAt e ∧ R.RetsAt e' := by
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
  have hJ := RL.realizesJCPTP (R := R) (t0 := t0) (G' := G') (XI := XI) (XI' := XI') hRn hRn' hsP hsP'
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
  refine ⟨N, _, _, fun i hi => ⟨ht0 i hi, ht0' i hi⟩, fun i hi => ?_, hJ2, fun i hi => ?_, ?_, ?_,
    ⟨_, _, _, _, _, _, _, _, rfl, hvb, hi⟩, ⟨_, _, _, _, _, _, _, _, rfl, hvb2, hi2⟩⟩
  · rw [hs, hs']; exact htN i hi
  · rw [Nat.add_assoc, hs, hs', iterN_add, iterN_add]
    exact ⟨ht3 i hi, ht3' i hi⟩
  · rw [Nat.add_assoc, hs, iterN_add]; exact hpc3
  · rw [Nat.add_assoc, hs', iterN_add]; exact hpc3'

set_option maxHeartbeats 2000000 in
/-- **`RL.twoRunPRT` with the first run's segment start handed to the lock step** (same proof,
on `RL.twoRunCTP`). -/
theorem RL.twoRunPRTP {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
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
      ({ R with X := XI.at n } : RL).SegFrom (fun u =>
        OnCall ({ R with X := XI.at 0 } : RL).step R.fa R.base R.s0 n u ∧ spOf u = R.spB) c i u →
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
      (∀ i < N, (∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
        R.Good (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0) ∧
        ({ R with s0 := t0, G := G' } : RL).Good (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
          RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
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
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' ∧
      R.RetsAt e ∧ R.RetsAt e' := by
  subst hR
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hemit
  subst hk
  obtain ⟨ckc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  have hF := he.hF
  have hF' := he'.hF
  subst hF hF'
  exact RL.twoRunCTP (R := actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)) (t0 := t0)
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
