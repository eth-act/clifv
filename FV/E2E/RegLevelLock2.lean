import FV.E2E.RegLevelCorrectCW

/-!
# One segment of two activations, in lock-step (SEM1 #537, item (3))

Two activations of one compiled function (`R`, and `R'` = `R` with another entry state, kept set,
external semantics, hooks and budget), started at one witness at shape-equal configurations,
realise shape-equal `MStep` successors by segments of the same length, provided a lock
predicate (index-dependent, implying equal pcs) holds at the segment start and is kept by every
pair of steps at the segment's states (with both runs' trace facts there):

* `firstArr_eq_min`: `firstArr_eq` with the pcs agreeing only up to the shorter run;
* `RL.nextW_shape`, `RL.emptyW_shape`, **`RL.segLenA_eq_shape`**: the segment length is decided
  by the shapes, the witness and the pcs (up to the shorter segment);
* **`RL.seg_lock`**: the lock at every index of the segment, and equal lengths;
* **`RL.jointSeg`**: `realizes_allCW` for both activations, in lock-step.
-/

namespace Backend.Proof

open Backend E2E

/-- **Two first arrivals at one pc take the same number of steps** when the pcs agree up to the
shorter one (and the zero-length cases agree). -/
theorem firstArr_eq_min {f f' : Arm.ArmState → Arm.ArmState} {s s' : Arm.ArmState} {n n' : Nat}
    {p : BitVec 64} (h : FirstArr f s n p) (h' : FirstArr f' s' n' p)
    (hpc : ∀ i ≤ min n n', Arm.r .PC (iterN f i s) = Arm.r .PC (iterN f' i s'))
    (hz : n = 0 ↔ n' = 0) : n = n' := by
  rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (hz.mp h0) (by omega)
    · exact absurd ((hpc n (by omega)).symm.trans h.1) (h'.2 n h0 hlt)
  · exact heq
  · rcases Nat.eq_zero_or_pos n' with h0 | h0
    · exact absurd (hz.mpr h0) (by omega)
    · exact absurd ((hpc n' (by omega)).trans h'.1) (h.2 n' h0 hgt)

/-- **The next witness sees only the shapes** (for two activations of one compiled function). -/
theorem RL.nextW_shape {R R' : RL} (h : R.SameCode R') (j : Nat) (ps1 : PState) (T : List Line)
    {c d c' d' : MConf CV Arm.ArmState} (hc : MConf.ShapeEq c c') (hd : MConf.ShapeEq d d') :
    R'.nextW j ps1 T c' d' = R.nextW j ps1 T c d := by
  rw [RL.nextW_congr h]
  cases c with
  | run s =>
    obtain ⟨b, its, m, w⟩ := s
    cases c' with
    | run s' =>
      obtain ⟨b', its', m', w'⟩ := s'
      obtain ⟨rfl, rfl⟩ := hc
      cases d with
      | run t =>
        obtain ⟨b'', its'', m₂, w₂⟩ := t
        cases d' with
        | run t' =>
          obtain ⟨b₃, its₃, m₃, w₃⟩ := t'
          obtain ⟨rfl, rfl⟩ := hd
          exact RL.nextW_run j ps1 T b b'' its its'' m m₂ m' m₃ w w₂ w' w₃
        | ret => exact hd.elim
        | halt => exact hd.elim
      | ret =>
        cases d' with
        | ret => cases its <;> rfl
        | run => exact hd.elim
        | halt => exact hd.elim
      | halt =>
        cases d' with
        | halt => cases its <;> rfl
        | run => exact hd.elim
        | ret => exact hd.elim
    | ret => exact hc.elim
    | halt => exact hc.elim
  | ret =>
    cases c' with
    | ret => rfl
    | run => exact hc.elim
    | halt => exact hc.elim
  | halt =>
    cases c' with
    | halt => rfl
    | run => exact hc.elim
    | ret => exact hc.elim

/-- **The zero-length case sees only the shapes.** -/
theorem RL.emptyW_shape {R R' : RL} (h : R.SameCode R') (j : Nat) (ps1 : PState) (T : List Line)
    {c d c' d' : MConf CV Arm.ArmState} (hc : MConf.ShapeEq c c') (hd : MConf.ShapeEq d d') :
    R'.EmptyW j ps1 T c' d' ↔ R.EmptyW j ps1 T c d := by
  have hW := RL.nextW_shape h j ps1 T hc hd
  have hS : RL.Straight c' d' ↔ RL.Straight c d := by
    cases c with
    | run s =>
      obtain ⟨b, its, m, w⟩ := s
      cases c' with
      | run s' =>
        obtain ⟨b', its', m', w'⟩ := s'
        obtain ⟨rfl, rfl⟩ := hc
        cases d with
        | run t =>
          obtain ⟨b'', its'', m₂, w₂⟩ := t
          cases d' with
          | run t' =>
            obtain ⟨b₃, its₃, m₃, w₃⟩ := t'
            obtain ⟨rfl, rfl⟩ := hd
            cases its <;> exact Iff.rfl
          | ret => exact hd.elim
          | halt => exact hd.elim
        | ret =>
          cases d' with
          | ret => cases its <;> exact Iff.rfl
          | run => exact hd.elim
          | halt => exact hd.elim
        | halt =>
          cases d' with
          | halt => cases its <;> exact Iff.rfl
          | run => exact hd.elim
          | ret => exact hd.elim
      | ret => exact hc.elim
      | halt => exact hc.elim
    | ret =>
      cases c' with
      | ret => exact Iff.rfl
      | run => exact hc.elim
      | halt => exact hc.elim
    | halt =>
      cases c' with
      | halt => exact Iff.rfl
      | run => exact hc.elim
      | ret => exact hc.elim
  have hL : R'.L = R.L := by simp only [RL.L, h.fa]
  unfold RL.EmptyW
  by_cases hs : RL.Straight c d
  · rw [if_pos hs, if_pos (hS.mpr hs), hW]
  · rw [if_neg hs, if_neg (fun h' => hs (hS.mp h')), hL]

/-- **Two segments at one witness, of shape-equal steps, with pcs agreeing up to the shorter,
have the same length.** -/
theorem RL.segLenA_eq_shape {R R' : RL} (h : R.SameCode R') {j : Nat} {ps1 : PState}
    {T : List Line} {c d c' d' : MConf CV Arm.ArmState} {s s' : Arm.ArmState} {n n' : Nat}
    (hc : MConf.ShapeEq c c') (hd : MConf.ShapeEq d d')
    (hs : R.SegLenA j ps1 T c d s n) (hs' : R'.SegLenA j ps1 T c' d' s' n')
    (hpc : ∀ i ≤ min n n', Arm.r .PC (iterN R.step i s) = Arm.r .PC (iterN R'.step i s')) :
    n = n' := by
  cases d with
  | run t =>
    cases d' with
    | run t' =>
      have hp : R'.pcOf (R'.nextW j ps1 T c' (.run t')).1 =
          R.pcOf (R.nextW j ps1 T c (.run t)).1 := by
        rw [RL.nextW_shape h j ps1 T hc hd]
        simp only [RL.pcOf, RL.L, h.fa, h.base]
      have h1 := hs'.1
      rw [hp] at h1
      exact firstArr_eq_min hs.1 h1 hpc
        (hs.2.trans ((RL.emptyW_shape h j ps1 T hc hd).symm.trans hs'.2.symm))
    | ret => exact hd.elim
    | halt => exact hd.elim
  | ret =>
    cases d' with
    | ret => exact (hs : n = 0).trans (hs' : n' = 0).symm
    | run => exact hd.elim
    | halt => exact hd.elim
  | halt =>
    cases d' with
    | halt => exact (hs : n = 0).trans (hs' : n' = 0).symm
    | run => exact hd.elim
    | ret => exact hd.elim

/-- **One segment of two activations in lock-step**: a lock (implying equal pcs) at the start,
kept by every pair of steps at indices before both segments' ends, holds at every index of the
segment, and the two segments have the same length. -/
theorem RL.seg_lock {R R' : RL} (h : R.SameCode R') {j : Nat} {ps1 : PState} {T : List Line}
    {c d c' d' : MConf CV Arm.ArmState} {s s' : Arm.ArmState} {n n' : Nat}
    (hc : MConf.ShapeEq c c') (hd : MConf.ShapeEq d d')
    (hs : R.SegLenA j ps1 T c d s n) (hs' : R'.SegLenA j ps1 T c' d' s' n')
    (Lk : Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ i u u', Lk i u u' → Arm.r .PC u = Arm.r .PC u') (h0 : Lk 0 s s')
    (hstep : ∀ i, i < n → i < n' → Lk i (iterN R.step i s) (iterN R'.step i s') →
      Lk (i + 1) (R.step (iterN R.step i s)) (R'.step (iterN R'.step i s'))) :
    n = n' ∧ ∀ i ≤ n, Lk i (iterN R.step i s) (iterN R'.step i s') := by
  have hL : ∀ i ≤ min n n', Lk i (iterN R.step i s) (iterN R'.step i s') := by
    intro i hi
    induction i with
    | zero => exact h0
    | succ i ih =>
      have e1 : iterN R.step (i + 1) s = R.step (iterN R.step i s) := by
        rw [iterN_add]; rfl
      have e2 : iterN R'.step (i + 1) s' = R'.step (iterN R'.step i s') := by
        rw [iterN_add]; rfl
      rw [e1, e2]
      exact hstep i (by omega) (by omega) (ih (by omega))
  have hn := RL.segLenA_eq_shape h hc hd hs hs' fun i hi => hLpc i _ _ (hL i hi)
  subst hn
  exact ⟨rfl, fun i hi => hL i (by omega)⟩

/-- **`realizes_allCW` for two activations of one compiled function, in lock-step**: started at
one witness at shape-equal configurations, with shape-equal successors (`hsh`), both realise
their step by a segment of the same length, ending at shape-equal configurations at one witness;
the lock holds at every index of the segment. -/
theorem RL.jointSeg {R R' : RL} (hR : R.Wf) (hR' : R'.Wf) (hsc : R.SameCode R')
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
    (he : MStep R.vc (R.semG Ok) ckeep R.rf c e) (he' : MStep R'.vc (R'.semG Ok') ckeep R'.rf c' e')
    (hsh : ∀ d d', MStep R.vc (R.semG Ok) ckeep R.rf c d →
      MStep R'.vc (R'.semG Ok') ckeep R'.rf c' d' → MConf.ShapeEq d d')
    (Lk : Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ i u u', Lk i u u' → Arm.r .PC u = Arm.r .PC u') (h0 : Lk 0 s s')
    (hstep : ∀ i u u', (R.GoodX u ∧ R.WReadsIn Ok u) → (R'.GoodX u' ∧ R'.WReadsIn Ok' u') →
      Lk i u u' → Lk (i + 1) (R.step u) (R'.step u')) :
    ∃ n d d', MStep R.vc (R.semG Ok) ckeep R.rf c d ∧ MStep R'.vc (R'.semG Ok') ckeep R'.rf c' d' ∧
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
  obtain ⟨n, d, hm, -, hqd, ht, hcnt, hs⟩ := realizes_allCW hR Ok hC hT hTls hcov hq hP he
  obtain ⟨n', d', hm', -, hqd', ht', hcnt', hs'⟩ :=
    realizes_allCW hR' Ok' hC' hT' hTls' hcov' hq' hP' he'
  have hd := hsh d d' hm hm'
  obtain ⟨rfl, hL⟩ := RL.seg_lock hsc hc hd hs hs' Lk hLpc h0 fun i hi hi' hl =>
    hstep i _ _ (ht i hi) (ht' i hi') hl
  have hW := RL.nextW_shape hsc j ps1 T hc hd
  rw [hW] at hqd'
  exact ⟨n, d, d', hm, hm', hd, hqd, hqd', fun i hi => ⟨ht i hi, ht' i hi⟩, hcnt, hcnt',
    hs, hs', hL⟩

end Backend.Proof
