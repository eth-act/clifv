import FV.E2E.RegLevelJointRL
import FV.E2E.RegLevelTwoRun

/-!
# Two activations along a paired VCode run, from the entries (SEM1 #537, item (3))

`forward2C_op` instantiated at the counted guarded semantics of two activations of one compiled
function (`RL.realizesJCP`), from the two body entries: both run the prologue (the same number of
steps), are jointly realised along a pair VCode run that returns (`PStep`, ending in a `rets`
step of both runs), and run the epilogue (`RL.retLen` steps each) to their return addresses. The
two runs take the same number of steps; between the prologue and the epilogue the joint trace
(some segment lock `Lk`) holds at every index, and the joint invariant `JR` at the `rets` item.

* `VStep.rets_of_ret`: a VCode step to a return executes a `rets` instruction;
* **`RL.twoRunC`**.
-/

namespace Backend.Proof

open Backend E2E

/-- **A VCode step to a return executes a `rets` instruction.** -/
theorem VStep.rets_of_ret {W : Type} {vc : VCode} {sem : ISem CV W} {x : VConf CV W}
    {vals : List CV} {w : W} (h : VStep vc sem x (.ret vals w)) :
    ∃ b k ρ wx vb rs, x = .run ⟨b, k, ρ, wx⟩ ∧ vc.blocks[b]? = some vb ∧
      vb.insts[k]? = some (.rets rs) := by
  cases h with
  | step hvb hi _ _ _ hn =>
    cases hn with
    | ret he => subst he; exact ⟨_, _, _, _, _, _, rfl, hvb, hi⟩

set_option maxHeartbeats 2000000 in
/-- **Two activations of one compiled function along a returning pair VCode run** (module doc).
`R` is entered at `R.s0` with external semantics `XI.at n` at call number `n`; the second
activation is `R` entered at `t0` with kept set `G'` and `XI'`. The pair run starts at the two
initial VCode configurations (one vreg file `ρ₀`) and ends with a `rets` step of both. `K`,
`LB`, `OkS`, `Lk` and their premises are `RL.realizesJCP`'s; `hK` derives `K` from the checker
relation of both runs and the pair invariant, `hpro` gives the boundary lock after the
prologues. -/
theorem RL.twoRunC {R : RL} {t0 : Arm.ArmState} {G' : BitVec 64 → Prop} {XI XI' : ExtSemI}
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
    (hp : Star (PStep R.vc (csemVIG R.gv R.F R.ctx XI OkG)
      (csemVIG R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI)
      (VConf.init ρ₀ (w₀, 0), VConf.init ρ₀ (w₀', 0)) (x, x'))
    (hpi0 : PI (VConf.init ρ₀ (w₀, 0)) (VConf.init ρ₀ (w₀', 0))) (hpix : PI x x')
    (hy : PStep R.vc (csemVIG R.gv R.F R.ctx XI OkG)
      (csemVIG R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI (x, x')
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
  obtain ⟨hSim, hinit⟩ := isSimulationS_match (sem := csemVIG R.gv R.F R.ctx XI OkG)
    (keep := ckeep) hcheck (locVal R.fr s₁) ρ₀ (w₀, 0) (hsel _)
  obtain ⟨hSim', hinit'⟩ := isSimulationS_match (sem := csemVIG R.gv R''.F R.ctx XI' OkG')
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
  have hJ := RL.realizesJCP (R := R) (t0 := t0) (G' := G') (XI := XI) (XI' := XI') hRn hRn' hsP hsP'
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
    forward2C_op (sem := fun n => csemVG R.gv R.F R.ctx (XI.at n) OkG)
      (sem' := fun n => csemVG R.gv R''.F R.ctx (XI'.at n) OkG')
      (s0 := s₁) (s0' := s₁') hJ (onCall_of_run hP0) (onCall_of_run hP0') hSim hSim'
      (hK := hK) hp hy hpix hinit hinit' hpi0 ⟨rfl, rfl⟩ rfl rfl
      ⟨⟨R0.initW, .inl ⟨hq1, hA0⟩, .inl ⟨hq1', hA0'⟩⟩, ⟨rfl, rfl⟩,
        hK _ _ _ _ hinit hinit' hpi0, hpro⟩
  -- the pair state steps to returns: both execute the `rets` instruction
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

end Backend.Proof
