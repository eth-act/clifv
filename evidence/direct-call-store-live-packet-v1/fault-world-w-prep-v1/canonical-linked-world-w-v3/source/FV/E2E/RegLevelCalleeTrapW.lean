import FV.E2E.WorldTrapStop
import FV.E2E.RegLevelFrameW
import FV.E2E.DeadCleanupRealizesW

namespace Backend.Proof
open Backend E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

theorem realizes_trapT_trace {R : RL} {good : Arm.ArmState → Prop} {sem₀ semU : Sem} {XR : XRaise}
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (QA R) good)
    (hagree : ∀ i uses w, NoRaise XR i uses w → semU i uses w = sem₀ i uses w)
    (hcall : ∀ info uses w r obj w', semU (.call info) uses w = some r →
      XR.raise (callDest info) uses w = some (obj, w') → r.2.2 = .halt)
    (hnt : R.vc.hasTryCall = false) :
    Realizes R.vc R.rf semU ckeep R.step (QA R) good := by
  intro s c c' hqa hm
  have old : MStep R.vc sem₀ ckeep R.rf c c' →
      (∀ b k allocs its m w vb i ops, c = .run ⟨b, .op k allocs :: its, m, w⟩ →
        R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
        NoRaise XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w) →
      ∃ n c'', MStep R.vc semU ckeep R.rf c c'' ∧
        QA R (iterN R.step n s) c'' ∧ ∀ i < n, good (iterN R.step i s) := by
    intro hm0 hnr
    obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s c c' hqa hm0
    exact ⟨n, c'', mstep_congr hm'' fun b k allocs its m w vb i ops hc hvb hi hops =>
      (hagree _ _ _ (hnr b k allocs its m w vb i ops hc hvb hi hops)).symm, hq'', ht⟩
  cases hm with
  | move =>
    exact old .move fun _ _ _ _ _ _ _ _ _ hc => by cases hc
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc semU ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    by_cases hr : NoRaise XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w
    · refine old (mstep_congr hstep fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_)
        fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hagree _ _ _ hr
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hr
    · simp only [NoRaise, Classical.not_forall] at hr
      obtain ⟨info, hik, hraise⟩ := hr
      obtain ⟨⟨obj, w2⟩, hraise⟩ := Option.ne_none_iff_exists'.mp hraise
      rcases hik with rfl | ⟨ti, rfl⟩
      · have hc := hcall info _ w (outs, w', ctl) obj w2 hsem hraise
        simp only at hc
        subst hc
        cases hn with
        | halt => exact ⟨0, _, hstep, .inl ⟨trivial, trivial⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · have := hasTryCall_of_mem hvb hi
        rw [hnt] at this; cases this


theorem regLevel_calleeTrap_coreW {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    {XT : Option String → List CV → Arm.ArmState → Prop}
    (hgot : GotSem R.gv R.X semU)
    (hRz : Realizes R.vc R.rf semU ckeep R.step (QA R) R.GoodXW)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ obj w', VUnwinds R.vc semU (xrT XT) (ρsel m₀) w₀ obj w' →
      ∃ n, R.CallTrapPre XT (E2E.runX R.step n R.s0) ∧
        (∀ i < n, R.GoodXW (E2E.runX R.step i R.s0)) ∧
        spOf (E2E.runX R.step n R.s0) = R.spB ∧
        (E2E.runX R.step n R.s0).program = R.fb.program R.base) := by
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_initW hR hent hbe
  obtain ⟨hSim, hinit, -⟩ := checkedAt_sound_match (sem := semU) (keep := ckeep) hcheck
    (locVal R.fr (iterN R.step n0 R.s0)) (ρsel (locVal R.fr (iterN R.step n0 R.s0))) w₀ (hsel _)
  have hfin : ∀ n1 n2 n3, E2E.runX R.step (n0 + n1 + n2 + n3) R.s0 =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 R.s0))) := by
    intro n1 n2 n3
    rw [runX_eq]
    simp only [iterN_add]
  refine ⟨locVal R.fr (iterN R.step n0 R.s0), ?_⟩
  intro obj w' hu
  obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
  obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
  have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w1⟩) (.halt w') :=
    VStep.step hvb hi hops hsem hlen VNext.halt
  obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
    forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
  obtain ⟨u, hu⟩ : ∃ u, iterN R.step n2 (iterN R.step n1 (iterN R.step n0 R.s0)) = u :=
    ⟨_, rfl⟩
  rw [hu] at hq2
  cases hms with
  | move => obtain ⟨_, e⟩ := hSim.run hr3; cases e
  | @op b' k' allocs its m w2 vb' i2 ops2 outs2 outs2' w2' ctl m2 c3 hvb' hi' hops' hsz hsem2
      hlen2 hho hcl hn =>
    obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
    simp only at hb' hk' hw'
    subst hb' hk' hw'
    rw [hvb] at hvb'; cases hvb'
    rw [hi] at hi'; cases hi'
    rw [hops] at hops'; cases hops'
    -- the allocated code reads the VCode's uses: the same trapping callee
    have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
      hops
    have hq2 := (qa_op hq2 hvb hi (fun us h => by cases h)).1
    obtain ⟨j0, items, pre, regs, i', cA, cB, ls1, ls2, ps1, psm, ps2, T', cc', wh, ops'', hal, hit,
      hsplit, hasg, hc1', hops'', hstat, hchk', hcode2, h1', h2', htr', hdrop, hpc, hst⟩ :=
      q_op hq2 hvb hi
    rw [hops] at hops''; cases hops''
    subst hal
    have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal u r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    have hraise' : (xrT XT).raise (callDest info) (useVals ops regs u) w1 = some (obj, w') := by
      rw [← useVals_of_store hstat hm', hU0]
      exact hraise
    have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
      rw [← useVals_of_store hstat hm', hU0]
      exact (hgot _ _ _ _).1 hsem
    have hcpc := callAt_of_q hq2 hvb hi call_hcall regs i' rfl hasg
    have hrun : E2E.runX R.step (n0 + n1 + n2) R.s0 = u := by
      rw [← hu, runX_eq]
      simp only [iterN_add]
    refine ⟨n0 + n1 + n2, ?_, fun i hi => ?_, by rw [hrun]; exact hst.sp,
      by rw [hrun]; exact hst.prog⟩
    · rw [hrun]
      exact ⟨info, ⟨b, vb, k, hvb, hi⟩, by rw [hst.sp]; exact RL.K_le hR,
        fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs,
        i', w1, hops, hstat, hasg, hcpc, hst.world, hst.align, hst.err, hgg,
        (xrT_some hraise').1⟩
    · rw [runX_eq]
      exact trace_add ht0 (trace_add ht1 ht2) i (by omega)

end Backend.Proof
