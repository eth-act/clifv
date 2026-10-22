import FV.E2E.RegLevelMemTrapW
import FV.E2E.RegLevelFrameW
import FV.E2E.DeadCleanupRealizesW

/-!
# The register level of the memory traps with the writes (A3, #412, slice F8b)

`regLevel_memtrap_world_valueW`: `regLevel_memtrap_world_value` with `actGoodXW` (every state
before the trap state with `GoodX` and the writes `RL.WritesAt`).
-/

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup Backend.Proof.Driver

private theorem valueSemV_halt' {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {X : ExtSem} {i : MInst} {us outs : List CV}
    {w w' : Arm.ArmState} (h : valueSemV gv F ctx X i us w = some (outs, w', .halt)) :
    csemV gv F ctx X i us w = some (outs, w', .halt) := by
  by_cases hp : pureForm i = true
  · have hs : mspec ctx.slotBase i us w = some (outs, w', .halt) := by
      simpa [valueSemV, hp] using h
    have := (mspec_pure hp hs).2
    cases this
  · simpa [valueSemV, hp] using h

/-- **The register level of the explicit and the memory traps** under the dead-cleanup chain's
value semantics (`regLevelCorrect_world_atX_value`'s trap half): an explicit trap of the VCode run
is a `udf` trap site of the machine run, a memory trap (`VMemTraps … c A`) whose address ranges
have an unmapped byte (`A` implies `Unmapped mp`) is the state at the trapping loop's `ldaxr`
(`TrapAtM`), every earlier state `GoodXW` (`regLevel_memtrap_world_value` with the writes). -/
theorem regLevel_memtrap_world_valueW {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r)))
    (mp : ArmFault.MemMap) :
    ∃ m₀ : Loc → CV,
    (∀ c, VTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c (A : BitVec 64 → Nat → Prop), (∀ x n, A x n → Unmapped mp x n) →
      VMemTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c A →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm, by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres,
    ⟨body, hb⟩, hent.program, hG⟩
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_initW hR hent hbe
  have hRz0 := realizes_value_allW hR hC hCT hTls hcov
  have hmk : ∀ (n1 n23 : Nat), (∀ i < n1 + n23, R.GoodXW (iterN R.step i (iterN R.step n0 s))) →
      ∀ i < n0 + (n1 + n23), actGoodXW vcp rf af fa fb base s X H K G gv
        (E2E.runX (ArmStepX X H fa) i s) := by
    intro n1 n23 hb i hi
    rw [runX_eq]
    exact (trace_add ht0 hb i hi).act
  have hfin : ∀ n1 n2 n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun c htr => ?_, fun c A hA hmt => ?_⟩
  · -- an explicit trap
    have hck := (lowerRFunc_ok hR.alloc).2.2
    obtain ⟨Rl, hSim, hinit, -⟩ :=
      checkedAt_sound R.vc R.rf R.valueSem ckeep hcheck (locVal R.fr (iterN R.step n0 s))
        (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
    have hRz := hRz0
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, ⟨hq1, hA1⟩, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨hq0, hA0⟩
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub (valueSemV_halt' hsem))
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc R.valueSem (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 ⟨hq1, hA1⟩
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, hline⟩ := trap_udf_line hR hq2 hvb hi
          refine ⟨n0 + n1 + n2 + 0, by rw [hfin n1 n2]; exact ⟨htrap, .inl hline⟩,
            fun i hi => hmk n1 (n2 + 0)
              (trace_add ht1 (trace_add ht2 fun _ h => absurd h (Nat.not_lt_zero _))) i (by omega)⟩
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub (valueSemV_halt' hsem2))
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, hline, ht3⟩ := trap_trapIf_lineW hR hq2 hvb hi hops' hholds
            refine ⟨n0 + n1 + n2 + n3, by rw [hfin n1 n2]; exact ⟨htrap, .inl hline⟩,
              fun i hi => hmk n1 (n2 + n3) (trace_add ht1 (trace_add ht2 ht3)) i (by omega)⟩

  · -- a memory trap
    obtain ⟨b, k, ρ, w, vb, i, ops, hstar, hvb, hi, hops, hh, -⟩ := memTrap_halt hmt
    obtain ⟨hSim, hinit, -⟩ := checkedAt_sound_match (sem := haltLoop c A R.valueSem)
      (keep := ckeep) hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
    have hRz : Realizes R.vc R.rf (haltLoop c A R.valueSem) ckeep R.step
        (fun s c => Q R s c ∧ AInv R c) R.GoodXW := realizes_haltLoopW hRz0
    obtain ⟨n1, c1, ⟨hq1, hA1⟩, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨hq0, hA0⟩
    have h1 : VStep R.vc (haltLoop c A R.valueSem) (.run ⟨b, k, ρ, w⟩) (.halt w) :=
      VStep.step hvb hi hops (haltLoop_of hh w) (haltOuts_length hops) VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 ⟨hq1, hA1⟩
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
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      obtain ⟨nb, u, us, hlt, hu, hAu⟩ := hh
      obtain ⟨j, bits, hj, hbits, hnb, hpc, herr, huse⟩ := loop_ldaxr hR hq2 hvb hi hlt
      obtain ⟨us', hus'⟩ := huse ops hops
      have hu0 : u = regVal (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) (.x 25) := by
        have := hU0.symm.trans hus'
        rw [hu] at this
        exact (List.cons.inj this).1
      have hun : Unmapped mp (Arm.r (.GPR 25#5)
          (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s)))) (bits / 8) := by
        rw [hnb]
        have := hA _ _ hAu
        rwa [hu0, lo64_regVal_x] at this
      refine ⟨n0 + n1 + n2 + 0, ?_, fun i hi => hmk n1 (n2 + 0)
        (trace_add ht1 (trace_add ht2 fun _ h => absurd h (Nat.not_lt_zero _))) i (by omega)⟩
      rw [hfin n1 n2 0]
      exact ⟨trapAt_ins hR hj hpc herr, .inr ⟨j, bits, some c, hj, hbits, hpc, hun⟩⟩

end Backend.Proof
