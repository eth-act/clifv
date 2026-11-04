import FV.E2E.RegLevelCorrectPRSNG

/-!
# The per-state trace up to the return in the oracle world (SEM1 #537, executable level)

`RegLevelCorrectPRSNG.lean`'s theorems (same proofs) whose return index `n` also has, at every
step before it, the register-level per-state facts `actGoodX` of the activation (`RL.GoodX`),
for the external semantics `XI.at m` of some call count `m` (the realisation of the counted run
has the facts of the call number's semantics; `RL.GoodX` mentions `X` only through its call
contract). The executable machine needs them at every state (`RunGoodL`, `LinkGood.lean`).

* `regLevelCorrect_world_atCSNX`, `_worldCSNX`, **`_worldPRSNX`**, and the value-semantics copies
  `_world_value_atCSNX`, `_value_worldCSNX`, **`_value_worldPRSNX`**.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver Backend.DeadCleanup

private theorem valueSemV_haltIX {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {X : ExtSem} {i : MInst} {us outs : List CV}
    {w w' : Arm.ArmState} (h : valueSemV gv F ctx X i us w = some (outs, w', .halt)) :
    csemV gv F ctx X i us w = some (outs, w', .halt) := by
  by_cases hp : specForm i = true
  · have hs : mspec ctx.slotBase i us w = some (outs, w', .halt) := by
      simpa [valueSemV, hp] using h
    have := mspec_spec_next hp hs
    cases this
  · simpa [valueSemV, hp] using h

/-- **`regLevelCorrect_world_atCSNG` with the per-state trace up to the return**: every step
before `n` has `actGoodX` for the semantics `XI.at m` of some `m`. -/
theorem regLevelCorrect_world_atCSNX {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkGP (fun u => OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w nc, VRetFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XI.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_initN hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf (csemVI R.gv R.F R.ctx XI) ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) (w₀, 0) (hsel _)
  have hP0 : countIn R.CallSt R.step s n0 = 0 := countIn_zero_of fun i hi => (ht0 i hi).2
  have hRzC : Realizes R.vc R.rf (csemVI R.gv R.F R.ctx XI) ckeep (stepC R.CallSt R.step)
      (fun p c => QA R p.1 (c.mapW Prod.fst) ∧ p.2 = c.world.2 ∧
        ∃ i, p = iterN (stepC R.CallSt R.step) i (iterN R.step n0 s, 0))
      (fun p => ∃ m, (Rn m).GoodX p.1) := by
    refine RealizesCP.countedRun (vc := R.vc) (rf := R.rf) (keep := ckeep)
      (sem := fun n => csemV R.gv R.F R.ctx (XI.at n))
      (Q := fun u c => QA R u c) (T := fun u => ∃ m, (Rn m).GoodX u) (C := R.CallSt)
      (P := fun n u => OnCall R.step fa base s n u) (s0 := iterN R.step n0 s) (fun n => ?_)
      (onCall_of_run hP0)
    have hq : ∀ u c, QA (Rn n) u c ↔ QA R u c := fun u c =>
      (RL.QA_withX (Rn n) (XI.at 0) (RL.sP_withX (hRn n) hent (XI.at 0)) u c).symm
    exact ((realizes_allC_sp (hRn n) (hC n) (fun h => hCT h n) (fun h => hTls h n) hcov).mono_T
      (T' := fun u => ∃ m, (Rn m).GoodX u) fun _ h => ⟨n, h⟩).congr_Q hq
  have hRz := Realizes.ofStepC (T := fun u => ∃ m, (Rn m).GoodX u) hRzC
  have hfin0 : ∀ n1 n2 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  have hfin1 : ∀ n1 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n3) s =
      iterN R.step n3 (iterN R.step n1 (iterN R.step n0 s)) := by
    intro n1 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun us vals w nc hret => ?_, fun c htr => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops
    cases hops
    obtain ⟨hsemV, hnc⟩ := ISem.counted_some hsem
    have hnc' : nc = w₁.2 := by simpa [MInst.isCallI] using hnc
    have hsem' := hsemV
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, hw, -⟩ := hsem'
    have h1 : VStep R.vc (csemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w₁⟩) (.ret vals (w, nc)) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_ (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    obtain ⟨n1, c', c'', hq2, hr2, hms, hr3, ht1, hcnt⟩ :=
      forward_lastC (Q := fun u c => QA R u (c.mapW Prod.fst))
        (T := fun u => ∃ m, (Rn m).GoodX u) hSim hRzC
        hstar h1 hinit (.inl ⟨hq0, hA0⟩) rfl
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      have hks := hkeep hr3
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        dsimp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [operands_retsC] at hops'; cases hops'
        cases hn with
        | ret _ =>
        obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
        simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, -, -⟩ := hsem3
        rw [rets_store hlen2 rfl hho hcl] at hks
        have hq2' : QA R (iterN R.step n1 (iterN R.step n0 s))
            (.run ⟨b, .op k _ :: _, _, w₁.1⟩) := hq2
        obtain ⟨mt, hq2''⟩ := qa_q hq2'
        have hst := q_stRel hq2''
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hsvd, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machineN hR hent hq2' hvb hi
        have htrG : ∀ i < n0 + n1 + n3, ∃ m, (Rn m).GoodX (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add (T := fun u => ∃ m, (Rn m).GoodX u) (fun j hj => ⟨0, (ht0 j hj).1⟩)
            (trace_add (T := fun u => ∃ m, (Rn m).GoodX u) ht1 fun j hj => ⟨0, (ht3 j hj).1⟩) i
            (by omega)
        have htrX : ∀ i < n0 + n1 + n3, R.GoodE (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
          intro i hi
          obtain ⟨m, h⟩ := htrG i hi
          exact ⟨h.good, h.err, h.prog⟩
        have htr : ∀ i < n0 + n1 + n3, R.Good (E2E.runX (ArmStepX (XI.at 0) H fa) i s) :=
          fun i hi => (htrX i hi).1
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 s) (.reg r) = regVal (iterN R.step n0 s) r :=
          fun _ => rfl
        refine ⟨n0 + n1 + n3, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
          fun i hi0 hi hpcall => ?_⟩
        rotate_right
        · exact (htr i hi).resolve_left (fun h => h hpcall)
        · have e0 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa) s n0 =
              0 := hP0
          have e1 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
              (iterN (ArmStepX (XI.at 0) H fa) n0 s) n1 = nc := by
            rw [hnc']; exact hcnt
          have e3 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
              (iterN (ArmStepX (XI.at 0) H fa) (n0 + n1) s) n3 = 0 := by
            rw [iterN_add]; exact countIn_zero_of fun j hj => (ht3 j hj).2
          rw [callsBefore_eq_countIn, countIn_add, countIn_add, e0, e1, e3, Nat.zero_add, Nat.add_zero]
        · exact fun i hi => ⟨(htrX i hi).2.1, (htrX i hi).2.2⟩
        · intro i hi
          obtain ⟨m, h⟩ := htrG i hi
          exact ⟨m, h.act⟩
        all_goals rw [hfin1]
        · exact hpc
        · exact herr
        · exact hsp
        · intro n hn
          simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
          obtain ⟨a, ha, rfl⟩ := hn
          by_cases h29 : a = 10
          · subst h29; exact hx29
          obtain ⟨hcs, hal⟩ := calleeSaved_x (n := 19 + a) (by omega) (by omega)
          by_cases hsv : Reg.x (19 + a) ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have hne : ∀ q, q < 32 → q ≠ 19 + a →
              Arm.StateField.GPR (rnum (19 + a)) ≠ .GPR (BitVec.ofNat 5 q) :=
            fun q h1 h2 e => rnum_ne (a := 19 + a) (b := q) (by omega) h1 (Ne.symm h2)
              (Arm.StateField.GPR.inj e)
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
            (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp)] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          by_cases hsv : Reg.v n ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)] at k1
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) s).setWidth 64
          rw [k2]
          exact setWidth128_inj k1
        · intro j v p x hj hx
          have e1 := hSim.ret hr3
          simp only [VConf.ret.injEq] at e1
          rw [e1.1] at hx
          exact hvalsM _ (operands_retsC ns) j v p x hj hx
        · intro a ha
          rw [hmem, ← hw]
          exact hst.world.2.1 a ha
        · intro f hf h29 h31
          rw [hfld f hf h29 h31, ← hw]
          exact hst.world.1 f hf
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hz1, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨0, .inl ⟨hq0, hA0⟩, rfl, 0, rfl⟩
    obtain ⟨hsemV, -⟩ := ISem.counted_some hsem
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub hsemV)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc (csemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', ⟨_, hq2, -⟩, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hz1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        dsimp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hq2'' : QA R (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s)))
            (.run ⟨b, .op k _ :: _, _, w.1⟩) := hq2
        have hnr : ∀ us, i ≠ .rets us := by
          intro us h
          rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
        have hq2' := (qa_op hq2'' hvb hi hnr).1
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, hholds⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, -⟩ := trap_udf hR hq2' hvb hi
          exact ⟨n0 + n1 + n2 + 0, by rw [hfin0]; exact htrap⟩
        · cases hn with
          | halt =>
          obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub hsem3)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds'⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, -, -⟩ := trap_trapIf hR hq2' hvb hi hops' hholds'
            exact ⟨n0 + n1 + n2 + n3, by rw [hfin0]; exact htrap⟩

/-- **`regLevelCorrect_worldCSNG` with the per-state trace up to the return.** -/
theorem regLevelCorrect_worldCSNX {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkGP (fun u => OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w nc, VRetFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atCSNX hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- **`regLevelCorrect_worldPRSNG` with the per-state trace up to the return.** -/
theorem regLevelCorrect_worldPRSNX {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    (hproph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P) {R : Nat → Arm.ArmState}
    (hregp : ProphRegOkM c (ArmStepX (XI.at 0) H fa) fa base s R)
    (hC : ∀ n, CalleeOkGP (fun u => OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n,
      CalleeTryOkGP (fun u =>
        OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w nc, VRetFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) :=
  regLevelCorrect_worldCSNX hcheck halloc hemit hlayout hcov hent hres hG
    (fun n => (hC n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n => (hCT h n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hTls hbe ρ₀

/-- **`regLevelCorrect_world_value_atCSNG` with the per-state trace up to the return.** -/
theorem regLevelCorrect_world_value_atCSNX {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkGP (fun u => OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w nc, VRetFrom vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XI.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_initN hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf (valueSemVI R.gv R.F R.ctx XI) ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) (w₀, 0) (hsel _)
  have hP0 : countIn R.CallSt R.step s n0 = 0 := countIn_zero_of fun i hi => (ht0 i hi).2
  have hRzC : Realizes R.vc R.rf (valueSemVI R.gv R.F R.ctx XI) ckeep (stepC R.CallSt R.step)
      (fun p c => QA R p.1 (c.mapW Prod.fst) ∧ p.2 = c.world.2 ∧
        ∃ i, p = iterN (stepC R.CallSt R.step) i (iterN R.step n0 s, 0))
      (fun p => ∃ m, (Rn m).GoodX p.1) := by
    refine RealizesCP.countedRun (vc := R.vc) (rf := R.rf) (keep := ckeep)
      (sem := fun n => valueSemV R.gv R.F R.ctx (XI.at n))
      (Q := fun u c => QA R u c) (T := fun u => ∃ m, (Rn m).GoodX u) (C := R.CallSt)
      (P := fun n u => OnCall R.step fa base s n u) (s0 := iterN R.step n0 s) (fun n => ?_)
      (onCall_of_run hP0)
    have hq : ∀ u c, QA (Rn n) u c ↔ QA R u c := fun u c =>
      (RL.QA_withX (Rn n) (XI.at 0) (RL.sP_withX (hRn n) hent (XI.at 0)) u c).symm
    exact ((realizes_value_allC_sp (hRn n) (hC n) (fun h => hCT h n) (fun h => hTls h n) hcov).mono_T
      (T' := fun u => ∃ m, (Rn m).GoodX u) fun _ h => ⟨n, h⟩).congr_Q hq
  have hRz := Realizes.ofStepC (T := fun u => ∃ m, (Rn m).GoodX u) hRzC
  have hfin0 : ∀ n1 n2 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  have hfin1 : ∀ n1 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n3) s =
      iterN R.step n3 (iterN R.step n1 (iterN R.step n0 s)) := by
    intro n1 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun us vals w nc hret => ?_, fun c htr => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops
    cases hops
    obtain ⟨hsemV, hnc⟩ := ISem.counted_some hsem
    have hnc' : nc = w₁.2 := by simpa [MInst.isCallI] using hnc
    have hsem' := hsemV
    simp only [valueSemV, specForm, pureForm, cmpForm, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, hw, -⟩ := hsem'
    have h1 : VStep R.vc (valueSemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w₁⟩) (.ret vals (w, nc)) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_ (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    obtain ⟨n1, c', c'', hq2, hr2, hms, hr3, ht1, hcnt⟩ :=
      forward_lastC (Q := fun u c => QA R u (c.mapW Prod.fst))
        (T := fun u => ∃ m, (Rn m).GoodX u) hSim hRzC
        hstar h1 hinit (.inl ⟨hq0, hA0⟩) rfl
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      have hks := hkeep hr3
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        dsimp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [operands_retsC] at hops'; cases hops'
        cases hn with
        | ret _ =>
        obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
        simp only [valueSemV, specForm, pureForm, cmpForm, Bool.false_or, Bool.false_eq_true,
          ↓reduceIte, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, -, -⟩ := hsem3
        rw [rets_store hlen2 rfl hho hcl] at hks
        have hq2' : QA R (iterN R.step n1 (iterN R.step n0 s))
            (.run ⟨b, .op k _ :: _, _, w₁.1⟩) := hq2
        obtain ⟨mt, hq2''⟩ := qa_q hq2'
        have hst := q_stRel hq2''
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hsvd, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machineN hR hent hq2' hvb hi
        have htrG : ∀ i < n0 + n1 + n3, ∃ m, (Rn m).GoodX (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add (T := fun u => ∃ m, (Rn m).GoodX u) (fun j hj => ⟨0, (ht0 j hj).1⟩)
            (trace_add (T := fun u => ∃ m, (Rn m).GoodX u) ht1 fun j hj => ⟨0, (ht3 j hj).1⟩) i
            (by omega)
        have htrX : ∀ i < n0 + n1 + n3, R.GoodE (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
          intro i hi
          obtain ⟨m, h⟩ := htrG i hi
          exact ⟨h.good, h.err, h.prog⟩
        have htr : ∀ i < n0 + n1 + n3, R.Good (E2E.runX (ArmStepX (XI.at 0) H fa) i s) :=
          fun i hi => (htrX i hi).1
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 s) (.reg r) = regVal (iterN R.step n0 s) r :=
          fun _ => rfl
        refine ⟨n0 + n1 + n3, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
          fun i hi0 hi hpcall => ?_⟩
        rotate_right
        · exact (htr i hi).resolve_left (fun h => h hpcall)
        · have e0 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa) s n0 =
              0 := hP0
          have e1 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
              (iterN (ArmStepX (XI.at 0) H fa) n0 s) n1 = nc := by
            rw [hnc']; exact hcnt
          have e3 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
              (iterN (ArmStepX (XI.at 0) H fa) (n0 + n1) s) n3 = 0 := by
            rw [iterN_add]; exact countIn_zero_of fun j hj => (ht3 j hj).2
          rw [callsBefore_eq_countIn, countIn_add, countIn_add, e0, e1, e3, Nat.zero_add, Nat.add_zero]
        · exact fun i hi => ⟨(htrX i hi).2.1, (htrX i hi).2.2⟩
        · intro i hi
          obtain ⟨m, h⟩ := htrG i hi
          exact ⟨m, h.act⟩
        all_goals rw [hfin1]
        · exact hpc
        · exact herr
        · exact hsp
        · intro n hn
          simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
          obtain ⟨a, ha, rfl⟩ := hn
          by_cases h29 : a = 10
          · subst h29; exact hx29
          obtain ⟨hcs, hal⟩ := calleeSaved_x (n := 19 + a) (by omega) (by omega)
          by_cases hsv : Reg.x (19 + a) ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have hne : ∀ q, q < 32 → q ≠ 19 + a →
              Arm.StateField.GPR (rnum (19 + a)) ≠ .GPR (BitVec.ofNat 5 q) :=
            fun q h1 h2 e => rnum_ne (a := 19 + a) (b := q) (by omega) h1 (Ne.symm h2)
              (Arm.StateField.GPR.inj e)
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
            (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp)] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          by_cases hsv : Reg.v n ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)] at k1
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) s).setWidth 64
          rw [k2]
          exact setWidth128_inj k1
        · intro j v p x hj hx
          have e1 := hSim.ret hr3
          simp only [VConf.ret.injEq] at e1
          rw [e1.1] at hx
          exact hvalsM _ (operands_retsC ns) j v p x hj hx
        · intro a ha
          rw [hmem, ← hw]
          exact hst.world.2.1 a ha
        · intro f hf h29 h31
          rw [hfld f hf h29 h31, ← hw]
          exact hst.world.1 f hf
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hz1, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨0, .inl ⟨hq0, hA0⟩, rfl, 0, rfl⟩
    obtain ⟨hsemV, -⟩ := ISem.counted_some hsem
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub (valueSemV_haltIX hsemV))
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc (valueSemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', ⟨_, hq2, -⟩, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hz1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        dsimp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hq2'' : QA R (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s)))
            (.run ⟨b, .op k _ :: _, _, w.1⟩) := hq2
        have hnr : ∀ us, i ≠ .rets us := by
          intro us h
          rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
        have hq2' := (qa_op hq2'' hvb hi hnr).1
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, hholds⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, -⟩ := trap_udf hR hq2' hvb hi
          exact ⟨n0 + n1 + n2 + 0, by rw [hfin0]; exact htrap⟩
        · cases hn with
          | halt =>
          obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub (valueSemV_haltIX hsem3))
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds'⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, -, -⟩ := trap_trapIf hR hq2' hvb hi hops' hholds'
            exact ⟨n0 + n1 + n2 + n3, by rw [hfin0]; exact htrap⟩

/-- **`regLevelCorrect_world_value_worldCSNG` with the per-state trace up to the return.** -/
theorem regLevelCorrect_world_value_worldCSNX {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkGP (fun u => OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w nc, VRetFrom vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_value_atCSNX hat (entryOk_of_le hle) halloc hemit hlayout hcov
    hent hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- **`regLevelCorrect_world_value_worldPRSNG` with the per-state trace up to the return.** -/
theorem regLevelCorrect_world_value_worldPRSNX {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    (hproph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P) {R : Nat → Arm.ArmState}
    (hregp : ProphRegOkM c (ArmStepX (XI.at 0) H fa) fa base s R)
    (hC : ∀ n, CalleeOkGP (fun u => OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n,
      CalleeTryOkGP (fun u =>
        OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w nc, VRetFrom vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) :=
  regLevelCorrect_world_value_worldCSNX hcheck halloc hemit hlayout hcov hent hres hG
    (fun n => (hC n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n => (hCT h n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hTls hbe ρ₀

end Backend.Proof
