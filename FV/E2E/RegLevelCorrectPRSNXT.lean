import FV.E2E.RegLevelTrapN
import FV.E2E.IselSimINT

/-!
# The per-state trace and the call count up to a trap in the oracle world (SEM1 #537)

`regLevelCorrect_world_atCSNX` (`RegLevelCorrectPRSNX`) gives, for a VCode trap, only the trap
site. Here, for a VCode trap whose trapping instruction runs at counter `nc` (`VTrapFromW`,
`IselSimINT`), the machine's trap index `n` also has (same setup; `forward_lastC` for the count,
`trap_udf` / `trap_trapIfN` for the trap's own steps, which pass no call state):

* `callsBefore … n = nc` (the machine's calls before the trap are the VCode's);
* at every step before `n`, no error and the activation's program, and `actGoodX` for the
  semantics `XI.at m` of some `m`;
* every state after the trap site's step errs.

`regLevelCorrect_world_atCSNXT`, `regLevelCorrect_worldCSNXT`, **`regLevelCorrect_worldPRSNXT`**.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver Backend.DeadCleanup

/-- **The trap clause of `regLevelCorrect_world_atCSNX` with the call count and the per-state
trace** (module doc). -/
theorem regLevelCorrect_world_atCSNXT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    ∀ c nc, VTrapFromW vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩ c
        (fun w => w.2 = nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XI.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
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
  have hfin0 : ∀ n1 n2 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun c nc htr => ?_⟩
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc, hnc⟩ := htr
  obtain ⟨hsemV, -⟩ := ISem.counted_some hsem
  obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub hsemV)
  subst hnil
  have hdefs : ops.toList.filter Operand.isDef = [] := by
    rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
    · rw [udf_ops hops]; rfl
    · exact trapIf_nodefs hops
  have h1 : VStep R.vc (csemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
    VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
  obtain ⟨n1, c', c'', hq2, hr2, hms, hr3, ht1, hcnt⟩ :=
    forward_lastC (Q := fun u c => QA R u (c.mapW Prod.fst))
      (T := fun u => ∃ m, (Rn m).GoodX u) hSim hRzC hstar h1 hinit (.inl ⟨hq0, hA0⟩) rfl
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
      have hq2'' : QA R (iterN R.step n1 (iterN R.step n0 s))
          (.run ⟨b, .op k _ :: _, _, w.1⟩) := hq2
      have hnr : ∀ us, i ≠ .rets us := by
        intro us h
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
      have hq2' := (qa_op hq2'' hvb hi hnr).1
      have e0 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa) s n0 = 0 :=
        hP0
      have e1 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
          (iterN (ArmStepX (XI.at 0) H fa) n0 s) n1 = nc := by
        rw [← hnc]; exact hcnt
      -- the trace and the count up to the trap's own steps (`n3` of them, no call state)
      have hfin : ∀ n3, (∀ j < n3, R.GoodXN (iterN R.step j (iterN R.step n1 (iterN R.step n0 s)))) →
          callsBefore (ArmStepX (XI.at 0) H fa) fa base s (n0 + n1 + n3) = nc ∧
          (∀ i < n0 + n1 + n3, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
            (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
          (∀ i < n0 + n1 + n3, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
            (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) := by
        intro n3 ht3
        have htrG : ∀ i < n0 + n1 + n3,
            ∃ m, (Rn m).GoodX (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add (T := fun u => ∃ m, (Rn m).GoodX u) (fun j hj => ⟨0, (ht0 j hj).1⟩)
            (trace_add (T := fun u => ∃ m, (Rn m).GoodX u) ht1 fun j hj => ⟨0, (ht3 j hj).1⟩) i
            (by omega)
        have e3 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
            (iterN (ArmStepX (XI.at 0) H fa) (n0 + n1) s) n3 = 0 := by
          rw [iterN_add]; exact countIn_zero_of fun j hj => (ht3 j hj).2
        refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
        · rw [callsBefore_eq_countIn, countIn_add, countIn_add, e0, e1, e3, Nat.zero_add,
            Nat.add_zero]
        · obtain ⟨m, h⟩ := htrG i hi
          exact ⟨h.err, h.prog⟩
        · obtain ⟨m, h⟩ := htrG i hi
          exact ⟨m, h.act⟩
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, hholds⟩
      · simp only [trapCode?, Option.some.injEq] at htc
        subst htc
        obtain ⟨htrap, hstuck⟩ := trap_udf hR hq2' hvb hi
        obtain ⟨hc0, he0, hg0⟩ := hfin 0 fun _ h => absurd h (Nat.not_lt_zero _)
        refine ⟨n0 + n1 + 0, hc0, by rw [show n0 + n1 + 0 = n0 + n1 + 0 + 0 from rfl, hfin0]; exact htrap,
          he0, hg0, fun m => ?_⟩
        rw [show n0 + n1 + 0 + m + 1 = n0 + n1 + 0 + (m + 1) by omega, hfin0]
        exact hstuck m
      · cases hn with
        | halt =>
        obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
        obtain ⟨-, hform2⟩ := csem_halt (csemV_sub hsem3)
        rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds'⟩
        · cases e
        · cases e
          simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨n3, htrap, ht3, hstuck⟩ := trap_trapIfN hR hq2' hvb hi hops' hholds'
          obtain ⟨hc0, he0, hg0⟩ := hfin n3 ht3
          refine ⟨n0 + n1 + n3, hc0, by rw [← Nat.add_zero (n0 + n1 + n3), hfin0]; exact htrap, he0,
            hg0, fun m => ?_⟩
          rw [show n0 + n1 + n3 + m + 1 = n0 + n1 + 0 + (n3 + m + 1) by omega, hfin0]
          exact hstuck m

private theorem valueSemV_haltIXT {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {X : ExtSem} {i : MInst} {us outs : List CV}
    {w w' : Arm.ArmState} (h : valueSemV gv F ctx X i us w = some (outs, w', .halt)) :
    csemV gv F ctx X i us w = some (outs, w', .halt) := by
  by_cases hp : specForm i = true
  · have hs : mspec ctx.slotBase i us w = some (outs, w', .halt) := by
      simpa [valueSemV, hp] using h
    have := mspec_spec_next hp hs
    cases this
  · simpa [valueSemV, hp] using h

/-- **`regLevelCorrect_world_atCSNXT` for the value semantics** (cleanup path). -/
theorem regLevelCorrect_world_value_atCSNXT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    ∀ c nc, VTrapFromW vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩ c
        (fun w => w.2 = nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XI.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
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
  have hfin0 : ∀ n1 n2 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun c nc htr => ?_⟩
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc, hnc⟩ := htr
  obtain ⟨hsemV, -⟩ := ISem.counted_some hsem
  obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub (valueSemV_haltIXT hsemV))
  subst hnil
  have hdefs : ops.toList.filter Operand.isDef = [] := by
    rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
    · rw [udf_ops hops]; rfl
    · exact trapIf_nodefs hops
  have h1 : VStep R.vc (valueSemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
    VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
  obtain ⟨n1, c', c'', hq2, hr2, hms, hr3, ht1, hcnt⟩ :=
    forward_lastC (Q := fun u c => QA R u (c.mapW Prod.fst))
      (T := fun u => ∃ m, (Rn m).GoodX u) hSim hRzC hstar h1 hinit (.inl ⟨hq0, hA0⟩) rfl
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
      have hq2'' : QA R (iterN R.step n1 (iterN R.step n0 s))
          (.run ⟨b, .op k _ :: _, _, w.1⟩) := hq2
      have hnr : ∀ us, i ≠ .rets us := by
        intro us h
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
      have hq2' := (qa_op hq2'' hvb hi hnr).1
      have e0 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa) s n0 = 0 :=
        hP0
      have e1 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
          (iterN (ArmStepX (XI.at 0) H fa) n0 s) n1 = nc := by
        rw [← hnc]; exact hcnt
      have hfin : ∀ n3, (∀ j < n3, R.GoodXN (iterN R.step j (iterN R.step n1 (iterN R.step n0 s)))) →
          callsBefore (ArmStepX (XI.at 0) H fa) fa base s (n0 + n1 + n3) = nc ∧
          (∀ i < n0 + n1 + n3, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
            (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
          (∀ i < n0 + n1 + n3, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
            (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) := by
        intro n3 ht3
        have htrG : ∀ i < n0 + n1 + n3,
            ∃ m, (Rn m).GoodX (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add (T := fun u => ∃ m, (Rn m).GoodX u) (fun j hj => ⟨0, (ht0 j hj).1⟩)
            (trace_add (T := fun u => ∃ m, (Rn m).GoodX u) ht1 fun j hj => ⟨0, (ht3 j hj).1⟩) i
            (by omega)
        have e3 : countIn (fun u => CallPc fa base (Arm.r .PC u)) (ArmStepX (XI.at 0) H fa)
            (iterN (ArmStepX (XI.at 0) H fa) (n0 + n1) s) n3 = 0 := by
          rw [iterN_add]; exact countIn_zero_of fun j hj => (ht3 j hj).2
        refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
        · rw [callsBefore_eq_countIn, countIn_add, countIn_add, e0, e1, e3, Nat.zero_add,
            Nat.add_zero]
        · obtain ⟨m, h⟩ := htrG i hi
          exact ⟨h.err, h.prog⟩
        · obtain ⟨m, h⟩ := htrG i hi
          exact ⟨m, h.act⟩
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, hholds⟩
      · simp only [trapCode?, Option.some.injEq] at htc
        subst htc
        obtain ⟨htrap, hstuck⟩ := trap_udf hR hq2' hvb hi
        obtain ⟨hc0, he0, hg0⟩ := hfin 0 fun _ h => absurd h (Nat.not_lt_zero _)
        refine ⟨n0 + n1 + 0, hc0, by rw [show n0 + n1 + 0 = n0 + n1 + 0 + 0 from rfl, hfin0]; exact htrap,
          he0, hg0, fun m => ?_⟩
        rw [show n0 + n1 + 0 + m + 1 = n0 + n1 + 0 + (m + 1) by omega, hfin0]
        exact hstuck m
      · cases hn with
        | halt =>
        obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
        obtain ⟨-, hform2⟩ := csem_halt (csemV_sub (valueSemV_haltIXT hsem3))
        rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds'⟩
        · cases e
        · cases e
          simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨n3, htrap, ht3, hstuck⟩ := trap_trapIfN hR hq2' hvb hi hops' hholds'
          obtain ⟨hc0, he0, hg0⟩ := hfin n3 ht3
          refine ⟨n0 + n1 + n3, hc0, by rw [← Nat.add_zero (n0 + n1 + n3), hfin0]; exact htrap, he0,
            hg0, fun m => ?_⟩
          rw [show n0 + n1 + n3 + m + 1 = n0 + n1 + 0 + (n3 + m + 1) by omega, hfin0]
          exact hstuck m

/-- **`regLevelCorrect_worldCSNX`'s trap clause with the call count and the per-state trace.** -/
theorem regLevelCorrect_worldCSNXT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    ∀ c nc, VTrapFromW vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c
        (fun w => w.2 = nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atCSNXT hat (entryOk_of_le hle) halloc hemit hlayout hcov
    hent hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- **`regLevelCorrect_worldPRSNX`'s trap clause with the call count and the per-state trace.** -/
theorem regLevelCorrect_worldPRSNXT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    ∀ c nc, VTrapFromW vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c
        (fun w => w.2 = nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None :=
  regLevelCorrect_worldCSNXT hcheck halloc hemit hlayout hcov hent hres hG
    (fun n => (hC n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n => (hCT h n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hTls hbe ρ₀

/-- **`regLevelCorrect_world_value_worldCSNX`'s trap clause with the call count and the
per-state trace.** -/
theorem regLevelCorrect_world_value_worldCSNXT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    ∀ c nc, VTrapFromW vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c
        (fun w => w.2 = nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_value_atCSNXT hat (entryOk_of_le hle) halloc hemit hlayout
    hcov hent hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- **`regLevelCorrect_world_value_worldPRSNX`'s trap clause with the call count and the
per-state trace.** -/
theorem regLevelCorrect_world_value_worldPRSNXT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    ∀ c nc, VTrapFromW vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c
        (fun w => w.2 = nc) →
      ∃ n, callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc ∧
        TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ i < n, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
        (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G gv
          (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None :=
  regLevelCorrect_world_value_worldCSNXT hcheck halloc hemit hlayout hcov hent hres hG
    (fun n => (hC n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n => (hCT h n).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hTls hbe ρ₀

end Backend.Proof
