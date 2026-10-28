import FV.E2E.BackendPrefixAtCleanup
import FV.E2E.RegLevelCorrectPRSNG
import FV.E2E.LinkArmInvokedStep

/-!
# The error-free trace up to a call (SEM1 #537, #680 (3), #700)

The prefix theorems (`regLevel_prefix_coreG` … `prefix_relatedPRI_atE`) give the trace `Good` up
to the machine's call-`j` state. The prefix-closed table `TableOfE` (#700) speaks only of run
prefixes without an error, so stage 2 also needs that the states before the call have no error and
the activation's program: `RL.GoodE` (`RegLevelCorrectPRSNG`), realised by the same
`realizes_allC_sp` (`mono_T` to `GoodE` instead of `Good`). Same proofs:

* `regLevel_prefix_coreGE`, `regLevel_prefixCGE`, `regLevel_prefixPRSGE`,
  `regLevel_value_prefixCGE`, `regLevel_value_prefixPRSGE`;
* `backend_prefixPRI_atSGE`, `backend_prefix_cleanupPRI_atGE`, `backend_prefixPRI_atEGE` (either
  artifact): the machine's call-`j` state with the `GoodE` trace;
* **`prefix_relatedPRI_atEG`**: `prefix_relatedPRI_atE` whose trace is also `GoodE` (the call-`j`
  state of both is the same step, `callIdx_unique`).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver Backend.DeadCleanup

/-- **`regLevel_prefix_coreG` with the error-free trace** (`GoodE`). -/
theorem regLevel_prefix_coreGE {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {sem : Nat → ISem CV Arm.ArmState}
    (hreal : ∀ n, RealizesCP R.vc R.rf (sem n) ckeep R.step (QA R) R.GoodE
      R.CallSt (OnCall R.step R.fa R.base R.s0 n))
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV, ∀ b k ρ w N vb i,
      Star (VStep R.vc (ISem.counted sem)) (.run ⟨0, 0, ρsel m₀, (w₀, 0)⟩) (.run ⟨b, k, ρ, (w, N)⟩) →
      R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      (∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ ops, i.operands = .ok ops →
      ∃ u, OnCallG R.step R.fa R.base R.s0 R.GoodE N u ∧ spOf u = R.spB ∧
        CallSiteAt R.F R.K R.G R.s0 R.fa R.base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_initN hR hent hbe
  let m₀ := locVal R.fr (iterN R.step n0 R.s0)
  have hSim := isSimulation_match (sem := ISem.counted sem) (keep := ckeep) hcheck
    (fun r => m₀ (.reg r))
  have hinit := match_init (W := Arm.ArmState × Nat) hcheck m₀ (ρsel m₀) (w₀, 0) (hsel _)
  have hP0 : countIn R.CallSt R.step R.s0 n0 = 0 := countIn_zero_of fun i hi => (ht0 i hi).2
  have hRp := RealizesCP.countedRun (vc := R.vc) (rf := R.rf) (keep := ckeep) (sem := sem)
    (Q := fun u c => QA R u c) (T := R.GoodE) (C := R.CallSt)
    (P := fun n u => OnCall R.step R.fa R.base R.s0 n u) (s0 := iterN R.step n0 R.s0) hreal
    (onCall_of_run hP0)
  refine ⟨m₀, fun b k ρ w N vb i hstar hvb hi hcall ops hops => ?_⟩
  obtain ⟨n1, c1, hz1, hr1, ht1⟩ :=
    forward hSim hRp (s := (iterN R.step n0 R.s0, 0))
      (show Star _ (VConf.init (ρsel m₀) (w₀, 0)) _ from hstar) hinit
      ⟨.inl ⟨hq0, hA0⟩, rfl, 0, rfl⟩
  cases c1 with
  | ret => exact hr1.elim
  | halt => exact hr1.elim
  | run ms =>
  obtain ⟨b1, its1, m1, w1⟩ := ms
  obtain ⟨n2, al, its', m', hz2, hm2, ht2⟩ := match_to_opT (vs := ⟨b, k, ρ, (w, N)⟩) hcheck
    hRp its1 b1 m1 w1 _ hr1 hz1 hvb hi
  obtain ⟨hb1, hw1, -⟩ := id hm2
  simp only at hb1 hw1
  subst hb1 hw1
  rw [← iterN_add, iterN_stepC, Nat.zero_add] at hz2
  obtain ⟨hqa, hk2, -⟩ := hz2
  simp only [MConf.world] at hk2
  have htr : ∀ j < n0 + (n1 + n2), R.GoodE (iterN R.step j R.s0) := by
    refine trace_add (fun j hj => ⟨(ht0 j hj).1.good, (ht0 j hj).1.err, (ht0 j hj).1.prog⟩)
      (trace_add (fun j hj => ?_) ?_)
    · have := ht1 j hj
      rw [iterN_stepC] at this
      exact this
    · intro j hj
      have := ht2 j hj
      rw [iterN_stepC, iterN_stepC, ← iterN_add] at this
      rw [← iterN_add]
      exact this
  refine ⟨iterN R.step (n1 + n2) (iterN R.step n0 R.s0), ?_, ?_⟩
  · refine ⟨n0 + (n1 + n2), ?_, ?_, fun j hj => by rw [runX_eq]; exact htr j hj⟩
    · rw [runX_eq, iterN_add]
    · rw [callsBefore_eq_countIn, countIn_add]
      show countIn R.CallSt R.step R.s0 n0 + countIn R.CallSt R.step (iterN R.step n0 R.s0) (n1 + n2) = N
      rw [hP0, hk2]
      omega
  · obtain ⟨-, huse⟩ := match_op_uses hcheck hm2 hvb hi hops
    have hq'' := hqa
    simp only [MConf.mapW] at hq''
    have hnr : ∀ us, i ≠ .rets us := by
      rintro us rfl; obtain ⟨info, h | ⟨ti, h⟩⟩ := hcall <;> cases h
    have hq' := (qa_op hq'' hvb hi hnr).1
    obtain ⟨info, hci⟩ := hcall
    have hcpc : ∀ regs i', al = regs.map Loc.reg → i.assign regs = .ok i' →
        CallAt R.fa R.base (Arm.r .PC (iterN R.step (n1 + n2) (iterN R.step n0 R.s0))) i' := by
      rcases hci with rfl | ⟨ti, rfl⟩
      · exact callAt_of_q hq' hvb hi call_hcall
      · exact callAt_of_q hq' hvb hi tryCall_hcall
    obtain ⟨j0, vb0, items0, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr',
      hdrop, hpc', hst⟩ := hq'
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
    obtain ⟨regs, i0, i', rfl, hi0, hasg, -⟩ := itemCode_op hc1
    rw [hi] at hi0; cases hi0
    obtain ⟨cc', wh, i2', ops2, hi2', hops2, hstat, -⟩ := op_checked hchk
    rw [hi] at hi2'; cases hi2'
    rw [hops] at hops2; cases hops2
    have hm : ∀ r, r.allocatable = true →
        m' (.reg r) = regVal (iterN R.step (n1 + n2) (iterN R.step n0 R.s0)) r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    have hK : R.K ≤ (spOf (iterN R.step (n1 + n2) (iterN R.step n0 R.s0))).toNat := by
      rw [hst.sp]; exact RL.K_le hR
    have hF : ∀ a, StackBelow R.K (spOf (iterN R.step (n1 + n2) (iterN R.step n0 R.s0))) a → R.F a :=
      fun a ha => by rw [hst.sp] at ha; exact RL.below_F (R := R) ha
    refine ⟨hst.sp, hK, hF, hst.gkeep, cc', wh, ops, regs, i', hops, hstat, hasg, hcpc regs i' rfl hasg,
      hst.world, hst.align, hst.err, ?_⟩
    rw [← useVals_of_store hstat hm]; exact huse

/-- **`regLevel_prefixCG` with the error-free trace.** -/
theorem regLevel_prefixCGE {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {N : Nat}
    (hC : ∀ n < N, CalleeOkGP (fun u => OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n < N, CalleeTryOkGP (fun u =>
        OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV, ∀ b k ρ w vb i,
      Star (VStep vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρsel m₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, N)⟩) →
      vcp.blocks[b]? = some vb → vb.insts[k]? = some i →
      (∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ ops, i.operands = .ok ops →
      ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
          (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
            spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
            t.program = fb.program base) N u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let XN := XI.upTo N
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XN.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
  have hC' : ∀ n, CalleeOkGP (fun u => OnCall R.step fa base s n u ∧ spOf u = R.spB) R.F K G s
      (CallAt fa base) (XN.at n) H vcp.CallSite gv := fun n => by
    by_cases h : n < N
    · show CalleeOkGP _ _ _ _ _ _ ((XI.upTo N).at n) _ _ _
      rw [XI.upTo_at_lt h]; exact hC n h
    · exact calleeOkGP_upTo_ge (by omega) hpc
  have hCT' : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP
      (fun u => OnCall R.step fa base s n u ∧ spOf u = R.spB) R.F K G s
      (CallAt fa base) (XN.at n) H vcp.TrySite gv := fun ht n => by
    by_cases h : n < N
    · show CalleeTryOkGP _ _ _ _ _ _ ((XI.upTo N).at n) _ _ _
      rw [XI.upTo_at_lt h]; exact hCT ht n h
    · exact calleeTryOkGP_upTo_ge (by omega)
  obtain ⟨m₀, h⟩ := regLevel_prefix_coreGE hR hent hbe hcheck
    (sem := fun n => csemV R.gv R.F R.ctx (XN.at n))
    (fun n => ((realizes_allC_sp (hRn n) (hC' n) (fun h => hCT' h n)
      (fun h => tlsOk_upTo (hTls h n)) hcov).mono_T
      (T' := R.GoodE) fun _ h => ⟨h.good, h.err, h.prog⟩).congr_Q fun u c =>
        (RL.QA_withX (Rn n) (XN.at 0) (RL.sP_withX (hRn n) hent (XN.at 0)) u c).symm) ρsel hsel
  exact ⟨m₀, fun b k ρ w vb i hstar hvb hi hcall ops hops =>
    h b k ρ w N vb i (vstar_upTo hstar (Nat.le_refl _)) hvb hi hcall ops hops⟩

/-- **`regLevel_prefixPRSG` with the error-free trace.** -/
theorem regLevel_prefixPRSGE {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    (hproph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P) {R : Nat → Arm.ArmState}
    (hregp : ProphRegOkM c (ArmStepX (XI.at 0) H fa) fa base s R) {N : Nat}
    (hC : ∀ n < N, CalleeOkGP (fun u => OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n < N,
      CalleeTryOkGP (fun u =>
        OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    ∀ b k ρ w vb i,
      Star (VStep vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, N)⟩) →
      vcp.blocks[b]? = some vb → vb.insts[k]? = some i →
      (∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ ops, i.operands = .ok ops →
      ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
          (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
            spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
            t.program = fb.program base) N u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevel_prefixCGE hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG (fun n hn => (hC n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n hn => (hCT h n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hpc hTls hbe
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- **`regLevel_value_prefixCG` with the error-free trace.** -/
theorem regLevel_value_prefixCGE {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {N : Nat}
    (hC : ∀ n < N, CalleeOkGP (fun u => OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n < N, CalleeTryOkGP (fun u =>
        OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV, ∀ b k ρ w vb i,
      Star (VStep vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρsel m₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, N)⟩) →
      vcp.blocks[b]? = some vb → vb.insts[k]? = some i →
      (∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ ops, i.operands = .ok ops →
      ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
          (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
            spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
            t.program = fb.program base) N u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let XN := XI.upTo N
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XN.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
  have hC' : ∀ n, CalleeOkGP (fun u => OnCall R.step fa base s n u ∧ spOf u = R.spB) R.F K G s
      (CallAt fa base) (XN.at n) H vcp.CallSite gv := fun n => by
    by_cases h : n < N
    · show CalleeOkGP _ _ _ _ _ _ ((XI.upTo N).at n) _ _ _
      rw [XI.upTo_at_lt h]; exact hC n h
    · exact calleeOkGP_upTo_ge (by omega) hpc
  have hCT' : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP
      (fun u => OnCall R.step fa base s n u ∧ spOf u = R.spB) R.F K G s
      (CallAt fa base) (XN.at n) H vcp.TrySite gv := fun ht n => by
    by_cases h : n < N
    · show CalleeTryOkGP _ _ _ _ _ _ ((XI.upTo N).at n) _ _ _
      rw [XI.upTo_at_lt h]; exact hCT ht n h
    · exact calleeTryOkGP_upTo_ge (by omega)
  obtain ⟨m₀, h⟩ := regLevel_prefix_coreGE hR hent hbe hcheck
    (sem := fun n => valueSemV R.gv R.F R.ctx (XN.at n))
    (fun n => ((realizes_value_allC_sp (hRn n) (hC' n) (fun h => hCT' h n)
      (fun h => tlsOk_upTo (hTls h n)) hcov).mono_T
      (T' := R.GoodE) fun _ h => ⟨h.good, h.err, h.prog⟩).congr_Q fun u c =>
        (RL.QA_withX (Rn n) (XN.at 0) (RL.sP_withX (hRn n) hent (XN.at 0)) u c).symm) ρsel hsel
  exact ⟨m₀, fun b k ρ w vb i hstar hvb hi hcall ops hops =>
    h b k ρ w N vb i (vstar_upTo_value hstar (Nat.le_refl _)) hvb hi hcall ops hops⟩

/-- **`regLevel_value_prefixPRSG` with the error-free trace.** -/
theorem regLevel_value_prefixPRSGE {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    (hproph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P) {R : Nat → Arm.ArmState}
    (hregp : ProphRegOkM c (ArmStepX (XI.at 0) H fa) fa base s R) {N : Nat}
    (hC : ∀ n < N, CalleeOkGP (fun u => OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n < N,
      CalleeTryOkGP (fun u =>
        OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    ∀ b k ρ w vb i,
      Star (VStep vcp (valueSemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, N)⟩) →
      vcp.blocks[b]? = some vb → vb.insts[k]? = some i →
      (∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ ops, i.operands = .ok ops →
      ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
          (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
            spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
            t.program = fb.program base) N u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevel_value_prefixCGE hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG (fun n hn => (hC n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n hn => (hCT h n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hpc hTls hbe
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`backend_prefixPRI_atS` with the error-free trace** (the machine's call-`j` state only). -/
theorem backend_prefixPRI_atSGE {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned v m) {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      CallPc fa base (Arm.r .PC u) := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar⟩ :=
    iselSim_prefixWI_next hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr hrun t N
      hr hcn
  obtain ⟨b', hstar', -⟩ := prep_prefixW (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk hstar
  obtain ⟨hstar'', -⟩ := gotInvI_star
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hstar'
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar'' (Nat.zero_le _) (by simp only [vctr]; omega)
  have hM := regLevel_prefixPRSGE hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  obtain ⟨u, hon, -, hsite⟩ := hM b1 k1 ρ1 w1 vb i hs1 hvb hi ⟨info, hci⟩ ops hops
  obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hpi, -⟩ := hsite
  exact ⟨u, hon, hpi.callPc⟩

/-- **`backend_prefix_cleanupPRI_at` with the error-free trace** (the machine's call-`j` state
only). -/
theorem backend_prefix_cleanupPRI_atGE {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned v m) {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      CallPc fa base (Arm.r .PC u) := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar⟩ :=
    iselSim_prefixWI_next_cleanup_stage hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs
      htr hrun
      t N hr hcn
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar (Nat.zero_le _) (by simp only [vctr]; omega)
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  have hkeep : pureForm i = false ∧ cmpForm i = false ∧ isJump i = false := by
    rcases hci with rfl | ⟨ti, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨vb2, k2, a2, hs2, hvb2, hi2, hu2⟩ := prune_prefixW (sem := valueSemI F ⟨fa.k, af.slotBase⟩ XI)
    (fun _ _ _ _ _ _ hi hs => counted_pure (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) hi hs)
    (cmpOverwrite_counted fun n => valueSem_cmpOverwrite _ _ _) hs1 hvb hi hops hkeep.1 hkeep.2.1
    hkeep.2.2
  have hds := DriverSemG.counted fun m =>
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG
  obtain ⟨b3, hs3, hins⟩ := prep_prefixW hds hc.prepOk hs2
  obtain ⟨vb3, i3, hvb3, hi3, hsame⟩ := hins vb2 i hvb2 hi2
  obtain ⟨hs4, -⟩ := gotInvI_star_value
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hs3
  have hci3 := sameInst_callLike hsame hci
  have hops3 : i3.operands = .ok ops := by rw [(sameInst_factsW hds hsame).1, hops]
  have hM := regLevel_value_prefixPRSGE hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨u, hon, -, hsite⟩ := hM b3 k2 a2 w1 vb3 i3 hs4 hvb3 hi3 ⟨info, hci3⟩ ops hops3
  obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hpi, -⟩ := hsite
  exact ⟨u, hon, hpi.callPc⟩

/-- **The machine's call-`j` state with the error-free trace, either artifact.** -/
theorem backend_prefixPRI_atEGE {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned v m) {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      CallPc fa base (Arm.r .PC u) := by
  cases hc with
  | legacy hc =>
    exact backend_prefixPRI_atSGE hsub hc hone htc hcov hX hsym hslot hcs hrel hargs htr hrun he
      hr hcn
  | cleanup hc =>
    exact backend_prefix_cleanupPRI_atGE hsub hc hone htc hcov hX hsym hslot hcs hrel hargs htr
      hrun he hr hcn

/-- **`prefix_relatedPRI_atE` with the error-free trace** (module doc). -/
theorem prefix_relatedPRI_atEG {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs)
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned v m) {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, ⟨n₁, hn₁, hcb₁, -⟩, hsp, hsite, hci, hcs', hgd, hx, hq⟩ :=
    prefix_relatedPRI_atE hsub hc hone htc hcov hnrc hX hsym hslot hcs hrel hargs htr hrun he hr hcn
      j hj
  obtain ⟨u', ⟨n₂, hn₂, hcb₂, htr₂⟩, hcp₂⟩ :=
    backend_prefixPRI_atEGE hsub hc hone htc hcov hX hsym hslot hcs hrel hargs htr hrun he hr hcn j hj
  have hcp₁ : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa) n₁ s)) := by
    obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hpi, -⟩ := hsite
    rw [hn₁]; exact hpi.callPc
  have hcp₂' : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa) n₂ s)) := by
    rw [hn₂]; exact hcp₂
  obtain rfl : n₁ = n₂ := callIdx_unique hcp₁ hcp₂' (hcb₁.trans hcb₂.symm)
  exact ⟨u, i, info, uses, w, r, ⟨n₁, hn₁, hcb₁, htr₂⟩, hsp, hsite, hci, hcs', hgd, hx, hq⟩

end E2E
