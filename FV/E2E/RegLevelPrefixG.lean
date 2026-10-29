module

public import FV.E2E.RegLevelPrefixC

@[expose] public section

/-!
# The counted register level up to call `N`, with the run's trace (SEM1 #537, #680 (3) (P1))

`regLevel_prefix_core` gives, for a counted VCode call at counter `N`, a machine state `u` of the
activation's run with `N` call states before it. Stage 2 also needs that `u` precedes the
activation's return (the caller's table `TableOf` speaks only of run prefixes before the return):
every state of the run before `u` is `RL.Good` (no return into the activation's own code but with
the body `sp`), as `regLevelCorrect_world*` show for the states before the return.

* `match_to_opT`: `match_to_op` with the realisation's trace;
* **`regLevel_prefix_coreG`**, **`regLevel_prefixCG`**, **`regLevel_prefixPRSG`**: the prefix
  theorems with the step index of `u` and `Good` at every earlier state (`OnCallG`).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)}
  {sem : ISem V W} {keep : Reg → V → V}

/-- **`match_to_op` with the trace** of the realisation. -/
theorem match_to_opT {a0 : AState} (hc : CheckedAt vc rf c ins a0) {r₀ : Reg → V} {S : Type}
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T) {vb : VBlock} {i : MInst} :
    ∀ (its : List RItem) (b : Nat) (m : Loc → V) (w : W) (vs : VState V W) (s : S),
      Match c ins keep r₀ (.run ⟨b, its, m, w⟩) (.run vs) → Q s (.run ⟨b, its, m, w⟩) →
      vc.blocks[vs.b]? = some vb → vb.insts[vs.k]? = some i →
      ∃ n a its' m', Q (iterN step n s) (.run ⟨b, .op vs.k a :: its', m', w⟩) ∧
        Match c ins keep r₀ (.run ⟨b, .op vs.k a :: its', m', w⟩) (.run vs) ∧
        ∀ j < n, T (iterN step j s)
  | [], b, m, w, vs, s, hm, _, hvb, hi => by
    obtain ⟨hb, -, vb', a, out, hvb', hrun, -⟩ := hm
    rw [hc.vc_eq, hvb] at hvb'; cases hvb'
    obtain ⟨hk, -⟩ := runItems_nil hrun
    rw [hk] at hi
    simp at hi
  | .move src dst :: its, b, m, w, vs, s, hm, hq, hvb, hi => by
    obtain ⟨n1, c'', hs, hq', ht1⟩ := hQ s _ _ hq MStep.move
    cases hs
    obtain ⟨n2, a, its', m', hq2, hm2, ht2⟩ := match_to_opT hc hQ its b _ w vs _
      ((isSimulation_match (sem := sem) hc r₀).move hm) hq' hvb hi
    exact ⟨n1 + n2, a, its', m', by rw [iterN_add]; exact hq2, hm2, trace_add ht1 ht2⟩
  | .op k a :: its, b, m, w, vs, s, hm, hq, _, _ => by
    have hk : vs.k = k := ((isSimulation_match (sem := sem) hc r₀).at_op hm).2.1
    subst hk
    exact ⟨0, a, its, m, hq, hm, fun _ h => absurd h (Nat.not_lt_zero _)⟩

end

/-- **`u` is the state of step `i` of the run of `Mm` from `s`, with `n` call states before
it and every earlier state satisfying `T`.** -/
def OnCallG (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64) (s : Arm.ArmState)
    (T : Arm.ArmState → Prop) (n : Nat) (u : Arm.ArmState) : Prop :=
  ∃ i, E2E.runX Mm i s = u ∧ callsBefore Mm fa base s i = n ∧ ∀ j < i, T (E2E.runX Mm j s)

theorem OnCallG.onCall {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s : Arm.ArmState} {T : Arm.ArmState → Prop} {n : Nat} {u : Arm.ArmState}
    (h : OnCallG Mm fa base s T n u) : OnCall Mm fa base s n u :=
  let ⟨i, h1, h2, _⟩ := h; ⟨i, h1, h2⟩

/-- **`regLevel_prefix_core` with the trace**: the machine state `u` of the counted VCode call is
reached after `i` steps, every earlier state `Good`. -/
theorem regLevel_prefix_coreG {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {sem : Nat → ISem CV Arm.ArmState}
    (hreal : ∀ n, RealizesCP R.vc R.rf (sem n) ckeep R.step (fun s c => Q R s c ∧ AInv R c) R.Good
      R.CallSt (OnCall R.step R.fa R.base R.s0 n))
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV, ∀ b k ρ w N vb i,
      Star (VStep R.vc (ISem.counted sem)) (.run ⟨0, 0, ρsel m₀, (w₀, 0)⟩) (.run ⟨b, k, ρ, (w, N)⟩) →
      R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      (∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ ops, i.operands = .ok ops →
      ∃ u, OnCallG R.step R.fa R.base R.s0 R.Good N u ∧ spOf u = R.spB ∧
        CallSiteAt R.F R.K R.G R.s0 R.fa R.base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_initN hR hent hbe
  let m₀ := locVal R.fr (iterN R.step n0 R.s0)
  have hSim := isSimulation_match (sem := ISem.counted sem) (keep := ckeep) hcheck
    (fun r => m₀ (.reg r))
  have hinit := match_init (W := Arm.ArmState × Nat) hcheck m₀ (ρsel m₀) (w₀, 0) (hsel _)
  have hP0 : countIn R.CallSt R.step R.s0 n0 = 0 := countIn_zero_of fun i hi => (ht0 i hi).2
  have hRp := RealizesCP.countedRun (vc := R.vc) (rf := R.rf) (keep := ckeep) (sem := sem)
    (Q := fun u c => Q R u c ∧ AInv R c) (T := R.Good) (C := R.CallSt)
    (P := fun n u => OnCall R.step R.fa R.base R.s0 n u) (s0 := iterN R.step n0 R.s0) hreal
    (onCall_of_run hP0)
  refine ⟨m₀, fun b k ρ w N vb i hstar hvb hi hcall ops hops => ?_⟩
  obtain ⟨n1, c1, hz1, hr1, ht1⟩ :=
    forward hSim hRp (s := (iterN R.step n0 R.s0, 0))
      (show Star _ (VConf.init (ρsel m₀) (w₀, 0)) _ from hstar) hinit
      ⟨⟨hq0, hA0⟩, rfl, 0, rfl⟩
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
  obtain ⟨⟨hq, -⟩, hk2, -⟩ := hz2
  simp only [MConf.world] at hk2
  have htr : ∀ j < n0 + (n1 + n2), R.Good (iterN R.step j R.s0) := by
    refine trace_add (fun j hj => (ht0 j hj).1.good) (trace_add (fun j hj => ?_) ?_)
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
    have hq' := hq
    simp only [MConf.mapW] at hq'
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

/-- **`regLevel_prefixC` with the trace**: the machine state of the counted VCode call is
reached after a run prefix whose states are no return into `fa`'s code but with the body `sp`. -/
theorem regLevel_prefixCG {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
          (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
            spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) N u ∧
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
  obtain ⟨m₀, h⟩ := regLevel_prefix_coreG hR hent hbe hcheck
    (sem := fun n => csemV R.gv R.F R.ctx (XN.at n))
    (fun n => ((realizes_allC_sp (hRn n) (hC' n) (fun h => hCT' h n)
      (fun h => tlsOk_upTo (hTls h n)) hcov).mono_T
      (T' := R.Good) fun _ h => h.good).congr_Q fun u c =>
        and_congr (RL.Q_withX (Rn n) (XN.at 0) u c).symm Iff.rfl) ρsel hsel
  exact ⟨m₀, fun b k ρ w vb i hstar hvb hi hcall ops hops =>
    h b k ρ w N vb i (vstar_upTo hstar (Nat.le_refl _)) hvb hi hcall ops hops⟩

/-- **`regLevel_prefixPRS` with the trace** (`regLevel_prefixCG` from `checkAlloc`, with the
prophecies). -/
theorem regLevel_prefixPRSG {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
          (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
            spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) N u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevel_prefixCG hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG (fun n hn => (hC n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n hn => (hCT h n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hpc hTls hbe
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof
