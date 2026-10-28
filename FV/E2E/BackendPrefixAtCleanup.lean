import FV.E2E.BackendPrefixAt
import FV.E2E.WorldUnwindGot
import FV.E2E.IselSimIPrefixSkip

/-!
# The counted pipeline at call `N` itself, cleanup path and either artifact (SEM1 #537, #680 (3))

`BackendPrefixAt` for `CompiledCleanup` (the compile path of `Link.DeadCleanup`) and for
`CompiledEither` (the artifact `LinkSys.Ok.compiled` gives):

* `regLevel_value_prefixCG`, `regLevel_value_prefixPRSG`: `regLevel_value_prefixC/PRS` with the
  trace (`OnCallG`, `regLevel_prefix_coreG`);
* `iselSim_prefixWI_next_cleanup`: the counted `valueSemI` run passes the call of a calling state
  of count `n` of a returning run (counter `n + 1`);
* **`backend_prefix_cleanupPRI_at`**, **`prefix_related_cleanupPRI_at`**: calls `j ≤ N`;
* **`prefix_relatedPRI_atE`**: `prefix_related*PRI_at` for `CompiledEither`.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver Backend.DeadCleanup

/-- **`regLevel_value_prefixC` with the trace.** -/
theorem regLevel_value_prefixCG {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
    (sem := fun n => valueSemV R.gv R.F R.ctx (XN.at n))
    (fun n => ((realizes_value_allC_sp (hRn n) (hC' n) (fun h => hCT' h n)
      (fun h => tlsOk_upTo (hTls h n)) hcov).mono_T
      (T' := R.Good) fun _ h => h.good).congr_Q fun u c =>
        (RL.QA_withX (Rn n) (XN.at 0) (RL.sP_withX (hRn n) hent (XN.at 0)) u c).symm) ρsel hsel
  exact ⟨m₀, fun b k ρ w vb i hstar hvb hi hcall ops hops =>
    h b k ρ w N vb i (vstar_upTo_value hstar (Nat.le_refl _)) hvb hi hcall ops hops⟩

/-- **`regLevel_value_prefixPRS` with the trace.** -/
theorem regLevel_value_prefixPRSG {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
          (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
            spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) N u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevel_value_prefixCG hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG (fun n hn => (hC n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n hn => (hCT h n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hpc hTls hbe
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The counted `valueSemI` run passes the call of a calling state of a returning run**
(`iselSim_prefixWI_next`, cleanup path). -/
theorem iselSim_prefixWI_next_cleanup {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs)
    {fuel : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned v m) :
    ∀ t n, ReachN env p cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep vc (valueSemI F ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, n + 1)⟩) := by
  intro t n hr hcn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW_cleanup hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _)
      (xCallsIndOk_none _ _ _ _) hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW_cleanup hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2
      hsym hslot
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hPr := probeOf_valueSem F ⟨fa.k, af.slotBase⟩ XI
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_step (Hb 0)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_valueSem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  obtain ⟨b, k', ρ, w, hst, hmt⟩ :=
    sim_prefix_call (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc hm hr hcn
  have hpre := (vstar_mapW (counted_probe_proj hPr 0) hstar).trans hst
  obtain ⟨fuel', hrun'⟩ := runLoop_returned_reachN hrun hr
  obtain ⟨t', fuel'', hs', hrun''⟩ := next_of_returned hrun' (step_ne_done_of_callNum hcn)
  cases hbt : t.frame.body with
  | cons st rest =>
    have hcl : st.inst.isCallLike = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hmt
    have hst : st ∈ B.body := by
      rw [hbd] at hbt
      exact List.mem_of_mem_drop (hbt ▸ List.mem_cons_self)
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun sig callee args hi => hP.indirect t st rest sig callee args hr.reach hbt hi
        ⟨B, hBmem, hst⟩
    obtain ⟨S1, -⟩ := stmt_stepG_call (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) hseg hmt hbt hcl hind
    obtain ⟨b', k'', ρ', w', hst', -⟩ := S1 t' hs'
    exact ⟨b', k'', ρ', w', hpre.trans hst'⟩
  | nil =>
    have hty : t.frame.term.isTry = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    obtain ⟨B, j, hB, hterm, -⟩ := hmt.2.2.2.2
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    obtain ⟨et, hT⟩ : ∃ et, IsTryWith t.frame.term et := by
      cases ht : t.frame.term with
      | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
      | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
      | _ => rw [ht] at hty; cases hty
    have hind : ∀ callee args, t.frame.term = .tryCallIndirect callee args et → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun callee args ht => hP.tryIndirect t callee args et hr.reach hbt ht
        ⟨B, hBmem, hterm.symm.trans ht⟩
    obtain ⟨-, Tnx⟩ := term_step_tryG (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) htc hmt hbt hT hind
    have hstep : Clif.step (env.only (Clif.Invoked env p t)) p t = Clif.step env p t :=
      Clif.step_only fun _ _ _ h => h
    obtain ⟨-, -, hnd, N3⟩ := Tnx t' (hstep.trans hs')
    have hstep' : Clif.step (env.only (Clif.Invoked env p t)) p t' = Clif.step env p t' := by
      apply Clif.step_only
      intro _ _ _ ⟨_, hI⟩
      obtain ⟨⟨hb', -⟩, -⟩ := Tnx t' (hstep.trans hs')
      obtain ⟨bc, hj⟩ := (Tnx t' (hstep.trans hs')).1.2
      simp [hb', hj] at hI
    obtain ⟨t'', -, hs'', -⟩ := next_of_returned hrun'' fun v m h => hnd v m (hstep'.trans h)
    obtain ⟨b', k'', ρ', w', hst2, -⟩ := N3 t'' (hstep'.trans hs'')
    exact ⟨b', k'', ρ', w', hpre.trans hst2⟩

/-- **`iselSim_prefixWI_next_cleanup` for the code after the skip of unused instructions**
(`skipStage f vc`, which the cleanup stage prunes and prepares). -/
theorem iselSim_prefixWI_next_cleanup_stage {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs)
    {fuel : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned v m) :
    ∀ t n, ReachN env p cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI))
        (.run ⟨0, 0, ρ₀, (w₀, 0)⟩) (.run ⟨b, k, ρ, (w, n + 1)⟩) := by
  intro t n hr hcn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  rcases hsk with heq | hK
  · rw [heq]
    exact iselSim_prefixWI_next_cleanup hsub hc hone htc hX hsym hslot ρ₀ hce hrel hargs htr hrun
      t n hr hcn
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW_cleanup hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _)
      (xCallsIndOk_none _ _ _ _) hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW_cleanup hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2
      hsym hslot
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hPr := probeOf_valueSem F ⟨fa.k, af.slotBase⟩ XI
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_stepP (Hb 0)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_valueSem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  obtain ⟨⟨b1, k1, ρ1, w1⟩, hsK, hmK⟩ := entry_matchK hK hB0 hbody hstar hm
  obtain ⟨b, k', ρ, w, hst, hmt⟩ :=
    sim_prefix_callK hK (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc hmK
      hr hcn
  have hpre := (vstar_mapW (counted_probe_proj hPr 0) hsK).trans hst
  obtain ⟨vsF, -, hMF⟩ := id hmt
  obtain ⟨fuel', hrun'⟩ := runLoop_returned_reachN hrun hr
  obtain ⟨t', fuel'', hs', hrun''⟩ := next_of_returned hrun' (step_ne_done_of_callNum hcn)
  cases hbt : t.frame.body with
  | cons st rest =>
    have hcl : st.inst.isCallLike = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
    have hst : st ∈ B.body := by
      rw [hbd] at hbt
      exact List.mem_of_mem_drop (hbt ▸ List.mem_cons_self)
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun sig callee args hi => hP.indirect t st rest sig callee args hr.reach hbt hi
        ⟨B, hBmem, hst⟩
    obtain ⟨S1, -⟩ := stmt_stepG_callK hK (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) hseg hmt hbt hcl hind
    obtain ⟨b', k'', ρ', w', hst', -⟩ := S1 t' hs'
    exact ⟨b', k'', ρ', w', hpre.trans hst'⟩
  | nil =>
    have hty : t.frame.term.isTry = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    obtain ⟨et, hT⟩ : ∃ et, IsTryWith t.frame.term et := by
      cases ht : t.frame.term with
      | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
      | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
      | _ => rw [ht] at hty; cases hty
    have hind : ∀ callee args, t.frame.term = .tryCallIndirect callee args et → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun callee args ht => hP.tryIndirect t callee args et hr.reach hbt ht
        ⟨B, hBmem, hterm.symm.trans ht⟩
    obtain ⟨-, Tnx⟩ := term_step_tryGK hK (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) htc hmt hbt hT hind
    have hstep : Clif.step (env.only (Clif.Invoked env p t)) p t = Clif.step env p t :=
      Clif.step_only fun _ _ _ h => h
    obtain ⟨-, -, hnd, N3⟩ := Tnx t' (hstep.trans hs')
    have hstep' : Clif.step (env.only (Clif.Invoked env p t)) p t' = Clif.step env p t' := by
      apply Clif.step_only
      intro _ _ _ ⟨_, hI⟩
      obtain ⟨⟨hb', -⟩, -⟩ := Tnx t' (hstep.trans hs')
      obtain ⟨bc, hj⟩ := (Tnx t' (hstep.trans hs')).1.2
      simp [hb', hj] at hI
    obtain ⟨t'', -, hs'', -⟩ := next_of_returned hrun'' fun v m h => hnd v m (hstep'.trans h)
    obtain ⟨b', k'', ρ', w', hst2, -⟩ := N3 t'' (hstep'.trans hs'')
    exact ⟨b', k'', ρ', w', hpre.trans hst2⟩


/-- **The counted pipeline at call `N` itself, cleanup path** (`backend_prefix_cleanupPRI` for
`j ≤ N`, for a calling state of count `N` of a returning run). -/
theorem backend_prefix_cleanupPRI_at {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar⟩ :=
    iselSim_prefixWI_next_cleanup_stage hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs
      htr hrun
      t N hr hcn
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar (Nat.zero_le _) (by simp only [vctr]; omega)
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  have hsemC : csem F ⟨fa.k, af.slotBase⟩ (XI.at j) i
      ((ops.toList.filter Operand.isUse).map (ρ1 ·.vreg)) w1 = some r := by
    rw [← valueSem_callLike hci]; exact hsem
  obtain ⟨r', hr'⟩ := csem_call_some hci hsemC
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
  obtain ⟨hs4, hinv4⟩ := gotInvI_star_value
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hs3
  have hci3 := sameInst_callLike hsame hci
  have hops3 : i3.operands = .ok ops := by rw [(sameInst_factsW hds hsame).1, hops]
  have hM := regLevel_value_prefixPRSG hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨u, hon, hsp, hsite⟩ := hM b3 k2 a2 w1 vb3 i3 hs4 hvb3 hi3 ⟨info, hci3⟩ ops hops3
  have hgd := gotGuard_of_inv hinv4 hvb3 hi3 hops3 info hci3
  refine ⟨u, i3, info, _, w1, r', hon, hsp, hsite, hci3, ⟨b3, vb3, k2, hvb3, ?_⟩, hgd, ?_⟩
  · rcases hci3 with rfl | ⟨ti, rfl⟩
    · exact .inl hi3
    · exact .inr ⟨ti, hi3⟩
  have hu2' : (ops.toList.filter Operand.isUse).map (a2 ·.vreg) =
      (ops.toList.filter Operand.isUse).map (ρ1 ·.vreg) := hu2.symm
  rw [hu2']; exact hr'

/-- **The machine's calls up to call `N` itself are the CLIF run's, cleanup path.** -/
theorem prefix_related_cleanupPRI_at {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
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
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx⟩ :=
    backend_prefix_cleanupPRI_at (XI := XI.relOnly (RelatedN env p cs (f.externs.map (·.2))
      (indSigs f) (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym))
      hsub hc hone htc hcov (fun s n hs => xCalls_relOnly hnrc hs (hX s n hs)) hsym hslot hcs hrel
      hargs htr hrun (he.relOnly _) hr hcn j hj
  obtain ⟨hq, hx'⟩ := relOnly_call_some hx
  exact ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx', hq⟩

/-- **`backend_prefixPRI_at` with the call site**: the VCode call of the machine's call `j` is a
call site of `vcp`. -/
theorem backend_prefixPRI_atS {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
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
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r := by
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
  have hM := regLevel_prefixPRSG hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  obtain ⟨u, hon, hsp, hsite⟩ := hM b1 k1 ρ1 w1 vb i hs1 hvb hi ⟨info, hci⟩ ops hops
  obtain ⟨r', hr'⟩ := csem_call_some hci (csemV_sub hsem)
  have hgd : gotGuard (GotV vcp) (XI.at j) info ((ops.toList.filter Operand.isUse).map (ρ1 ·.vreg)) := by
    rcases hci with rfl | ⟨ti, rfl⟩
    · exact csemV_guard hsem
    · exact csemV_guard_try hsem
  refine ⟨u, i, info, _, w1, r', hon, hsp, hsite, hci, ⟨b1, vb, k1, hvb, ?_⟩, hgd, hr'⟩
  rcases hci with rfl | ⟨ti, rfl⟩
  · exact .inl hi
  · exact .inr ⟨ti, hi⟩

/-- **`prefix_relatedPRI_at` with the call site.** -/
theorem prefix_relatedPRI_atS {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx⟩ :=
    backend_prefixPRI_atS (XI := XI.relOnly (RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym))
      hsub hc hone htc hcov (fun s n hs => xCalls_relOnly hnrc hs (hX s n hs)) hsym hslot hcs hrel
      hargs htr hrun (he.relOnly _) hr hcn j hj
  obtain ⟨hq, hx'⟩ := relOnly_call_some hx
  exact ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx', hq⟩

/-- **The machine's calls up to call `N` itself are the CLIF run's, either artifact.** -/
theorem prefix_relatedPRI_atE {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  cases hc with
  | legacy hc =>
    exact prefix_relatedPRI_atS hsub hc hone htc hcov hnrc hX hsym hslot hcs hrel hargs htr hrun he
      hr hcn
  | cleanup hc =>
    exact prefix_related_cleanupPRI_at hsub hc hone htc hcov hnrc hX hsym hslot hcs hrel hargs htr
      hrun he hr hcn

end E2E
