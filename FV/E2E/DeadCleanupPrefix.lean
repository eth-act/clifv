import FV.E2E.BackendPrefixI
import FV.E2E.BackendWorldCleanupI
import FV.E2E.IselSimIPrefixSkip
import FV.E2E.DeadCleanupRegLevelPRS

/-!
# The counted pipeline up to call `N`, cleanup path (SEM1 #537, item (d), docs/plans/uninit.md §5.9)

`backend_prefixPRI` for `CompiledCleanup` (the compile path `Link.DeadCleanup` uses): the value
semantics at the register level (`regLevel_value_prefixC`, `regLevel_value_prefixPRS`: the
prefix core `regLevel_prefix_core` on `realizes_value_allC_sp`), the dead-code cleanup on run
prefixes (`prune_prefixW`: a kept instruction reached by the VCode is reached by the cleaned
VCode, with the same operand values and world), and **`backend_prefix_cleanupPRI`**.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver Backend.DeadCleanup

theorem valueSemV_call_congr (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    {i : MInst} (h : i.isCallI = false) :
    valueSemV gv F ctx { X with call := c } i = valueSemV gv F ctx X i := by
  funext uses w
  simp only [valueSemV]
  split
  · rfl
  · exact congrFun (congrFun (csemV_call_congr gv F ctx X c h) uses) w

/-- The counted run of the value semantics to counter `≤ N` is one of `XI.upTo N`. -/
theorem vstar_upTo_value {vc : VCode} {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {XI : ExtSemI} {N : Nat} {v v' : VConf CV (Arm.ArmState × Nat)}
    (h : Star (VStep vc (valueSemVI gv F ctx XI)) v v') (hN : vctr v' ≤ N) :
    Star (VStep vc (valueSemVI gv F ctx (XI.upTo N))) v v' :=
  vstar_counted_upTo (sem := fun n => valueSemV gv F ctx (XI.at n))
    (sem' := fun n => valueSemV gv F ctx ((XI.upTo N).at n))
    (fun j i h => by
      rcases h with h | h
      · show _ = valueSemV gv F ctx ((XI.upTo N).at j) i
        rw [XI.upTo_at_lt h]
      · exact (valueSemV_call_congr gv F ctx (XI.at j) _ h).symm) h hN

/-- **`regLevel_prefixC` for the value semantics.** -/
theorem regLevel_value_prefixC {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
      ∃ u, OnCall (ArmStepX (XI.at 0) H fa) fa base s N u ∧
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
  obtain ⟨m₀, h⟩ := regLevel_prefix_core hR hent hbe hcheck
    (sem := fun n => valueSemV R.gv R.F R.ctx (XN.at n))
    (fun n => ((realizes_value_allC_sp (hRn n) (hC' n) (fun h => hCT' h n)
      (fun h => tlsOk_upTo (hTls h n)) hcov).mono_T
      (T' := R.Good) fun _ h => h.good).congr_Q fun u c =>
        (RL.QA_withX (Rn n) (XN.at 0) (RL.sP_withX (hRn n) hent (XN.at 0)) u c).symm) ρsel hsel
  exact ⟨m₀, fun b k ρ w vb i hstar hvb hi hcall ops hops =>
    h b k ρ w N vb i (vstar_upTo_value hstar (Nat.le_refl _)) hvb hi hcall ops hops⟩

/-- **`regLevel_value_prefixC` from `checkAlloc`, with the prophecies.** -/
theorem regLevel_value_prefixPRS {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
      ∃ u, OnCall (ArmStepX (XI.at 0) H fa) fa base s N u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevel_value_prefixC hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG (fun n hn => (hC n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩)
    (fun h n hn => (hCT h n hn).mono fun _ h => ⟨onCallPR_of hproph hregp h.1, h.2⟩) hpc hTls hbe
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The cleanup on run prefixes**: a kept instruction (not pure, not a comparison, not a jump)
that the VCode reaches from the entry is reached by the cleaned VCode, in the same block and world,
with the same operand values. -/
theorem prune_prefixW {W : Type} {vc : VCode} {sem : ISem CV W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem) {ρ₀ : Nat → CV} {w₀ : W} {b k : Nat} {a : Nat → CV} {w : W}
    {vb : VBlock} {i : MInst} {ops : Array Operand}
    (hs : Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨b, k, a, w⟩))
    (hb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hop : i.operands = .ok ops)
    (hpi : pureForm i = false) (hc : cmpForm i = false) (hj : isJump i = false) :
    ∃ vb' k' a', Star (VStep (prune vc) sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨b, k', a', w⟩) ∧
      (prune vc).blocks[b]? = some vb' ∧ vb'.insts[k']? = some i ∧ vuses ops a = vuses ops a' := by
  unfold prune
  cases h : vc.cfg with
  | error e => exact ⟨vb, k, a, hs, hb, hi, rfl⟩
  | ok p =>
    have hb0 : ∃ vb0, vc.blocks[0]? = some vb0 := by
      cases hs with
      | refl => exact ⟨vb, hb⟩
      | step h _ => cases h with | step he _ _ _ _ _ => exact ⟨_, he⟩
    obtain ⟨vb0, hb0⟩ := hb0
    obtain ⟨c1, hstar', hr⟩ := star_sim hp hcmp (terminated_of_cfg h) (rel_entry hb0 ρ₀ w₀) hs
    obtain ⟨k', a', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop hpi hc hj
    exact ⟨_, k', a', hstar', hb', hi', hu⟩

theorem valueSem_callLike {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti) :
    valueSem F ctx X i = csem F ctx X i := by
  rcases hi with rfl | ⟨ti, rfl⟩ <;> rfl

/-- **The counted pipeline up to call `N`, cleanup path** (`backend_correct_world_cleanupPRI`'s
premises; the machine contracts of the calls `j < N` only): `backend_prefixPRI`'s conclusion for
`CompiledCleanup`. -/
theorem backend_prefix_cleanupPRI {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    (htr : TrapsExplicit env p cs) {N : Nat} {H : ArmHooks} {G : BitVec 64 → Prop}
    {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j < N, ∃ u i info uses w r, OnCall (ArmStepX (XI.at 0) H fa) fa base s j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ (XI.at j).call (callDest info) uses w = some r := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar, -⟩ :=
    iselSim_prefixWI_cleanup_stage hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr t
      N hr hcn
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar (Nat.zero_le _) hj
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
  obtain ⟨hs4, -⟩ := gotInvI_star_value
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hs3
  have hci3 := sameInst_callLike hsame hci
  have hops3 : i3.operands = .ok ops := by rw [(sameInst_factsW hds hsame).1, hops]
  have hM := regLevel_value_prefixPRS hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨u, hon, hsp, hsite⟩ := hM b3 k2 a2 w1 vb3 i3 hs4 hvb3 hi3 ⟨info, hci3⟩ ops hops3
  refine ⟨u, i3, info, _, w1, r', hon, hsp, hsite, hci3, ?_⟩
  have hu2' : (ops.toList.filter Operand.isUse).map (a2 ·.vreg) =
      (ops.toList.filter Operand.isUse).map (ρ1 ·.vreg) := hu2.symm
  rw [hu2']; exact hr'

end E2E
