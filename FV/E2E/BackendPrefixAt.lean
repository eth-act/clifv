import FV.E2E.PrefixRelated
import FV.E2E.RegLevelPrefixG

/-!
# The counted pipeline at call `N` itself (SEM1 #537, #680 (3), `docs/plans/uninit.md` §5.9 (P1))

`backend_prefixPRI` realises every call `j < N` of the counted VCode run by the machine's call-`j`
state, for a CLIF calling state reached after `N` calls. Stage 2 at call `N` needs the call `N`
itself. The VCode run reaches the call instruction of count `N` once the CLIF state of count `N`
makes its call (it then passes the call: the semantics `XI` meets stage 1 everywhere), and the
machine contracts are needed only below `N` (`regLevel_prefixPRS` at counter `N`).

* `step_ne_done_of_callNum`: a calling state does not return;
* `runLoop_returned_reachN`: the run from a reached state of a returning run returns;
* `next_of_returned_call`: a calling state of a returning run steps;
* **`iselSim_prefixWI_next`**: the counted VCode run passes the call of a calling state of
  count `n` of a returning run (it reaches counter `n + 1`);
* **`backend_prefixPRI_at`**: `backend_prefixPRI` for every `j ≤ N` (contracts `n < N`);
* **`prefix_relatedPRI_at`**: `prefix_relatedPRI` for every `j ≤ N`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A calling state does not return.** -/
theorem step_ne_done_of_callNum {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    (hc : callNum s = 1) (v : List Clif.Val) (m : Clif.Mem) : Clif.step env p s ≠ .done v m := by
  intro h
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [Clif.step_try env p s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Clif.ofRes_eq_done h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := Clif.ofRes_eq_done h
    exact absurd h Clif.callCont_ne_done
  · rw [Clif.step_tryInd env p s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Clif.ofRes_eq_done h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := Clif.ofRes_eq_done h
    exact absurd h Clif.indCont_ne_done
  · rw [Clif.step_ind env p s hb hi] at h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := Clif.ofRes_eq_done h
    exact absurd h Clif.indCont_ne_done
  · rw [Opt.step_eq_lift env p s hci] at h
    have hnil : ∀ (hb : s.frame.body = []), False := fun hb => by
      have := hci.2 hb
      simp [callNum, hb, this] at hc
    cases hl : Opt.lstep s.frame s.mem with
    | ret vals => exact hnil (Opt.lstep_ret_inv hl)
    | call ext vals rs rest => rw [hl] at h; exact absurd h Clif.callCont_ne_done
    | tail ext vals => exact hnil (Opt.lstep_tail_inv hl)
    | next fr1 m1 => rw [hl] at h; cases h
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-- **The run from a reached state of a returning run returns.** -/
theorem runLoop_returned_reachN {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {fuel : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned v m) {t : Clif.State} {n : Nat}
    (hr : ReachN env p cs t n) : ∃ fuel', Clif.runLoop env p fuel' t = .returned v m := by
  induction hr with
  | refl => exact ⟨fuel, hrun⟩
  | @snoc s s' k _ hs ih =>
    obtain ⟨f, hf⟩ := ih
    cases f with
    | zero => simp at hf
    | succ f =>
      rw [Clif.runLoop_succ, hs] at hf
      exact ⟨f, hf⟩

/-- **A state of a returning run that does not return steps.** -/
theorem next_of_returned {env : Clif.Env} {p : Clif.Program} {t : Clif.State} {fuel : Nat}
    {v : List Clif.Val} {m : Clif.Mem} (hrun : Clif.runLoop env p fuel t = .returned v m)
    (hnd : ∀ v m, Clif.step env p t ≠ .done v m) :
    ∃ t' fuel', Clif.step env p t = .next t' ∧ Clif.runLoop env p fuel' t' = .returned v m := by
  cases fuel with
  | zero => simp at hrun
  | succ f =>
    rw [Clif.runLoop_succ] at hrun
    cases hs : Clif.step env p t with
    | next t' => rw [hs] at hrun; exact ⟨t', f, rfl, hrun⟩
    | done v' m' => exact absurd hs (hnd v' m')
    | trapped c => rw [hs] at hrun; cases hrun
    | stuck msg => rw [hs] at hrun; cases hrun

/-- **The counted VCode run passes the call of a calling state of a returning run**
(`iselSim_prefixWI`'s premises): it reaches counter `n + 1`. -/
theorem iselSim_prefixWI_next {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
      ∃ b k ρ w, Star (VStep vc (csemI F ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, n + 1)⟩) := by
  intro t n hr hcn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _)
      hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (csem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2 hsym hslot
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
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_step (Hb 0)
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_csem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  obtain ⟨b, k', ρ, w, hst, hmt⟩ :=
    sim_prefix_call (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (semB := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall) (noncallIndep_csem _ _ XI)
      (probeOf_csem _ _ XI) hP Hb Hs hseg htc hm hr hcn
  have hpre := (vstar_mapW (csem_noCall_proj F ⟨fa.k, af.slotBase⟩ XI 0) hstar).trans hst
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
    obtain ⟨S1, -⟩ := stmt_stepG_call (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_csem _ _ XI) (Hs t n hr) hseg hmt hbt hcl hind
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
    obtain ⟨-, Tnx⟩ := term_step_tryG (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_csem _ _ XI) (Hs t n hr) htc hmt hbt hT hind
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

/-- **The counted pipeline at call `N` itself** (`backend_prefixPRI` for `j ≤ N`): for a CLIF
calling state of count `N` of a returning run, every call `j ≤ N` of the counted VCode run is
realised by the machine's call-`j` state, with the machine contracts of the calls `n < N`
only. -/
theorem backend_prefixPRI_at {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
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
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ (XI.at j).call (callDest info) uses w = some r := by
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
  exact ⟨u, i, info, _, w1, r', hon, hsp, hsite, hci, hr'⟩

/-- **The machine's calls up to call `N` itself are the CLIF run's** (`prefix_relatedPRI` for
`j ≤ N`, for a calling state of count `N` of a returning run). -/
theorem prefix_relatedPRI_at {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
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
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hx⟩ :=
    backend_prefixPRI_at (XI := XI.relOnly (RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym))
      hsub hc hone htc hcov (fun s n hs => xCalls_relOnly hnrc hs (hX s n hs)) hsym hslot hcs hrel
      hargs htr hrun (he.relOnly _) hr hcn j hj
  obtain ⟨hq, hx'⟩ := relOnly_call_some hx
  exact ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hx', hq⟩

end E2E
