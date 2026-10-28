import FV.E2E.LinkArmThmPRBRLAll
import FV.E2E.BackendWorldPRGYN
import FV.E2E.LinkArmCountZero

/-!
# `CountPRB` at every depth, and `ThmPRBRL` without it (SEM1 #537, #680 (3), stage 2 glue (5))

**`countPRB_succ`**: under `NeedSlots`, `CountPRB κ (M' + 1)` from `ThmPRBRL κ M'`, `DetPRB κ M'`,
`DetTabPRB κ (M' + 1)` and `RetOkPRB κ (M' + 1)` (the premises of `stage2PRBZS_of`).

For an activation of `g` whose CLIF run returns, and a machine return `n` with the `Good` trace:

* the counted pipeline at the return (`backend_correct_world_pipelinePRGYN`, stage 2 at the
  call sites by `stage2PRBZS_of`) gives a machine return `n'` whose `callsBefore … n'` is the call
  count `k` of the CLIF run up to its returning state `u`; `n' = n` (no return before a return
  with the trace, `noRetAt_of`, both ways);
* the count invariant of `stage2PRBZS_of` up to the return: the caller table's count before step
  `i ≤ n` is `Σ_{j < callsBefore i} advAt j` (each machine call before the return is a CLIF call
  `j < k`, realised by the prefix theorem at call `k - 1`, `prefix_relatedPRI_atE`);
* the returning state's popped entry is advanced by `Σ_{j < k} advAt j`
  (`nextAdv_leave_of_done`, `returned_nextAdv_leave` from a given returning state).

**`thmPRBRL_allC`**: `thmPRBRL_all` without the `CountPRB` premise (`countPRB_succ`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`returned_nextAdv_leave` from a given returning state**: a bare activation reaching `u`
after `k` calls, whose step returns, advances the popped entry's counter by
`Σ_{j<k} advAt … j`. -/
theorem nextAdv_leave_of_done {P q : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {env : Clif.Env} (hk : Clif.EnvAdv env) {cs : Clif.State} (hI : Clif.LInv P cs)
    (hc : cs.callers = []) {pl : Clif.Place} {ini : Clif.SlotInit}
    (hp : cs.mem.place = some pl) (hin : pl.init = some ini) {u : Clif.State} {k : Nat}
    {v : List Clif.Val} {m : Clif.Mem} (hu : ReachN env q.bare cs u k)
    (hd : Clif.step env q.bare u = .done v m) :
    Clif.NextAdv cs.mem.leave m (Clif.sumTo (advAt env q.bare cs) k) := by
  obtain ⟨hIu, -, hN⟩ := nextAdv_reachN hP hk hI hc hp hin hu
  rw [step_done_mem_q hP hIu hd]
  intro pl' ini' hp' hi'
  have hu := hN pl ini hp hin
  simp only [Clif.Mem.leave, hp, Option.some.injEq] at hp'
  subst hp'
  simp only at hi'
  rw [hin, Option.some.injEq] at hi'
  subst hi'
  simp only [Clif.Mem.leave, Clif.Mem.free, hu]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **An activation's return is a `RetAt`.** -/
theorem retAt_of_actRet {M : Nat} {g : Clif.Function} {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (hME : L.MachEntry κ M g F G ra s w₀) {us : List (Reg × Reg)}
    {outs : List CV} {wf t : Arm.ArmState} (h : ActRet ra F G us outs wf s t) : L.RetAt g s t :=
  ⟨h.ret.pc.trans hME.abi.lr.symm, h.ret.err,
    h.prog.trans (by first | exact hME.abi.program | exact hME.abi.program.symm), h.ret.sp⟩

/-- **Two returns with the trace are the same step** (`noRetAt_of` both ways). -/
theorem actRet_unique (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (hME : L.MachEntry κ M g F G ra s w₀) (hra : RaOk (L.A g) (ra - 4))
    {us us' : List (Reg × Reg)} {outs outs' : List CV} {wf wf' : Arm.ArmState} {n n' : Nat}
    (h : ActRet ra F G us outs wf s (runX (L.mach M g) n s))
    (ht : PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n)
    (h' : ActRet ra F G us' outs' wf' s (runX (L.mach M g) n' s))
    (ht' : PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n') : n = n' := by
  rcases Nat.lt_trichotomy n n' with hl | he | hl
  · exact absurd (L.retAt_of_actRet hME h) (L.noRetAt_of hL hg hME hra ht' h'.ret.err n hl)
  · exact he
  · exact absurd (L.retAt_of_actRet hME h') (L.noRetAt_of hL hg hME hra ht h.ret.err n' hl)

/-- **`CountPRB` one level up** (module doc). -/
theorem countPRB_succ (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRL κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRB κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.CountPRB κ (M' + 1) := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun us' outs' wf' n e hAR
    hPT hte _
  have hZS := L.stage2PRBZS_of hL hκ hN ih hdet hdt hret g hg F vals cs w₀ fuel rvals cm' ini G ra
    s hWE hME hra htab hrun
  have hc := hL.compiled g hg
  have hgf := hL.free g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB (M' + 1) g (spv w₀)) L.P.bare fuel cs =
      .returned rvals cm' := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hrun
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hgf
  have hnrc : NoRetCall (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs :=
    noRetCall_of_linv hPf (fun _ h => by simp at h) hI
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M' + 1) he.body.sp
  have hX := hX_guardRXRI (Γ := ⟨F, L.syms, (L.A g).af.slotBase,
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩) (f := g) (c := spv w₀)
    (L.XPBTI κ (M' + 1) g F (L.BP (M' + 1) g s) (L.RP (M' + 1) g s)) hnrc
    (hret g hg F vals cs w₀ ini hWE)
  have hk := L.envAdv_envOfB (L.crun_adv hL hN (M' + 1)) g (spv w₀)
  obtain ⟨sps0, hp0⟩ := hWE.place hN
  have ih' : 0 < M' + 1 → L.ThmPRBRL κ (M' + 1 - 1) := fun _ => by
    rw [Nat.add_sub_cancel]; exact ih
  have hdet' : 0 < M' + 1 → L.DetPRB κ (M' + 1 - 1) := fun _ => by
    rw [Nat.add_sub_cancel]; exact hdet
  have hpc := (L.calleeOkPRBRL hL hκ ih' hdet' hg he (hQ 0)).pc
  -- the counted pipeline at the return
  have hpip := backend_correct_world_pipelinePRGYN (hL.subset g hg) hc
    (XI := L.XPBTI κ (M' + 1) g F (L.BP (M' + 1) g s) (L.RP (M' + 1) g s)) (syms := L.syms)
    (env := L.envOfB (M' + 1) g (spv w₀)) (K := κ (M' + 1) g) (F := F) (c := spv w₀)
    (hL.covered g hg) hnrc (hret g hg F vals cs w₀ ini hWE) (fun n b hn => hL.symOk n b hn) rfl
    hWE.clif hWE.rel hWE.args (trapsExplicit_of_returned hrun') fuel
  obtain ⟨_us, _outs, _wf, -, -, -, -, -, hall⟩ := hpip.1 rvals cm' hrun'
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ (M' + 1) g) F G
      (L.XPBTGY κ (M' + 1) g F (L.BP (M' + 1) g s) (L.RP (M' + 1) g s)
        (L.envOfB (M' + 1) g (spv w₀)) cs (spv w₀))
      (L.hooks (M' + 1)) (L.A g).base ra (κ (M' + 1) g) (spv w₀) (L.BP (M' + 1) g s)
      (L.RP (M' + 1) g s) s w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun k => L.calleeOkXPBTGZS hL hκ ih' hdet' hg he (hQ k) (hZS k),
      fun _ k => L.calleeTryOkXPBTGZS hL hκ ih' hdet' hg he (hQ k) (hZS k),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ (M' + 1) g)
        exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  obtain ⟨n2, hret2, htr2, u, hu, hd⟩ := hall (L.hooks (M' + 1)) G (L.A g).base ra
    (κ (M' + 1) g) (spv w₀) (L.BP (M' + 1) g s) (L.RP (M' + 1) g s) s hAE
  obtain rfl : n = n2 := L.actRet_unique hL hg he hra hAR hPT hret2 htr2
  change ReachN _ _ cs u (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s n) at hu
  -- the count invariant up to the return
  have hcntAll : ∀ i ≤ n, ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) := by
    intro i
    induction i with
    | zero =>
      intro _ e he0
      have := L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ he0 (L.tabUpTo_zero (M' + 1) g s ini.bytes ini.next)
      rw [this]; rfl
    | succ i ihi =>
      intro hle
      have hlt : i < n := by omega
      have hcnt := ihi (by omega)
      by_cases hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s))
      · have hjn : callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i <
            callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s n := callsBefore_lt hcp hlt
        -- the prefix theorem at the last CLIF call
        obtain ⟨tl, -, hrtl, hcnl, -, -⟩ := reachN_call_at hu
          (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s n - 1) (by omega)
        have hAE' : ActEntryPRN (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
            (κ (M' + 1) g) F G
            (L.XPBTGY κ (M' + 1) g F (L.BP (M' + 1) g s) (L.RP (M' + 1) g s)
              (L.envOfB (M' + 1) g (spv w₀)) cs (spv w₀))
            (L.hooks (M' + 1)) (L.A g).base ra (κ (M' + 1) g) (spv w₀) (L.BP (M' + 1) g s)
            (L.RP (M' + 1) g s) s w₀
            (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s n - 1) :=
          ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
            fun k _ => L.calleeOkXPBTGZS hL hκ ih' hdet' hg he (hQ k) (hZS k),
            fun _ k _ => L.calleeTryOkXPBTGZS hL hκ ih' hdet' hg he (hQ k) (hZS k),
            hpc,
            fun ht _ => by
              have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ (M' + 1) g)
              exact ⟨h0.pc, h0.seq, h0.flags⟩,
            he.body⟩
        have hpre := prefix_relatedPRI_atE (hL.subset g hg) hc (instCallsOne_all g)
          (tryCallsOne_all g) (hL.covered g hg) hnrc hX (fun n b hn => hL.symOk n b hn) rfl hWE.clif
          hWE.rel hWE.args (trapsExplicit_of_returned hrun') hrun' hAE' hrtl hcnl
        obtain ⟨uj, insj, infoj, usesj, wj, rj, ⟨ij, hij, hcbj, htrj⟩, hspj, hsitej, hcij, hCSj,
          hgdj, -, hrelj⟩ := hpre (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)
            (by omega)
        obtain ⟨-, -, hGuj, ccj, whj, opsj, regsj, i'j, hopsj, hstj', hasgj, hpij, hswj, -, herrj,
          husesj⟩ := hsitej
        have hij' : runX (L.mach (M' + 1) g) ij s = uj := hij
        have hcpj : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) ij s)) := by
          rw [hij']; exact hpij.callPc
        have hiji : ij = i := callIdx_unique hcpj hcp hcbj
        subst hiji hij'
        obtain ⟨tj, tj1, hrtj, hcnj, hstj, -⟩ := reachN_call_at hu _ hjn
        obtain ⟨hItj, hctj, -⟩ := nextAdv_reachN hPf hk hI hWE.clif.callers hp0 rfl hrtj
        have hptj := L.counter_reachN hk hgf hI hWE.clif.callers (hWE.place hN) hrtj
        subst husesj
        rcases L.nv_cases hL hκ hg hWE.dead (L.BP (M' + 1) g s) (L.RP (M' + 1) g s) cs _ hrelj with
          ⟨h', hh', args', vals'', cmj, csj', rvj, cmj', hshape, hinvN, hcal', -, hmrW', hargsW',
            hsavW', hsw', hinit', hrun'', hspw'⟩ | ⟨nm, valsb, cmb, hinvN, hpfb, hshapeb⟩
        · obtain ⟨t', hrt', hcn', hinv'⟩ := hinvN
          obtain rfl := reachN_call_unique hrt' hcn' hrtj hcnj
          exact L.countStep_prog hL hκ hN ih hdet hdt hg hWE hME hra htab htrj hspj hcij hCSj hopsj
            hstj' hasgj hpij herrj hgdj hGuj hswj hh' hshape hcal' hmrW' hargsW' hsavW' hspw'
            hinit' hrun'' hrtj hcnj hstj hinv' hItj hctj hptj hcnt
        · obtain ⟨t', hrt', hcn', hinv'⟩ := hinvN
          obtain rfl := reachN_call_unique hrt' hcn' hrtj hcnj
          have himgUj : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) ij s).mem a = L.imgMem a :=
            fun a ha => (hGuj a (he.imgG a ha)).trans (he.imgS a ha)
          have hn := L.callDecodeBase hL hg hcij hCSj hopsj hstj' hasgj hpij himgUj hpfb
            (hshapeb.imp (fun h => h.1) fun h => h)
          exact L.countStep_base hL hN hg hcp hn hrtj hcnj hstj hinv' hpfb hItj hctj hptj hcnt
      · intro e' h1
        have h0 := L.tabUpTo_succ_noCall hcp h1
        rw [hcnt e' h0]
        simp only [callsBefore, hcp, ↓reduceIte, Nat.add_zero]
  rw [hcntAll n (Nat.le_refl n) e hte]
  exact nextAdv_leave_of_done hPf hk hI hWE.clif.callers hp0 rfl hu hd

/-- **`ThmPRBRL` at every depth without `CountPRB`** (`thmPRBRL_all`, `CountPRB` by
`countPRB_zero` and `countPRB_succ`). -/
theorem thmPRBRL_allC (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hB : L.BaseRetOk)
    (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRB κ M)
    (hdt : ∀ M, L.DetTabPRB κ M) (M : Nat) : L.ThmPRBRL κ M := by
  by_cases hN : L.NeedSlots
  · induction M with
    | zero => exact L.thmPRBRL_zero_of hL hκ hB hC
    | succ M ih =>
      have hret := L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1)
      exact L.thmPRBRL_succS hL hκ hN ih (hdet M) (hdt (M + 1)) hret
        (L.countPRB_succ hL hκ hN ih (hdet M) (hdt (M + 1)) hret)
  · exact L.thmPRBRL_of_thm hL hN (L.thm hL hκ M)

end LinkSys

end E2E
