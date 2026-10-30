import FV.E2E.LinkArmProgInst
import FV.E2E.LinkArmStage2ZS
import FV.E2E.LinkArmStage2Count
import FV.E2E.BackendPrefixAtCleanup
import FV.E2E.IselCallsOneAll

/-!
# Stage 2 at the call sites from the depth below (SEM1 #537, #680 (3), stage 2 glue (2)+(3))

**`stage2PRBZS_of`**: under `NeedSlots`, `Stage2PRBZS κ (M' + 1)` from `ThmPRBRL κ M'`,
`DetPRB κ M'`, `DetTabPRB κ (M' + 1)` and `RetOkPRB κ (M' + 1)`.

For an activation of `g` whose CLIF run returns, by strong induction on the call count `n`:
stage 2 at the calls `k < n` gives the machine contracts of those calls (`calleeOkXPBTGZS`), so
the counted pipeline up to call `n` itself (`prefix_relatedPRI_atE`) realises every call `j ≤ n`
of the CLIF run at the machine's call-`j` state with the `Good` trace, the call site and its GOT
guard, and the CLIF invocation of count `j` behind it (`RelatedN`, `nv_cases`). The call state
of stage 2 at count `n` is the machine's call-`n` state (`callIdx_unique`). Along the machine run
up to it the caller table's count is the CLIF counter's advance `Σ_{k < j} advAt k` before
call `j` (inner induction over the steps: `tabUpTo_succ_noCall`, `countStep_prog`,
`countStep_base`), so the invocation of count `n` is placed with `ini` advanced by the table's
count (`counter_reachN`) and has the oracle facts (`oracleAt_at`); `stage2_answerF` answers.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **Stage 2 at the call sites from the depth below** (module doc). -/
theorem stage2PRBZS_of (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRL κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRB κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.Stage2PRBZS κ (M' + 1) := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
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
  suffices H : ∀ n, (∀ k < n, L.Stage2ZS κ (M' + 1) g F (L.BP (M' + 1) g s) (L.RP (M' + 1) g s)
      (L.envOfB (M' + 1) g (spv w₀)) cs (spv w₀) (L.CallStPRB κ (M' + 1) g s w₀ k) k) →
      L.Stage2ZS κ (M' + 1) g F (L.BP (M' + 1) g s) (L.RP (M' + 1) g s)
        (L.envOfB (M' + 1) g (spv w₀)) cs (spv w₀) (L.CallStPRB κ (M' + 1) g s w₀ n) n by
    intro n
    exact Nat.strongRecOn n fun n ihn => H n ihn
  intro n IH
  have hAE : ActEntryPRN (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ (M' + 1) g) F G
      (L.XPBTGY κ (M' + 1) g F (L.BP (M' + 1) g s) (L.RP (M' + 1) g s)
        (L.envOfB (M' + 1) g (spv w₀)) cs (spv w₀))
      (L.hooks (M' + 1)) (L.A g).base ra (κ (M' + 1) g) (spv w₀) (L.BP (M' + 1) g s)
      (L.RP (M' + 1) g s) s w₀ n :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun k hk => L.calleeOkXPBTGZS hL hκ ih' hdet' hg he (hQ k) (IH k hk),
      fun _ k hk => L.calleeTryOkXPBTGZS hL hκ ih' hdet' hg he (hQ k)
        (IH k hk),
      hpc,
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ (M' + 1) g)
        exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  intro u w hu hsw ins info hi hS ops regs i' hops cc wh hst hasg hpi hal herr hgd hnv
  refine L.stage2_answerF hL hκ ih' hdet' hg hWE.img hWE.room hWE.dead
    hWE.align _ _ cs n ?_ hnv
  intro h hh args vals' cm cs' rvals' cm'' hd hA hcal hM hmrW hargsW hsavW hswW hspw hinit hrun2
  obtain ⟨t, hrt, hcnt1, hinvt⟩ := hA
  have hpre := prefix_relatedPRI_atE (hL.subset g hg) hc (instCallsOne_all g) (tryCallsOne_all g)
    (hL.covered g hg) hnrc hX (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
    (trapsExplicit_of_returned hrun') hrun' hAE hrt hcnt1
  obtain ⟨un, insn, infon, usesn, wn, rn, ⟨i1, hi1, hcb1, htr1⟩, hsp1, hsite1, hci1, hCS1, hgd1,
    hx1, hrel1⟩ := hpre n (Nat.le_refl n)
  obtain ⟨⟨⟨⟨iu, hiu, hcbu⟩, -⟩, -⟩, hspu⟩ := hu
  have hcpu : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) iu s)) := by
    rw [hiu]; exact hpi.callPc
  obtain ⟨-, -, hGun, cc1, wh1, ops1, regs1, i1', -, -, -, hpi1, -⟩ := hsite1
  have hi1' : runX (L.mach (M' + 1) g) i1 s = un := hi1
  have hcp1 : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i1 s)) := by
    rw [hi1']; exact hpi1.callPc
  have hiu1 : iu = i1 := callIdx_unique hcpu hcp1 (hcbu.trans hcb1.symm)
  subst hiu1 hiu hi1'
  -- the count invariant up to the call state
  have hcntAll : ∀ i ≤ iu, ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
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
      have hlt : i < iu := by omega
      have hcnt := ihi (by omega)
      by_cases hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s))
      · have hjn : callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i < n := by
          rw [← hcbu]; exact callsBefore_lt hcp hlt
        obtain ⟨uj, insj, infoj, usesj, wj, rj, ⟨ij, hij, hcbj, htrj⟩, hspj, hsitej, hcij, hCSj,
          hgdj, -, hrelj⟩ := hpre _ (Nat.le_of_lt hjn)
        obtain ⟨-, -, hGuj, ccj, whj, opsj, regsj, i'j, hopsj, hstj', hasgj, hpij, hswj, -, herrj,
          husesj⟩ := hsitej
        have hij' : runX (L.mach (M' + 1) g) ij s = uj := hij
        have hcpj : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) ij s)) := by
          rw [hij']; exact hpij.callPc
        have hiji : ij = i := callIdx_unique hcpj hcp hcbj
        subst hiji hij'
        obtain ⟨tj, tj1, hrtj, hcnj, hstj, -⟩ := reachN_call_at hrt _ hjn
        obtain ⟨hItj, hctj, -⟩ := nextAdv_reachN hPf hk hI hWE.clif.callers hp0 rfl hrtj
        have hptj := L.counter_reachN hk hgf hI hWE.clif.callers (hWE.place hN) hrtj
        subst husesj
        rcases L.nv_cases hL hκ hg hWE.dead (L.BP (M' + 1) g s) (L.RP (M' + 1) g s) cs _ hrelj with
          ⟨h', hh', args', vals'', cmj, csj', rvj, cmj', hshape, hinvN, hcal', -, hmrW', hargsW',
            hsavW', hsw', hinit', hrun', hspw'⟩ | ⟨nm, valsb, cmb, hinvN, hpfb, hshapeb⟩
        · obtain ⟨t', hrt', hcn', hinv'⟩ := hinvN
          obtain rfl := reachN_call_unique hrt' hcn' hrtj hcnj
          exact L.countStep_prog hL hκ hN ih hdet hdt hg hWE hME hra htab htrj hspj hcij hCSj hopsj
            hstj' hasgj hpij herrj hgdj hGuj hswj hh' hshape hcal' hmrW' hargsW' hsavW' hspw'
            hinit' hrun' hrtj hcnj hstj hinv' hItj hctj hptj hcnt
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
  -- the oracle facts at call `n`
  subst hcbu
  have hptn := L.counter_reachN hk hgf hI hWE.clif.callers (hWE.place hN) hrt
  have hcm : cm = t.mem := hinvt.1
  obtain ⟨-, -, -, -, -, hor⟩ := L.oracleAt_at hL hκ hdt hg hWE hME hra htab htr1 hsp1 hi hS hops hst
    hasg hpi herr hgd hGun hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun2
    (fun _ => by rw [hcm]; exact hptn) (hcntAll _ (Nat.le_refl _))
  exact hor

end LinkSys

end E2E
