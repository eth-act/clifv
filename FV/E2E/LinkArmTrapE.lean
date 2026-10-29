import FV.E2E.LinkArmProgramInitE
import FV.E2E.BackendPrefixAtEnds

/-!
# Traps under the machine's own slot table (SEM1 #537)

`ThmPRBRLE` (`LinkArmThmPRBRLE`, `thmPRBRLE_allC`) and `backend_correct_program_initE` cover
**returning** CLIF runs under the slot-byte oracle. A trapping run is realised the same way
(`backend_correct_program_coreX`'s trap branch): the pipeline's trap clause
(`backend_correct_world_pipelinePRGYNG`) under the activation's call contracts, which come from
stage 2. Stage 2 used the returning run only to know that the run passes each call
(`prefix_relatedPRI_atEG`); a trapping run under `TrapsExplicit` passes them too
(`prefix_relatedPRI_atEG_ends`). The callees of a trapping run return, so `ThmPRBRLE` one level
down covers them.

Determinism premises: `DetPRBR` (#719; the `DetPRB` forms are corollaries through `DetPRB.toR`).

* `reach_envOfB`, `trapsExplicit_envOfB`: the run premises under `envOfB`;
* `Stage2PRBZSEnds`, **`stage2PRBZS_ofE_endsR`** (`stage2PRBZS_ofE_ends`), `stage2PRBZSEnds_zero`:
  `Stage2PRBZSE` for a run that returns or traps;
* `ThmPRBTE`, **`thmPRBTE_ofR`**, **`thmPRBTE_allCR`** (`thmPRBTE_of`, `thmPRBTE_allC`): the
  trapping counterpart of `ThmPRBRLE`;
* **`backend_correct_program_core_initETR`**, **`backend_correct_program_initETR`**
  (`…_initET`): the trapping counterparts of `backend_correct_program_core_initE` /
  `backend_correct_program_initE`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem reach_envOfB (hL : L.Ok) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {cs s : Clif.State} (hr : Reach (L.envOfB M g c) L.P.bare cs s)
    (hJ : L.ActInvB g c cs) :
    Reach (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs s ∧ L.ActInvB g c s := by
  induction hr with
  | refl => exact ⟨.refl _, hJ⟩
  | step hs _ ih =>
    have hs' := L.step_envOfB_link hL hg hJ hs (fun _ h => nomatch h)
    obtain ⟨h1, h2⟩ := ih (L.actInvB_step hL hg hJ hs')
    exact ⟨.step hs' h1, h2⟩

/-- The run premises of `P.bare` under `linkEnvR` are those under `envOfB`. -/
theorem trapsExplicit_envOfB (hL : L.Ok) [L.CrunOk] {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {c : BitVec 64} {cs : Clif.State} (hJ : L.ActInvB g c cs)
    (h : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) :
    TrapsExplicit (L.envOfB M g c) L.P.bare cs where
  stmt := fun s c st rest hr hs hb => by
    obtain ⟨hr', hJs⟩ := L.reach_envOfB hL hg hr hJ
    exact h.stmt s c st rest hr' (L.step_envOfB_link hL hg hJs hs (fun _ h => nomatch h)) hb
  tryCall := fun s c fn args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_envOfB hL hg hr hJ
    exact h.tryCall s c fn args et hr' (L.step_envOfB_link hL hg hJs hs (fun _ h => nomatch h)) hb
      ht
  tryCallInd := fun s c callee args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_envOfB hL hg hr hJ
    exact h.tryCallInd s c callee args et hr'
      (L.step_envOfB_link hL hg hJs hs (fun _ h => nomatch h)) hb ht
  indirect := fun s st rest sig callee args hr hb hi hst =>
    h.indirect s st rest sig callee args (L.reach_envOfB hL hg hr hJ).1 hb hi hst
  tryIndirect := fun s callee args et hr hb ht hB =>
    h.tryIndirect s callee args et (L.reach_envOfB hL hg hr hJ).1 hb ht hB

/-- **`Stage2PRBZSE` for a run that returns or traps** (under `TrapsExplicit`). -/
def Stage2PRBZSEnds (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64)
    (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOfE M g s ini →
    TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs →
    RunEnds (Clif.runLoop (L.envR M g) L.P.bare fuel cs) →
    ∀ n, L.Stage2ZS κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n

/-- **`stage2PRBZS_ofERU` for a run that returns or traps** (`stage2PRBZS_ofERU`'s proof with
`prefix_relatedPRI_atEG_ends`), determinism `DetPRBRU` (#732). -/
theorem stage2PRBZS_ofE_endsRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBRU κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.Stage2PRBZSEnds κ (M' + 1) := by
  intro g hg F vals cs w₀ fuel ini G ra s hWE hME hra htab htrL hend
  have hc := hL.compiled g hg
  have hgf := hL.free g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : RunEnds (Clif.runLoop (L.envOfB (M' + 1) g (spv w₀)) L.P.bare fuel cs) := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hend
  have htrB := L.trapsExplicit_envOfB hL hg hJ htrL
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
  have ihO : L.ThmPRBRL κ M' := ThmPRBRLE.toThmPRBRL L ih
  have ih' : 0 < M' + 1 → L.ThmPRBRL κ (M' + 1 - 1) := fun _ => by
    rw [Nat.add_sub_cancel]; exact ihO
  have hdet' : 0 < M' + 1 → L.DetPRBRU κ (M' + 1 - 1) := fun _ => by
    rw [Nat.add_sub_cancel]; exact hdet
  have hpc := (L.calleeOkPRBRLRU hL hκ ih' hdet' hg he (hQ 0)).pc
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
      fun k hk => L.calleeOkXPBTGZSRU hL hκ ih' hdet' hg he (hQ k) (IH k hk),
      fun _ k hk => L.calleeTryOkXPBTGZSRU hL hκ ih' hdet' hg he (hQ k)
        (IH k hk),
      hpc,
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ (M' + 1) g)
        exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  intro u w hu hsw ins info hi hS ops regs i' hops cc wh hst hasg hpi hal herr hgd hnv
  refine L.stage2_answerFRU hL hκ ih' hdet' hg hWE.img hWE.room hWE.dead
    hWE.align _ _ cs n ?_ hnv
  intro h hh args vals' cm cs' rvals' cm'' hd hA hcal hM hmrW hargsW hsavW hswW hspw hinit hrun2
  obtain ⟨t, hrt, hcnt1, hinvt⟩ := hA
  have hpre := prefix_relatedPRI_atEG_ends (hL.subset g hg) hc (instCallsOne_all g)
    (tryCallsOne_all g) (hL.covered g hg) hnrc hX (fun n b hn => hL.symOk n b hn) rfl hWE.clif
    hWE.rel hWE.args htrB hrun' hAE hrt hcnt1
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
          exact L.countStep_progERU hL hκ hN ih hdet hdt hg hWE hME hra htab htrj hspj hcij hCSj hopsj
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
  obtain ⟨-, -, -, -, -, hor⟩ := L.oracleAt_atE hL hκ ih hdt hg hWE hME hra htab htr1 hsp1 hi hS
    hops hst hasg hpi herr hgd hGun hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun2
    (fun _ => by rw [hcm]; exact hptn) (hcntAll _ (Nat.le_refl _))
  exact hor

/-- **`stage2PRBZS_ofER` for a run that returns or traps**, determinism `DetPRBR`
(`stage2PRBZS_ofE_endsRU`, `DetPRBR.toU`). -/
theorem stage2PRBZS_ofE_endsR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBR κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.Stage2PRBZSEnds κ (M' + 1) :=
  L.stage2PRBZS_ofE_endsRU hL hκ hN ih (DetPRBR.toU L hdet) hdt hret

/-- **`stage2PRBZS_ofE` for a run that returns or traps** (`stage2PRBZS_ofE_endsR` with
`DetPRB`). -/
theorem stage2PRBZS_ofE_ends (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.Stage2PRBZSEnds κ (M' + 1) :=
  L.stage2PRBZS_ofE_endsR hL hκ hN ih (DetPRB.toR L hdet) hdt hret

/-- `Stage2PRBZSEnds κ 0` (`stage2PRB_zero`'s proof: the run is not used). -/
theorem stage2PRBZSEnds_zero (hL : L.Ok) [L.CrunOk] : L.Stage2PRBZSEnds κ 0 :=
  fun _ hg F _ cs w₀ _ _ _ _ s _ _ _ _ _ _ n =>
    Stage2Z.toZS L (Stage2Y.toZ L
      (L.stage2Y_zero hL hg F (L.BP 0 _ s) (L.RP 0 _ s) (spv w₀) cs (spv w₀) _ n))

/-- **The trapping counterpart of `ThmPRBRLE`**: at `ThmPRBRLE`'s entries, a CLIF run of the
activation that traps (its traps explicit) is realised by the linked machine reaching the trap
site. -/
def ThmPRBTE (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (c : Clif.TrapCode) (ini : Clif.SlotInit)
    (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s) →
    RaOk (L.A g) (ra - 4) →
    L.TableOfE M g s ini →
    TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .trapped c →
    ∃ n, TrapAt (L.A g).fb (L.A g).base c (runX (L.mach M g) n s)

/-- **The trapping step** (`thmPRBRL_ofZSERU` with the pipeline's trap clause), determinism
`DetPRBRU` (#732). -/
theorem thmPRBTE_ofRU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSEnds κ M) : L.ThmPRBTE κ M := by
  intro g hg F vals cs w₀ fuel c ini G ra s hWE hME hra htab htrL hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .trapped c := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hrun
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hnrc : NoRetCall (L.envOfB M g (spv w₀)) L.P.bare cs :=
    noRetCall_of_linv hPf (fun _ h => by simp at h) hI
  have h := backend_correct_world_pipelinePRGYNG (hL.subset g hg) hc
    (XI := L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) (syms := L.syms)
    (env := L.envOfB M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    hnrc (hret g hg F vals cs w₀ ini hWE) (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel
    hWE.args (L.trapsExplicit_envOfB hL hg hJ htrL) fuel
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hZS := h2 g hg F vals cs w₀ fuel ini G ra s hWE hME hra htab htrL (runEnds_trapped hrun)
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun n => L.calleeOkXPBTGZSRU hL hκ ih hdet hg he (hQ n) (hZS n),
      fun _ n => L.calleeTryOkXPBTGZSRU hL hκ ih hdet hg he (hQ n) (hZS n),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  exact h.2 c hrun' (L.hooks M) G (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s
    hAE

/-- **The trapping step**, determinism `DetPRBR` (`thmPRBTE_ofRU`, `DetPRBR.toU`). -/
theorem thmPRBTE_ofR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSEnds κ M) : L.ThmPRBTE κ M :=
  L.thmPRBTE_ofRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hret h2

/-- **The trapping step** with `DetPRB` (`thmPRBTE_ofR`, `DetPRB.toR`). -/
theorem thmPRBTE_of (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSEnds κ M) : L.ThmPRBTE κ M :=
  L.thmPRBTE_ofR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hret h2

/-- **`ThmPRBTE` at every depth** under `NeedSlots`, from `thmPRBRLE_allCRU`'s premises (the
callees of a trapping run return: `ThmPRBRLE` one level down), determinism `DetPRBRU` (#732). -/
theorem thmPRBTE_allCRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBRU κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (M : Nat) : L.ThmPRBTE κ M := by
  cases M with
  | zero =>
    exact L.thmPRBTE_ofRU hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
      (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSEnds_zero hL)
  | succ M =>
    have ihE := L.thmPRBRLE_allCRU hL hκ hN hB hC hdet hdt M
    have hret := L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1)
    exact L.thmPRBTE_ofRU hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L ihE)
      (fun _ => by rw [Nat.add_sub_cancel]; exact hdet M) hret
      (L.stage2PRBZS_ofE_endsRU hL hκ hN ihE (hdet M) (hdt (M + 1)) hret)

/-- **`ThmPRBTE` at every depth**, determinism `DetPRBR` (`thmPRBTE_allCRU`, `DetPRBR.toU`). -/
theorem thmPRBTE_allCR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBR κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (M : Nat) : L.ThmPRBTE κ M :=
  L.thmPRBTE_allCRU hL hκ hN hB hC (fun M => DetPRBR.toU L (hdet M)) hdt M

/-- **`ThmPRBTE` at every depth** with `DetPRB` (`thmPRBTE_allCR`, `DetPRB.toR`). -/
theorem thmPRBTE_allC (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRB κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (M : Nat) : L.ThmPRBTE κ M :=
  L.thmPRBTE_allCR hL hκ hN hB hC (fun M => DetPRB.toR L (hdet M)) hdt M

end LinkSys

/-- **A trapping activation entered from outside, under the machine's own slot table**
(`backend_correct_program_core_initE` for a trapping CLIF run whose traps are explicit): under
`NeedSlots` by `thmPRBTE_allCRU`, otherwise (the oracle unused) by `backend_correct_program_core`;
determinism `DetPRBRU` (#732). The oracle route's premises are needed only under `NeedSlots`. -/
theorem backend_correct_program_core_initETRU (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.NeedSlots → L.BaseRetOk)
    (hRC : L.NeedSlots → ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : L.NeedSlots → ∀ M, L.DetPRBRU κ M)
    (hdt : L.NeedSlots → ∀ M, L.DetTabPRBE κ M) (hK : L.NeedSlots → L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.iniOf M f s))
    (htr : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs)
    {fuel : Nat} {c : Clif.TrapCode}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare fuel cs = .trapped c) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB, hK'⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  by_cases hN : L.NeedSlots
  · -- the world side
    have hWE : L.WorldEntryB κ M f L.F args cs w₀ (L.iniOf M f s) := by
      refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
      · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
      · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs (fun off v hm k hk hk' => ?_) hres
        rw [hF] at hk'
        rcases hk' with hw | hi
        · exact stackArgsAvoid_frameW_pipeline hc hres hent hargs off v hm k hk hw
        · exact hsav off v hm k hk hi
      · rw [hbe.sp, hB]; omega
      · intro a ha
        rw [hbe.sp] at ha
        refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
        obtain ⟨h1, h2⟩ := ha
        rw [hB] at h1 h2
        exact ⟨by omega, by omega⟩
      · rw [hbe.sp, hB, hd]
        have := hent.spAligned
        have := L.frameSize_mod hL hf
        omega
    -- the machine side, with the run's own prophecies
    have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
      ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
        hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
          ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
    have hMEP : L.MachEntryPR κ M f L.F L.Img ra s w₀
        (prophOf (L.mach M f) (L.A f).fa (L.A f).base s)
        (prophStOf (L.mach M f) (L.A f).fa (L.A f).base s) :=
      ⟨⟨hME, prophOk_prophOf _ _ _ _ _ _⟩, fun _ hcp _ _ _ _ => by rw [prophStOf_call hcp]⟩
    have hra : RaOk (L.A f) (ra - 4) := .inl fun k hk => by
      rw [BitVec.sub_add_cancel]; exact hent.raOutside k hk
    exact L.thmPRBTE_allCRU hL hκ hN (hBR hN) (hRC hN) (hdet hN) (hdt hN) M f hf L.F args cs w₀
      fuel c (L.iniOf M f s) L.Img ra s hWE hMEP hra (L.tableOfE_iniOf hL (hK hN) hf hent.program)
      htr hrun
  · exact backend_correct_program_core L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav
      hrel (fun h => absurd h hN) htr (o := .trapped c) fun _ => ⟨fuel, hrun⟩

/-- **`backend_correct_program_core_initETRU` with `DetPRBR`** (`DetPRBR.toU`). -/
theorem backend_correct_program_core_initETR (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBR κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hK : L.HooksKeep) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.iniOf M f s))
    (htr : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs)
    {fuel : Nat} {c : Clif.TrapCode}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare fuel cs = .trapped c) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) :=
  backend_correct_program_core_initETRU L hL hκ (fun _ => hBR) (fun _ => hRC)
    (fun _ M => LinkSys.DetPRBR.toU L (hdet M)) (fun _ => hdt) (fun _ => hK) hf M hent hres hF
    hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

/-- **The whole-program trapping run under the machine's own slot table**: a trapping
whole-program CLIF run of at most `M + 1` steps (its traps explicit) from `f`'s entry placed with
the machine's own table is realised by the linked machine of depth `M` reaching the trap site;
determinism `DetPRBRU` (#732), the oracle route's premises only under `NeedSlots`. -/
theorem backend_correct_program_initETRU (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.NeedSlots → L.BaseRetOk)
    (hRC : L.NeedSlots → ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : L.NeedSlots → ∀ M, L.std.DetPRBRU κ M)
    (hdt : L.NeedSlots → ∀ M, L.std.DetTabPRBE κ M) (hK : L.NeedSlots → L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.std.iniOf M f s))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped c) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) := by
  haveI := L.crunOk_std hL
  rw [← L.mach_std]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact backend_correct_program_core_initETRU L.std (hL.withCrun _) hκ hBR hRC hdet hdt
    (fun hN => ⟨(hK hN).err, (hK hN).tlsErr, (hK hN).prog, (hK hN).tlsProg⟩) hf M hent hres hF
    hgfree himg hbe hargs hcs hsav hrel hpl htr hm

/-- **`backend_correct_program_initETRU` with `DetPRBR`** (`DetPRBR.toU`). -/
theorem backend_correct_program_initETR (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : ∀ M, L.std.DetPRBR κ M) (hdt : ∀ M, L.std.DetTabPRBE κ M) (hK : L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.std.iniOf M f s))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped c) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) :=
  backend_correct_program_initETRU L hL hκ (fun _ => hBR) (fun _ => hRC)
    (fun _ M => LinkSys.DetPRBR.toU L.std (hdet M)) (fun _ => hdt) (fun _ => hK) hf M hent hres
    hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

/-- `backend_correct_program_core_initETR` with `DetPRB` (`DetPRB.toR`). -/
theorem backend_correct_program_core_initET (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRB κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hK : L.HooksKeep) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.iniOf M f s))
    (htr : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs)
    {fuel : Nat} {c : Clif.TrapCode}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare fuel cs = .trapped c) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) :=
  backend_correct_program_core_initETR L hL hκ hBR hRC (fun M => LinkSys.DetPRB.toR L (hdet M))
    hdt hK hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

/-- `backend_correct_program_initETR` with `DetPRB` (`DetPRB.toR`). -/
theorem backend_correct_program_initET (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : ∀ M, L.std.DetPRB κ M) (hdt : ∀ M, L.std.DetTabPRBE κ M) (hK : L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.std.iniOf M f s))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped c) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) :=
  backend_correct_program_initETR L hL hκ hBR hRC (fun M => LinkSys.DetPRB.toR L.std (hdet M))
    hdt hK hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

end E2E
