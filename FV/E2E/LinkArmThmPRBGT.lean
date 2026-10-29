import FV.E2E.LinkArmTrapE
import FV.E2E.BackendWorldPRGYNXT
import FV.E2E.LinkArmProgramInitR

/-!
# The per-state facts of a trapping run under the slot-byte oracle (SEM1 #537)

`ThmPRBG` (`LinkArmThmPRBG`) gives the per-state facts `RunGoodL` for a **returning** CLIF run
under the oracle. **`ThmPRBGT`**: the same for a **trapping** CLIF run (its traps explicit), with
`thmPRBG_ofR`'s proof on the pipeline's counted trap clause
(`backend_correct_world_pipelinePRGYNXT`):

* the activation's states before the trap index `n`: the trap clause's trace `actGoodX`; every
  state from the trap site on errs, so a state whose step ends without error is before `n`;
* its call states: the prefix theorem for an ending run (`prefix_relatedPRI_atEG_ends`) at a CLIF
  calling state of the count before the trap (the trap clause's `ReachN … (callsBefore … n)`);
* the nested activations: callees of a trapping run return, so `ThmPRBG` one level down.

`ThmPRBGT`, **`thmPRBGT_ofR`**, **`thmPRBGT_allCR`**; at the program level
**`backend_correct_program_core_initETXR`**, **`backend_correct_program_initETXR`**: a trapping
whole-program run under the machine's own slot table is realised by the linked machine reaching
the trap site, and every state of its run whose step ends without error has the per-state facts
(without `NeedSlots`, by `backend_correct_program_coreX`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The per-state part of `ThmPRBTE`** (module doc). -/
def ThmPRBGT (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
    L.RunGoodL M g s

/-- **The trapping step of `ThmPRBG`** (module doc), determinism `DetPRBRU` (#732). -/
theorem thmPRBGT_ofRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSEnds κ M)
    (ihG : 0 < M → L.ThmPRBG κ (M - 1)) (hdtr : 0 < M → L.DetTabPRBr κ M) :
    L.ThmPRBGT κ M := by
  intro g hg F vals cs w₀ fuel c ini G ra s hWE hME hra htab htrL hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .trapped c := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hrun
  have htrB := L.trapsExplicit_envOfB hL hg hJ htrL
  have hend : RunEnds (Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs) :=
    runEnds_trapped hrun'
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hnrc : NoRetCall (L.envOfB M g (spv w₀)) L.P.bare cs :=
    noRetCall_of_linv hPf (fun _ h => by simp at h) hI
  have hpipe := backend_correct_world_pipelinePRGYNXT (hL.subset g hg) hc
    (XI := L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) (syms := L.syms)
    (env := L.envOfB M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    hnrc (hret g hg F vals cs w₀ ini hWE) (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel
    hWE.args htrB fuel
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hZS := h2 g hg F vals cs w₀ fuel ini G ra s hWE hME hra htab htrL (runEnds_trapped hrun)
  have hX := hX_guardRXRI (Γ := ⟨F, L.syms, (L.A g).af.slotBase,
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩) (f := g) (c := spv w₀)
    (L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) hnrc (hret g hg F vals cs w₀ ini hWE)
  have hpc := (L.calleeOkPRBRLRU hL hκ ih hdet hg he (hQ 0)).pc
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
  obtain ⟨n, -, -, hgood, hstuck, u, hu, -⟩ := hpipe c hrun' (L.hooks M) G (L.A g).base ra (κ M g)
    (spv w₀) (L.BP M g s) (L.RP M g s) s hAE
  change ReachN _ _ cs u (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n) at hu
  -- the call data at the machine's call states before the trap (the prefix theorem)
  have hcall : ∀ i < n, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) →
      ∃ (ins : MInst) (info : CallInfo) (w : Arm.ArmState) (r : List CV × Arm.ArmState)
        (ops : Array Operand) (regs : Array Reg) (i' : MInst) (cc : CheckCtx) (wh : String),
        (ins = .call info ∨ ∃ ti, ins = .tryCall info ti) ∧ (L.A g).vcp.CallSite info ∧
        ins.operands = .ok ops ∧ cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok () ∧
        ins.assign regs = .ok i' ∧
        CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) i' ∧
        SameWorld F (runX (L.mach M g) i s) w ∧
        (∀ a, G a → (runX (L.mach M g) i s).mem a = s.mem a) ∧
        gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach M g) i s)) ∧
        (L.XPRBT κ M g F (L.BP M g s) (L.RP M g s)
          (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i)).call (callDest info)
            (useVals ops regs (runX (L.mach M g) i s)) w = some r ∧
        L.CallStPRB κ M g s w₀ (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i)
          (runX (L.mach M g) i s) := by
    intro i hi hcp
    have hjn : callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i <
        callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n := callsBefore_lt hcp hi
    obtain ⟨tl, -, hrtl, hcnl, -, -⟩ := reachN_call_at hu
      (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n - 1) (by omega)
    have hAE' : ActEntryPRN (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
        (κ M g) F G
        (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
        (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀
        (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n - 1) :=
      ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
        fun k _ => L.calleeOkXPBTGZSRU hL hκ ih hdet hg he (hQ k) (hZS k),
        fun _ k _ => L.calleeTryOkXPBTGZSRU hL hκ ih hdet hg he (hQ k) (hZS k),
        hpc,
        fun ht _ => by
          have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
          cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
        he.body⟩
    have hpre := prefix_relatedPRI_atEG_ends (hL.subset g hg) hc (instCallsOne_all g)
      (tryCallsOne_all g) (hL.covered g hg) hnrc hX (fun n b hn => hL.symOk n b hn) rfl hWE.clif
      hWE.rel hWE.args htrB hend hAE' hrtl hcnl
    obtain ⟨uj, insj, infoj, usesj, wj, rj, ⟨ij, hij, hcbj, -⟩, hspj, hsitej, hcij, hCSj,
      hgdj, hxj, -⟩ := hpre (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i) (by omega)
    obtain ⟨-, -, hGuj, ccj, whj, opsj, regsj, i'j, hopsj, hstj', hasgj, hpij, hswj, halj, herrj,
      husesj⟩ := hsitej
    have hij' : runX (L.mach M g) ij s = uj := hij
    have hcpj : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) ij s)) := by
      rw [hij']; exact hpij.callPc
    have hiji : ij = i := callIdx_unique hcpj hcp hcbj
    subst hiji hij' husesj
    have hcs : L.CallStPRB κ M g s w₀ (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s ij)
        (runX (L.mach M g) ij s) :=
      ⟨onCallPR_of hME.entryP.proph hME.reg ⟨ij, rfl, rfl⟩, hspj⟩
    have hxP := L.XPBTGY_subZS hL (hZS (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s ij))
      _ wj hcs hswj insj infoj hcij hCSj opsj regsj i'j hopsj ccj whj hstj' hasgj hpij halj herrj
      hgdj rj hxj
    exact ⟨insj, infoj, wj, rj, opsj, regsj, i'j, ccj, whj, hcij, hCSj, hopsj, hstj', hasgj, hpij,
      hswj, hGuj, hgdj, hxP, hcs⟩
  -- every state whose step ends without error is before the trap index `n`
  have hbound : ∀ k, Arm.r .ERR (runX (L.mach M g) (k + 1) s) = .None → k < n :=
    fun k hk => Nat.lt_of_not_le fun hle => hstuck (k - n) (by
      rw [show n + (k - n) + 1 = k + 1 by omega]; exact hk)
  have hcode : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hc.layout]; have := hL.fits g hg; omega
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  intro M' g' c' t hRL herrt
  cases hRL with
  | act hno =>
    rename_i k
    have hk : k < n := hbound k (by rw [runX_add]; exact herrt)
    obtain ⟨m, hG⟩ := hgood k hk
    refine ⟨_, κ M g, G, GotV (L.A g).vcp, ?_, hG, he.imgG, he.imgS, ?_⟩
    · rfl
    intro xr h hx hb
    obtain ⟨-, -, -, ⟨x, ⟨j, tt, hj, hpcj⟩, -⟩, -⟩ := hG
    replace hpcj : Arm.r .PC (runX (L.mach M g) k s) = _ := hpcj
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hx' : insnAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) k s)) = some x := by
      rw [hpcj]; exact insnAt_line hcode hj'
    rw [hx'] at hx
    cases hx
    obtain ⟨ins, info, w, r, ops, regs, i', cc, wh, hci, hCS, hops, hst, hasg, hpi, hsw, hGu, hgd,
      hxP, -⟩ := hcall k hk ⟨j, _, tt, hj', .inr ⟨xr, rfl⟩, hpcj⟩
    have himgU : ∀ a, L.Img a → (runX (L.mach M g) k s).mem a = L.imgMem a :=
      fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
    obtain ⟨-, -, -, -, -, -, hblr⟩ := L.ansDecode hL hg hci hCS hops hst hasg hpi himgU hgd hxP
      (h := h) (.inr ⟨⟨xr, hx'⟩, hb⟩)
    exact hblr xr hx'
  | nest hno hcl herr1 hR' =>
    rename_i M0 k h
    have hk : k < n := hbound k herr1
    obtain ⟨m, hG⟩ := hgood k hk
    obtain ⟨-, -, hprog, ⟨x, ⟨j, tt, hj, hpcj⟩, -⟩, -⟩ := hG
    replace hpcj : Arm.r .PC (runX (L.mach (M0 + 1) g) k s) = _ := hpcj
    replace hprog : (runX (L.mach (M0 + 1) g) k s).program = _ := hprog
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hins : insnAt (L.A g).fa (progBase (runX (L.mach (M0 + 1) g) k s))
        (Arm.r .PC (runX (L.mach (M0 + 1) g) k s)) = some x := by
      rw [hpcj]; exact insnAt_ofLine hc.layout hlm (by have := hL.fits g hg; omega) hprog hj'
    have hxb : insnAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M0 + 1) g) k s)) =
        some x := by
      rw [hpcj]; exact insnAt_line hcode hj'
    obtain ⟨hct, hcp⟩ : L.CallsTo g (runX (L.mach (M0 + 1) g) k s) h ∧
        CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M0 + 1) g) k s)) := by
      rcases hcl with ⟨n', hn', hpf'⟩ | ⟨⟨r', hr'⟩, hb⟩
      · rw [hins] at hn'; cases hn'
        exact ⟨.inl ⟨n', hxb, hpf'⟩, ⟨j, _, tt, hj', .inl ⟨n', rfl⟩, hpcj⟩⟩
      · rw [hins] at hr'; cases hr'
        exact ⟨.inr ⟨⟨r', hxb⟩, hb⟩, ⟨j, _, tt, hj', .inr ⟨r', rfl⟩, hpcj⟩⟩
    obtain ⟨ins, info, w, r, ops, regs, i', cc, wh, hci, hCS, hops, hst, hasg, hpi, hsw, hGu, hgd,
      hxP, hcs⟩ := hcall k hk hcp
    have himgU : ∀ a, L.Img a → (runX (L.mach (M0 + 1) g) k s).mem a = L.imgMem a :=
      fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
    obtain ⟨hh, hcal, Lu, hLu, hrah, hx2, -⟩ := L.ansDecode hL hg hci hCS hops hst hasg hpi himgU
      hgd hxP hct
    -- the program call's condition: the callee's CLIF run, its canonical table
    have hcond := hx2
    unfold progXPRBT progXBT at hcond
    split at hcond
    · rename_i hcd
      obtain ⟨⟨hM, herrW, halW, hroomW, hdeadW, vals', cm, cs', rvals', cm'', ini', hmr, hargs,
        hsav, hpl, htabC, hinit, hrun2⟩, -⟩ := hcd
      have hspW : spv (L.worldPR κ (M0 + 1) h
          (L.BP (M0 + 1) g s (callsBefore (L.mach (M0 + 1) g) (L.A g).fa (L.A g).base s k))
          (L.RP (M0 + 1) g s (callsBefore (L.mach (M0 + 1) g) (L.A g).fa (L.A g).base s k)) w) =
          spv w :=
        L.r_worldPR_out (κ := κ) (M := M0 + 1) h _ _ w (f := .GPR 31#5)
          (fun hm => by simp [MaskedReg, Masked] at hm)
      obtain ⟨hmskQ, hrgnQ⟩ := hQ _ _ hcs hcp
      obtain ⟨hcOk, hmsk, hrgn, -⟩ := L.callerFacts hL hκ hM hg hh hcal hWE.img hLu hsw himgU hrah
        hmskQ hrgnQ (fun a ha => hdeadW a (by rw [hspW]; exact ha))
      have hpf := func?_of_mem hL.names hh
      have htabE := L.tableOfE_of (hdtr hM h.name h hpf ⟨g, hg, hcal⟩ F hWE.img _ _ herrW halW
        hroomW hdeadW
        vals' cm cs' rvals' cm'' ini' hmr hargs hsav (fun hN => (hpl hN).1) (fun hN => (hpl hN).2)
        hinit hrun2 _ hcOk hmsk hrgn htabC)
      obtain ⟨Fh, G', w₀', m', hWE', hME', hra', hm'⟩ := L.actualEntry hL hM hpf ⟨g, hg, hcal⟩
        hWE.img herrW halW hroomW hdeadW (hκ.2 _ h hh) hmr hargs hsav (fun hN => (hpl hN).1)
        (fun hN => (hpl hN).2) hinit hrun2 hcOk hrgn
      exact ihG hM h hh Fh vals' cs' w₀' m' rvals' cm'' (calleeIni h ini') G' _ _ hWE' hME' hra'
        htabE hm' _ _ _ _ hR' herrt
    · cases hcond

/-- **The trapping step of `ThmPRBG`**, determinism `DetPRBR` (`thmPRBGT_ofRU`,
`DetPRBR.toU`). -/
theorem thmPRBGT_ofR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSEnds κ M)
    (ihG : 0 < M → L.ThmPRBG κ (M - 1)) (hdtr : 0 < M → L.DetTabPRBr κ M) :
    L.ThmPRBGT κ M :=
  L.thmPRBGT_ofRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hret h2 ihG hdtr

/-- **`ThmPRBGT` at every depth** under `NeedSlots`, from `thmPRBG_allCRU`'s premises (#732). -/
theorem thmPRBGT_allCRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBRU κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hdtr : ∀ M, L.DetTabPRBr κ M) (M : Nat) :
    L.ThmPRBGT κ M := by
  cases M with
  | zero =>
    exact L.thmPRBGT_ofRU hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
      (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSEnds_zero hL)
      (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0))
  | succ M =>
    have ihE := L.thmPRBRLE_allCRU hL hκ hN hB hC hdet hdt M
    have hret := L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1)
    exact L.thmPRBGT_ofRU hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L ihE)
      (fun _ => by rw [Nat.add_sub_cancel]; exact hdet M) hret
      (L.stage2PRBZS_ofE_endsRU hL hκ hN ihE (hdet M) (hdt (M + 1)) hret)
      (fun _ => by rw [Nat.add_sub_cancel]; exact L.thmPRBG_allCRU hL hκ hN hB hC hdet hdt hdtr M)
      (fun _ => hdtr (M + 1))

/-- **`ThmPRBGT` at every depth** under `NeedSlots`, determinism `DetPRBR` (`thmPRBGT_allCRU`,
`DetPRBR.toU`). -/
theorem thmPRBGT_allCR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBR κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hdtr : ∀ M, L.DetTabPRBr κ M) (M : Nat) :
    L.ThmPRBGT κ M :=
  L.thmPRBGT_allCRU hL hκ hN hB hC (fun M => DetPRBR.toU L (hdet M)) hdt hdtr M

end LinkSys

/-- **A trapping activation entered from outside under the machine's own slot table, with the
per-state facts** (module doc), determinism `DetPRBRU` (#732), the oracle route's premises only
under `NeedSlots`. -/
theorem backend_correct_program_core_initETXRU (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.NeedSlots → L.BaseRetOk)
    (hRC : L.NeedSlots → ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : L.NeedSlots → ∀ M, L.DetPRBRU κ M) (hdt : L.NeedSlots → ∀ M, L.DetTabPRBE κ M)
    (hdtr : L.NeedSlots → ∀ M, L.DetTabPRBr κ M) (hK : L.NeedSlots → L.HooksKeep)
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) ∧ L.RunGoodL M f s := by
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
    have htab := L.tableOfE_iniOf (M := M) hL (hK hN) hf hent.program
    exact ⟨L.thmPRBTE_allCRU hL hκ hN (hBR hN) (hRC hN) (hdet hN) (hdt hN) M f hf L.F args cs w₀
      fuel c (L.iniOf M f s) L.Img ra s hWE hMEP hra htab htr hrun,
      L.thmPRBGT_allCRU hL hκ hN (hBR hN) (hRC hN) (hdet hN) (hdt hN) (hdtr hN) M f hf L.F args
        cs w₀ fuel c (L.iniOf M f s) L.Img ra s hWE hMEP hra htab htr hrun⟩
  · obtain ⟨hA, hG⟩ := backend_correct_program_coreX L hL hκ hf M hent hres hF hgfree himg hbe
      hargs hcs hsav hrel (fun h => absurd h hN) htr (o := .trapped c) fun _ => ⟨fuel, hrun⟩
    exact ⟨hA, hG (.inr ⟨c, rfl⟩)⟩

/-- **`backend_correct_program_core_initETXRU` with `DetPRBR`** (`DetPRBR.toU`). -/
theorem backend_correct_program_core_initETXR (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBR κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hdtr : ∀ M, L.DetTabPRBr κ M) (hK : L.HooksKeep)
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) ∧ L.RunGoodL M f s :=
  backend_correct_program_core_initETXRU L hL hκ (fun _ => hBR) (fun _ => hRC)
    (fun _ M => LinkSys.DetPRBR.toU L (hdet M)) (fun _ => hdt) (fun _ => hdtr) (fun _ => hK) hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

/-- **The whole-program trapping run under the machine's own slot table, with the per-state
facts** (module doc): a trapping whole-program CLIF run of at most `M + 1` steps (its traps
explicit) from `f`'s entry placed with the machine's own table is realised by the linked machine
of depth `M`, and every state of its run whose step ends without error has the per-state facts;
determinism `DetPRBRU` (#732), the oracle route's premises only under `NeedSlots`. -/
theorem backend_correct_program_initETXRU (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.NeedSlots → L.BaseRetOk)
    (hRC : L.NeedSlots → ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : L.NeedSlots → ∀ M, L.std.DetPRBRU κ M) (hdt : L.NeedSlots → ∀ M, L.std.DetTabPRBE κ M)
    (hdtr : L.NeedSlots → ∀ M, L.std.DetTabPRBr κ M) (hK : L.NeedSlots → L.HooksKeep)
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) ∧ L.RunGoodL M f s := by
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
  obtain ⟨hA, hG⟩ := backend_correct_program_core_initETXRU L.std (hL.withCrun _) hκ hBR hRC
    hdet hdt hdtr (fun hN => ⟨(hK hN).err, (hK hN).tlsErr, (hK hN).prog, (hK hN).tlsProg⟩) hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hm
  exact ⟨hA, LinkSys.runGoodL_withCrun hG⟩

/-- **`backend_correct_program_initETXRU` with `DetPRBR`** (`DetPRBR.toU`). -/
theorem backend_correct_program_initETXR (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : ∀ M, L.std.DetPRBR κ M) (hdt : ∀ M, L.std.DetTabPRBE κ M)
    (hdtr : ∀ M, L.std.DetTabPRBr κ M) (hK : L.HooksKeep)
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.trapped c) ∧ L.RunGoodL M f s :=
  backend_correct_program_initETXRU L hL hκ (fun _ => hBR) (fun _ => hRC)
    (fun _ M => LinkSys.DetPRBR.toU L.std (hdet M)) (fun _ => hdt) (fun _ => hdtr) (fun _ => hK)
    hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

end E2E
