import FV.E2E.LinkArmThmPRBRLE
import FV.E2E.BackendPrefixAtGE
import FV.E2E.BackendWorldPRGYNG

/-!
# Stage 2, the count and the linking statement with the prefix-closed table (SEM1 #537, #680 (3), fix of #700, step 4)

The stage-2 glue of `LinkArmStage2Count`, `LinkArmCallCount`, `LinkArmStage2PRBZSOf`,
`LinkArmCountPRBSucc`, `LinkArmStage2ZS` and `LinkArmThmPRBRLAll` with the caller's
prefix-closed table `TableOfE` (#700) in place of `TableOf`; same proofs, but:

* the machine's call states come with the error-free trace (`prefix_relatedPRI_atEG`), so the
  caller's prefixes up to a call have prefix-closed tables, and tables (`tabUpTo_of_E`: the
  callees before the call returned);
* the callee's `TableOfE` comes from the caller's (`tabUpToE_call_at`), moves to the canonical
  callee entry by `DetTabPRBE`, and gives the canonical callee's `TableOf` (the oracle facts
  `OracleAt` of the call semantics) by `ThmPRBRLE` one level down (`tableOf_canon_of_E`);
* a callee's count is pinned by its run's full table from `progCallPRBRLT`'s return
  (`callCountE`, `tabUpTo_count_E`);
* at the return, the error-free trace of `backend_correct_world_pipelinePRGYNG` gives the table up
  to the return.

Results: `oracleAt_of_callE`, `oracleAt_atE`, `callCountE`, `countStep_progE`, `Stage2PRBZSE`,
**`stage2PRBZS_ofE`**, `CountPRBE`, **`countPRB_succE`**, `countPRBE_zero`, `stage2PRBZSE_zero`,
**`thmPRBRL_ofZSE`**, `thmPRBRLE_succS`, **`thmPRBRLE_allC`** (`ThmPRBRLE` at every depth under
`NeedSlots` from `BaseRetOk`, `RetCount`, `DetPRB`, `DetTabPRBE`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`oracleAt_of_call` with the prefix-closed table** (module doc). -/
theorem oracleAt_of_callE (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M' : Nat}
    (ih : L.ThmPRBRLE κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (hME : L.MachEntry κ (M' + 1) g F G ra s w₀)
    (hra : RaOk (L.A g) (ra - 4)) {ini : Clif.SlotInit} (htab : L.TableOfE (M' + 1) g s ini)
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ (M' + 1) g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ (M' + 1) g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0)
    {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {h : Clif.Function} (hpf : L.P.func? h.name = some h) (hcal : L.Callee g h)
    (hct : L.CallsTo g (runX (L.mach (M' + 1) g) i s) h)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f (runX (L.mach (M' + 1) g) i s) =
      Arm.r f (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)))
    (hrgnQ : ∀ a, StackBelow (κ (M' + 1) g) (spv (runX (L.mach (M' + 1) g) i s)) a →
      (runX (L.mach (M' + 1) g) i s).mem a =
        P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig) {w : Arm.ArmState}
    (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w) (hspw : spv w = c)
    (himgT : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a)
    (hrah : RaOk (L.A h) (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    {x : Nat} (hpl : L.NeedSlots → L.PlaceAtB cm c (ini.adv x))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e → e = x)
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun (M' + 1) cs = .returned rvals cm') :
    L.OracleAt κ (M' + 1) h c cm (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) := by
  have hM : 0 < M' + 1 := Nat.succ_pos M'
  have hh : h ∈ L.P.funcs := L.callee_mem hcal
  have hbud := L.budget_step hκ hM hg hcal
  have hnr := L.noRetAt_upTo hL hg hME hra (fun j hj => (htrE j hj).1) hsp herr
  have herrs : ∀ j < i + 1, Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None := fun j hj => by
    rcases Nat.lt_or_ge j i with hlt | hge
    · exact (htrE j hlt).2.1
    · obtain rfl : j = i := by omega
      exact herr
  have hpb : ∀ j < i, progBase (runX (L.mach (M' + 1) g) j s) = (L.A g).base := fun j hj =>
    L.progBase_of_callsTo hL hg hct (htrE j hj).2.2
  obtain ⟨E, hE, hsb, -, htabCE, -⟩ := L.tabUpToE_call_at htab hnr herrs hpb hcp hct
  obtain ⟨e0, he0⟩ := htab i (fun j hj => hnr j (by omega)) (fun j hj => herrs j (by omega))
  have he0' : L.TabUpTo (M' + 1) g s ini.bytes ini.next i e0 :=
    L.tabUpTo_of_E hL hg (M' + 1) s _ _ i e0 (fun j hj => (htrE j hj).2.2)
      (fun j hj => herrs (j + 1) (by omega)) he0
  have hx : x = Clif.sumTo E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) :=
    (hcnt e0 he0').symm.trans (hE e0 he0)
  have hst : spv (runX (L.mach (M' + 1) g) i s) = c := (hsw.1 _ (by simp [Masked])).trans hspw
  have hspW : spv (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) = c :=
    (L.r_worldPR_out (κ := κ) (M := M' + 1) h _ _ w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)).trans hspw
  have hdeadW : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M' + 1 - 1) h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha => hdead a (by rw [← hspw]; exact stackBelow_mono ha hbud)
  obtain ⟨hcOk, hmsk, hrgn, hswW⟩ := L.callerFacts hL hκ hM hg hh hcal himgF hLu hsw himgT hrah
    hmskQ hrgnQ hdeadW
  -- the slot bytes
  have hslot : L.NeedSlots → ∀ a, L.SlotByte h c a →
      (ini.adv x).bytes ((ini.adv x).next + 1) a =
        probeMem (L.A h).af (L.worldPR κ (M' + 1) h
          (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
          (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w)
          (BitVec.ofNat 64 a) := by
    intro _ a ha
    have h1 : slotted h = 1 := by
      obtain ⟨p, hp, -⟩ := ha
      unfold slotted
      cases hs : h.slots with
      | nil => rw [hs] at hp; cases hp
      | cons _ _ => rfl
    obtain ⟨hbel, -⟩ := L.slotByte_below hL hg hcal (c := c) (by omega) ha
    have hrg : StackBelow (frameDrop (L.A h).af + κ (M' + 1 - 1) h) c (BitVec.ofNat 64 a) :=
      stackBelow_mono hbel (by omega)
    have e1 := hsb h1 a (by rw [hst]; exact ha)
    simp only [Clif.SlotInit.adv]
    rw [hx, e1]
    refine probeMem_congr (hst.trans hspW.symm) ?_
    rw [hrgnQ _ (by rw [hst]; exact stackBelow_mono hrg hbud), L.mem_worldPR, worldP,
      mem_overlay_in (show L.calleeRgn κ (M' + 1) h w (BitVec.ofNat 64 a) by
        unfold calleeRgn; rw [hspw]; exact hrg)]
  -- the actual callee run's prefix-closed table
  have htabT : L.TableOfE M' h (enterAt (L.A h) (runX (L.mach (M' + 1) g) i s))
      (calleeIni h (ini.adv x)) := by
    rw [calleeIni_adv_eq h ini hx]; exact htabCE
  have herrW : Arm.r .ERR (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) = .None := by
    rw [show Arm.r .ERR _ = Arm.r .ERR w from
        L.r_worldPR_out h _ _ w (fun hm => by simp [MaskedReg, Masked] at hm),
      ← hsw.1 .ERR (by simp [Masked])]; exact herr
  have hcanE := hdt h.name h hpf ⟨g, hg, hcal⟩ F himgF _ _ herrW
    (by rw [hspW]; exact halign) (by rw [hspW]; have := hbud; omega)
    (fun a ha => hdead a (by rw [hspW] at ha; exact stackBelow_mono ha hbud))
    vals cm cs rvals cm' (ini.adv x) hmrW hargsW hsavW (fun hN => by rw [hspW]; exact hpl hN)
    (fun hN => by rw [hspW]; exact hslot hN) hinit hrun _ hcOk hmsk hrgn htabT
  have ih' : L.ThmPRBRLE κ (M' + 1 - 1) := by rw [Nat.add_sub_cancel]; exact ih
  refine ⟨ini.adv x, hpl, hslot, ?_⟩
  exact L.tableOf_canon_of_E hL hM ih' hpf ⟨g, hg, hcal⟩ himgF herrW
    (by rw [hspW]; exact halign) (by rw [hspW]; have := hbud; omega)
    (fun a ha => hdead a (by rw [hspW] at ha; exact stackBelow_mono ha hbud))
    (hκ.2 _ h hh)
    hmrW hargsW hsavW (fun hN => by rw [hspW]; exact hpl hN)
    (fun hN => by rw [hspW]; exact hslot hN) hinit hrun hcanE

/-- **`oracleAt_at` with the prefix-closed table.** -/
theorem oracleAt_atE (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M' : Nat}
    (ih : L.ThmPRBRLE κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {vals : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} {ini : Clif.SlotInit} {G : BitVec 64 → Prop}
    {ra : BitVec 64} {s : Arm.ArmState}
    (hWE : L.WorldEntryB κ (M' + 1) g F vals cs w₀ ini)
    (hME : L.MachEntryPR κ (M' + 1) g F G ra s w₀ (L.BP (M' + 1) g s) (L.RP (M' + 1) g s))
    (hra : RaOk (L.A g) (ra - 4)) (htab : L.TableOfE (M' + 1) g s ini) {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    {ins : MInst} {info : CallInfo} (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : ins.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (L.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState} (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w)
    {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (L.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ L.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (L.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = L.Xb.sym h.name 0)
    (hcal : L.Callee g h) {vals' : List Clif.Val} {cm : Clif.Mem} {cs' : Clif.State}
    {rvals' : List Clif.Val} {cm'' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState L.P h.name vals' cm = .ok cs')
    (hrun : L.crun (M' + 1) cs' = .returned rvals' cm'') {x : Nat}
    (hpl : L.NeedSlots → L.PlaceAtB cm (spv w₀) (ini.adv x))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e → e = x) :
    ∃ Lu : List (Nat × Reg), Lu.map (·.2) = regLocs h.sig ∧
      args = Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2) ∧
      L.CallsTo g (runX (L.mach (M' + 1) g) i s) h ∧
      RaOk (L.A h) (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) ∧
      L.OracleAt κ (M' + 1) h (spv w₀) cm args (L.worldPR κ (M' + 1) h
        (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) := by
  have he := hME.entryP.entry
  have himgU : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a :=
    fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
  obtain ⟨Lu, hLu, hargs, hct, hrah⟩ :=
    L.callDecode hL hg hi hS hops hst hasg hpi himgU hgd hh hd (argsAt_regLocs hargsW)
  have hcp := hpi.callPc
  obtain ⟨hmskQ, hrgnQ⟩ := L.callStPRB_q (κ := κ) (M := M' + 1) he.body.sp
    (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) (runX (L.mach (M' + 1) g) i s)
    ⟨onCallPR_of hME.entryP.proph hME.reg ⟨i, rfl, rfl⟩, hsp⟩ hcp
  subst hargs
  exact ⟨Lu, hLu, rfl, hct, hrah, L.oracleAt_of_callE hL hκ ih hdt hg he hra htab hWE.img
    hWE.room hWE.dead hWE.align htrE hsp herr hcp (func?_of_mem hL.names hh) hcal hct hmskQ hrgnQ
    hLu hsw hspw himgU hrah hmrW hargsW hsavW hpl hcnt hinit hrun⟩

/-- **`callCount` with the prefix-closed table** (module doc), determinism `DetPRBRU` (#732). -/
theorem callCountERU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M' : Nat}
    (ih : L.ThmPRBRL κ M') (hdet : L.DetPRBRU κ M')
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (hME : L.MachEntry κ (M' + 1) g F G ra s w₀)
    (hra : RaOk (L.A g) (ra - 4)) {ini : Clif.SlotInit} (htab : L.TableOfE (M' + 1) g s ini)
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ (M' + 1) g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ (M' + 1) g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0)
    {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {h : Clif.Function} (hpf : L.P.func? h.name = some h) (hcal : L.Callee g h)
    (hct : L.CallsTo g (runX (L.mach (M' + 1) g) i s) h)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f (runX (L.mach (M' + 1) g) i s) =
      Arm.r f (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)))
    (hrgnQ : ∀ a, StackBelow (κ (M' + 1) g) (spv (runX (L.mach (M' + 1) g) i s)) a →
      (runX (L.mach (M' + 1) g) i s).mem a =
        P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig) {w : Arm.ArmState}
    (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w) (hspw : spv w = c)
    (himgT : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a)
    (hrah : RaOk (L.A h) (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hor : L.OracleAt κ (M' + 1) h c cm (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun (M' + 1) cs = .returned rvals cm') :
    ∃ d, (L.NeedSlots → Clif.NextAdv cm cm' d) ∧
      ∀ e e', L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
        L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' → e' = e + d := by
  have hM : 0 < M' + 1 := Nat.succ_pos M'
  have hh : h ∈ L.P.funcs := L.callee_mem hcal
  have hbud := L.budget_step hκ hM hg hcal
  have hnr := L.noRetAt_upTo hL hg hME hra (fun j hj => (htrE j hj).1) hsp herr
  have herrs : ∀ j < i + 1, Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None := fun j hj => by
    rcases Nat.lt_or_ge j i with hlt | hge
    · exact (htrE j hlt).2.1
    · obtain rfl : j = i := by omega
      exact herr
  have hspW : spv (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) = c :=
    (L.r_worldPR_out (κ := κ) (M := M' + 1) h _ _ w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)).trans hspw
  have hdeadW : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M' + 1 - 1) h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha => hdead a (by rw [← hspw]; exact stackBelow_mono ha hbud)
  obtain ⟨hcOk, hmsk, hrgn, -⟩ := L.callerFacts hL hκ hM hg hh hcal himgF hLu hsw himgT hrah
    hmskQ hrgnQ hdeadW
  obtain ⟨inj, hpl, hslot, htabC⟩ := hor
  -- the callee's linking statement, with the trace of the actual callee run
  obtain ⟨us0, outs0, wf0, ec, -, -, -, -, -, hadv, hcall⟩ :=
    L.progCallPRBRLTRU hL hM ih hdet hpf ⟨g, hg, hcal⟩ himgF
      (by rw [show Arm.r .ERR _ = Arm.r .ERR w from
            L.r_worldPR_out h _ _ w (fun hm => by simp [MaskedReg, Masked] at hm),
          ← hsw.1 .ERR (by simp [Masked])]; exact herr)
      (by rw [hspW]; exact halign) (by rw [hspW]; have := hbud; omega)
      (fun a ha => hdead a (by rw [hspW] at ha; exact stackBelow_mono ha hbud))
      (hκ.2 _ h hh)
      hmrW hargsW hsavW (fun hN => by rw [hspW]; exact hpl hN)
      (fun hN => by rw [hspW]; exact hslot hN) htabC hinit hrun
  obtain ⟨k', -, hret', htabk, htrk⟩ := hcall _ hcOk hmsk hrgn
  -- the caller's prefix-closed table over the call
  obtain ⟨e1, E, -, hall⟩ := htab (i + 1) hnr herrs
  obtain ⟨-, hle, -, hretcl⟩ := (hall i (by omega) hcp).2 h hct
  have hc := hL.compiled h hh
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hfd := L.frameDrop_eq hL hh
  have hfdlt : frameDrop (L.A h).af < 2 ^ 64 := by
    have := (spv w).isLt
    have := hdeadW
    have hr : frameDrop (L.A h).af + κ (M' + 1 - 1) h ≤ (spv w).toNat := by rw [hspw]; omega
    omega
  have hro := retOf_of_actRet hret'
  have htabN := hretcl k' hro (fun N'' hN'' => noRetOf_before (X := L.Xb) (H := L.hooks M')
    hc.layout hlm hrah (by omega) hfdlt htrk hro N'' hN'')
  have hec : ec = E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) - slotted h :=
    L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ htabk htabN
  refine ⟨slotted h + ec, fun hN => ?_, fun e e' he he' => ?_⟩
  · have h1 := L.initState_leave_nextAdv hpf hinit (hpl hN)
    have h2 := hadv hN
    have : (if h.slots.isEmpty then 0 else 1) = slotted h := rfl
    rw [this] at h1
    exact h1.trans h2
  · have hpre : L.TabUpToE (M' + 1) g s ini.bytes ini.next i
        (Clif.sumTo E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) :=
      ⟨E, rfl, fun i' hi' => hall i' (by omega)⟩
    have hpost : L.TabUpToE (M' + 1) g s ini.bytes ini.next (i + 1)
        (Clif.sumTo E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s (i + 1))) :=
      ⟨E, rfl, hall⟩
    rw [L.tabUpTo_count_E he hpre, L.tabUpTo_count_E he' hpost]
    simp only [callsBefore, hcp, ↓reduceIte, Clif.sumTo]
    omega

/-- **`callCount` with the prefix-closed table**, determinism `DetPRBR` (`callCountERU`). -/
theorem callCountER (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M' : Nat}
    (ih : L.ThmPRBRL κ M') (hdet : L.DetPRBR κ M')
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (hME : L.MachEntry κ (M' + 1) g F G ra s w₀)
    (hra : RaOk (L.A g) (ra - 4)) {ini : Clif.SlotInit} (htab : L.TableOfE (M' + 1) g s ini)
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ (M' + 1) g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ (M' + 1) g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0)
    {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {h : Clif.Function} (hpf : L.P.func? h.name = some h) (hcal : L.Callee g h)
    (hct : L.CallsTo g (runX (L.mach (M' + 1) g) i s) h)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f (runX (L.mach (M' + 1) g) i s) =
      Arm.r f (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)))
    (hrgnQ : ∀ a, StackBelow (κ (M' + 1) g) (spv (runX (L.mach (M' + 1) g) i s)) a →
      (runX (L.mach (M' + 1) g) i s).mem a =
        P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig) {w : Arm.ArmState}
    (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w) (hspw : spv w = c)
    (himgT : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a)
    (hrah : RaOk (L.A h) (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hor : L.OracleAt κ (M' + 1) h c cm (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun (M' + 1) cs = .returned rvals cm') :
    ∃ d, (L.NeedSlots → Clif.NextAdv cm cm' d) ∧
      ∀ e e', L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
        L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' → e' = e + d :=
  L.callCountERU hL hκ ih (DetPRBR.toU L hdet) hg hME hra htab himgF hroom hdead halign htrE hsp
    herr hcp hpf hcal hct hmskQ hrgnQ hLu hsw hspw himgT hrah hmrW hargsW hsavW hor hinit hrun

/-- **`callCount` with the prefix-closed table** (`callCountER` with `DetPRB`). -/
theorem callCountE (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M' : Nat}
    (ih : L.ThmPRBRL κ M') (hdet : L.DetPRB κ M')
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (hME : L.MachEntry κ (M' + 1) g F G ra s w₀)
    (hra : RaOk (L.A g) (ra - 4)) {ini : Clif.SlotInit} (htab : L.TableOfE (M' + 1) g s ini)
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ (M' + 1) g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ (M' + 1) g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0)
    {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {h : Clif.Function} (hpf : L.P.func? h.name = some h) (hcal : L.Callee g h)
    (hct : L.CallsTo g (runX (L.mach (M' + 1) g) i s) h)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f (runX (L.mach (M' + 1) g) i s) =
      Arm.r f (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)))
    (hrgnQ : ∀ a, StackBelow (κ (M' + 1) g) (spv (runX (L.mach (M' + 1) g) i s)) a →
      (runX (L.mach (M' + 1) g) i s).mem a =
        P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig) {w : Arm.ArmState}
    (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w) (hspw : spv w = c)
    (himgT : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a)
    (hrah : RaOk (L.A h) (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hor : L.OracleAt κ (M' + 1) h c cm (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun (M' + 1) cs = .returned rvals cm') :
    ∃ d, (L.NeedSlots → Clif.NextAdv cm cm' d) ∧
      ∀ e e', L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
        L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' → e' = e + d :=
  L.callCountER hL hκ ih (DetPRB.toR L hdet) hg hME hra htab himgF hroom hdead halign htrE hsp
    herr hcp hpf hcal hct hmskQ hrgnQ hLu hsw hspw himgT hrah hmrW hargsW hsavW hor hinit hrun

/-- **`countStep_prog` with the prefix-closed table**, determinism `DetPRBRU` (#732). -/
theorem countStep_progERU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBRU κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {vals : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} {ini : Clif.SlotInit} {G : BitVec 64 → Prop}
    {ra : BitVec 64} {s : Arm.ArmState}
    (hWE : L.WorldEntryB κ (M' + 1) g F vals cs w₀ ini)
    (hME : L.MachEntryPR κ (M' + 1) g F G ra s w₀ (L.BP (M' + 1) g s) (L.RP (M' + 1) g s))
    (hra : RaOk (L.A g) (ra - 4)) (htab : L.TableOfE (M' + 1) g s ini) {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    {ins : MInst} {info : CallInfo} (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : ins.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (L.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState} (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w)
    {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (L.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ L.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (L.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = L.Xb.sym h.name 0)
    (hcal : L.Callee g h) {vals' : List Clif.Val} {cm : Clif.Mem} {cs' : Clif.State}
    {rvals' : List Clif.Val} {cm'' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState L.P h.name vals' cm = .ok cs')
    (hrun : L.crun (M' + 1) cs' = .returned rvals' cm'')
    {tj tj1 : Clif.State}
    (hrtj : ReachN (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs tj
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
    (hcnj : callNum tj = 1)
    (hstj : Clif.step (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj = .next tj1)
    (hinvj : Clif.Invoked (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj h.name vals' cm)
    (hItj : Clif.LInv (L.P.only g) tj) (hctj : tj.callers = [])
    (hptj : L.PlaceAtB tj.mem (spv w₀) (ini.adv (Clif.sumTo
      (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) :
    ∀ e', L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' →
      e' = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s (i + 1)) := by
  have he := hME.entryP.entry
  have hcm : cm = tj.mem := hinvj.1
  have hpl : L.NeedSlots → L.PlaceAtB cm (spv w₀) (ini.adv (Clif.sumTo
      (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))) := fun _ => by
    rw [hcm]; exact hptj
  obtain ⟨Lu, hLu, hargs, hct, hrah, hor⟩ := L.oracleAt_atE hL hκ ih hdt hg hWE hME hra htab htrE
    hsp hi hS hops hst hasg hpi herr hgd hGu hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun hpl
    hcnt
  have himgU : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a :=
    fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
  have hcp := hpi.callPc
  obtain ⟨hmskQ, hrgnQ⟩ := L.callStPRB_q (κ := κ) (M := M' + 1) he.body.sp
    (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) (runX (L.mach (M' + 1) g) i s)
    ⟨onCallPR_of hME.entryP.proph hME.reg ⟨i, rfl, rfl⟩, hsp⟩ hcp
  subst hargs
  obtain ⟨d, hnd, hgrow⟩ := L.callCountERU hL hκ (ThmPRBRLE.toThmPRBRL L ih) hdet hg he hra htab
    hWE.img hWE.room hWE.dead hWE.align htrE hsp herr hcp (func?_of_mem hL.names hh) hcal hct
    hmskQ hrgnQ hLu hsw hspw himgU hrah hmrW hargsW hsavW hor hinit hrun
  have hm1 : tj1.mem = cm'' := L.adv_prog (hL.free g hg) hItj hctj hinvj
    (func?_of_mem hL.names hh) hinit hrun hstj
  obtain ⟨sps, hp⟩ := hptj
  have hadv : advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) = d :=
    advAt_eq hrtj hcnj hstj (by rw [hm1, ← hcm]; exact hnd hN) hp rfl
  intro e' h1
  obtain ⟨e, h0⟩ := L.tabUpTo_mono h1 (Nat.le_succ i)
  rw [hgrow e e' h0 h1, hcnt e h0]
  simp only [callsBefore, hcp, ↓reduceIte, Clif.sumTo, hadv]

/-- **`countStep_prog` with the prefix-closed table**, determinism `DetPRBR`
(`countStep_progERU`). -/
theorem countStep_progER (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBR κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {vals : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} {ini : Clif.SlotInit} {G : BitVec 64 → Prop}
    {ra : BitVec 64} {s : Arm.ArmState}
    (hWE : L.WorldEntryB κ (M' + 1) g F vals cs w₀ ini)
    (hME : L.MachEntryPR κ (M' + 1) g F G ra s w₀ (L.BP (M' + 1) g s) (L.RP (M' + 1) g s))
    (hra : RaOk (L.A g) (ra - 4)) (htab : L.TableOfE (M' + 1) g s ini) {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    {ins : MInst} {info : CallInfo} (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : ins.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (L.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState} (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w)
    {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (L.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ L.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (L.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = L.Xb.sym h.name 0)
    (hcal : L.Callee g h) {vals' : List Clif.Val} {cm : Clif.Mem} {cs' : Clif.State}
    {rvals' : List Clif.Val} {cm'' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState L.P h.name vals' cm = .ok cs')
    (hrun : L.crun (M' + 1) cs' = .returned rvals' cm'')
    {tj tj1 : Clif.State}
    (hrtj : ReachN (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs tj
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
    (hcnj : callNum tj = 1)
    (hstj : Clif.step (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj = .next tj1)
    (hinvj : Clif.Invoked (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj h.name vals' cm)
    (hItj : Clif.LInv (L.P.only g) tj) (hctj : tj.callers = [])
    (hptj : L.PlaceAtB tj.mem (spv w₀) (ini.adv (Clif.sumTo
      (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) :
    ∀ e', L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' →
      e' = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s (i + 1)) :=
  L.countStep_progERU hL hκ hN ih (DetPRBR.toU L hdet) hdt hg hWE hME hra htab htrE hsp hi hS hops
    hst hasg hpi herr hgd hGu hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun hrtj hcnj hstj hinvj
    hItj hctj hptj hcnt

/-- **`countStep_prog` with the prefix-closed table** (`countStep_progER` with `DetPRB`). -/
theorem countStep_progE (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {vals : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} {ini : Clif.SlotInit} {G : BitVec 64 → Prop}
    {ra : BitVec 64} {s : Arm.ArmState}
    (hWE : L.WorldEntryB κ (M' + 1) g F vals cs w₀ ini)
    (hME : L.MachEntryPR κ (M' + 1) g F G ra s w₀ (L.BP (M' + 1) g s) (L.RP (M' + 1) g s))
    (hra : RaOk (L.A g) (ra - 4)) (htab : L.TableOfE (M' + 1) g s ini) {i : Nat}
    (htrE : ∀ j < i, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      Arm.r .ERR (runX (L.mach (M' + 1) g) j s) = .None ∧
      (runX (L.mach (M' + 1) g) j s).program = (L.A g).fb.program (L.A g).base)
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    {ins : MInst} {info : CallInfo} (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : ins.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (L.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState} (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w)
    {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (L.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ L.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (L.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = L.Xb.sym h.name 0)
    (hcal : L.Callee g h) {vals' : List Clif.Val} {cm : Clif.Mem} {cs' : Clif.State}
    {rvals' : List Clif.Val} {cm'' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState L.P h.name vals' cm = .ok cs')
    (hrun : L.crun (M' + 1) cs' = .returned rvals' cm'')
    {tj tj1 : Clif.State}
    (hrtj : ReachN (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs tj
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
    (hcnj : callNum tj = 1)
    (hstj : Clif.step (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj = .next tj1)
    (hinvj : Clif.Invoked (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj h.name vals' cm)
    (hItj : Clif.LInv (L.P.only g) tj) (hctj : tj.callers = [])
    (hptj : L.PlaceAtB tj.mem (spv w₀) (ini.adv (Clif.sumTo
      (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) :
    ∀ e', L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' →
      e' = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s (i + 1)) :=
  L.countStep_progER hL hκ hN ih (DetPRB.toR L hdet) hdt hg hWE hME hra htab htrE hsp hi hS hops
    hst hasg hpi herr hgd hGu hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun hrtj hcnj hstj hinvj
    hItj hctj hptj hcnt

/-- **`Stage2PRBZS` with the prefix-closed table.** -/
def Stage2PRBZSE (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOfE M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∀ n, L.Stage2ZS κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n

/-- **`CountPRB` with the prefix-closed table.** -/
def CountPRBE (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOfE M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∀ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (n e : Nat),
      ActRet ra F G us outs wf s (runX (L.mach M g) n s) →
      PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n →
      L.TabUpTo M g s ini.bytes ini.next n e → L.NeedSlots → Clif.NextAdv cs.mem.leave cm' e

/-- **`stage2PRBZS_of` with the prefix-closed table** (module doc), determinism `DetPRBRU`
(#732). -/
theorem stage2PRBZS_ofERU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBRU κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.Stage2PRBZSE κ (M' + 1) := by
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
  have hpre := prefix_relatedPRI_atEG (hL.subset g hg) hc (instCallsOne_all g) (tryCallsOne_all g)
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

/-- **`stage2PRBZS_of` with the prefix-closed table**, determinism `DetPRBR`
(`stage2PRBZS_ofERU`). -/
theorem stage2PRBZS_ofER (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBR κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.Stage2PRBZSE κ (M' + 1) :=
  L.stage2PRBZS_ofERU hL hκ hN ih (DetPRBR.toU L hdet) hdt hret

/-- **`stage2PRBZS_of` with the prefix-closed table** (`stage2PRBZS_ofER` with `DetPRB`). -/
theorem stage2PRBZS_ofE (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.Stage2PRBZSE κ (M' + 1) :=
  L.stage2PRBZS_ofER hL hκ hN ih (DetPRB.toR L hdet) hdt hret

/-- **`countPRB_succ` with the prefix-closed table** (module doc), determinism `DetPRBRU`
(#732). -/
theorem countPRB_succERU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBRU κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.CountPRBE κ (M' + 1) := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun us' outs' wf' n e hAR
    hPT hte _
  have hZS := L.stage2PRBZS_ofERU hL hκ hN ih hdet hdt hret g hg F vals cs w₀ fuel rvals cm' ini G
    ra s hWE hME hra htab hrun
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
  have ihO : L.ThmPRBRL κ M' := ThmPRBRLE.toThmPRBRL L ih
  have ih' : 0 < M' + 1 → L.ThmPRBRL κ (M' + 1 - 1) := fun _ => by
    rw [Nat.add_sub_cancel]; exact ihO
  have hdet' : 0 < M' + 1 → L.DetPRBRU κ (M' + 1 - 1) := fun _ => by
    rw [Nat.add_sub_cancel]; exact hdet
  have hpc := (L.calleeOkPRBRLRU hL hκ ih' hdet' hg he (hQ 0)).pc
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
      fun k => L.calleeOkXPBTGZSRU hL hκ ih' hdet' hg he (hQ k) (hZS k),
      fun _ k => L.calleeTryOkXPBTGZSRU hL hκ ih' hdet' hg he (hQ k) (hZS k),
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
            fun k _ => L.calleeOkXPBTGZSRU hL hκ ih' hdet' hg he (hQ k) (hZS k),
            fun _ k _ => L.calleeTryOkXPBTGZSRU hL hκ ih' hdet' hg he (hQ k) (hZS k),
            hpc,
            fun ht _ => by
              have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ (M' + 1) g)
              exact ⟨h0.pc, h0.seq, h0.flags⟩,
            he.body⟩
        have hpre := prefix_relatedPRI_atEG (hL.subset g hg) hc (instCallsOne_all g)
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
          exact L.countStep_progERU hL hκ hN ih hdet hdt hg hWE hME hra htab htrj hspj hcij hCSj hopsj
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

/-- **`countPRB_succ` with the prefix-closed table**, determinism `DetPRBR`
(`countPRB_succERU`). -/
theorem countPRB_succER (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBR κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.CountPRBE κ (M' + 1) :=
  L.countPRB_succERU hL hκ hN ih (DetPRBR.toU L hdet) hdt hret

/-- **`countPRB_succ` with the prefix-closed table** (`countPRB_succER` with `DetPRB`). -/
theorem countPRB_succE (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.CountPRBE κ (M' + 1) :=
  L.countPRB_succER hL hκ hN ih (DetPRB.toR L hdet) hdt hret

/-- `CountPRBE κ 0` (`countPRB_zero`'s proof: the table is not used). -/
theorem countPRBE_zero (hL : L.Ok) [L.CrunOk] : L.CountPRBE κ 0 := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE _ _ _ hrun _ _ _ n e _ _ hte hN
  obtain ⟨rfl, -⟩ := hte
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  exact returned_keeps_leave hPf (L.envR_zero_keeps hL hN g) hI hWE.clif.callers hrun

/-- `Stage2PRBZSE κ 0` (`stage2PRB_zero`'s proof: the table is not used). -/
theorem stage2PRBZSE_zero (hL : L.Ok) [L.CrunOk] : L.Stage2PRBZSE κ 0 :=
  fun _ hg F _ cs w₀ _ _ _ _ _ _ s _ _ _ _ _ n =>
    Stage2Z.toZS L (Stage2Y.toZ L
      (L.stage2Y_zero hL hg F (L.BP 0 _ s) (L.RP 0 _ s) (spv w₀) cs (spv w₀) _ n))

/-- **`thmPRBRL_ofZS` with the prefix-closed table**: the table up to the return from the error-free
trace of `backend_correct_world_pipelinePRGYNG` (`tabUpTo_of_E`). -/
theorem thmPRBRL_ofZSE (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSE κ M) (hcnt : L.CountPRBE κ M) :
    L.ThmPRBRLE κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
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
    hWE.args (trapsExplicit_of_returned hrun') fuel
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall⟩ := h.1 rvals cm' hrun'
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun n => L.calleeOkXPBTGZS hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun _ n => L.calleeTryOkXPBTGZS hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  obtain ⟨n, hret', htr, hgood, -⟩ := hall (L.hooks M) G (L.A g).base ra (κ M g) (spv w₀)
    (L.BP M g s) (L.RP M g s) s hAE
  have hnr := L.noRetAt_of hL hg he hra htr hret'.ret.err
  obtain ⟨e, hteE⟩ := htab n hnr (fun j hj => (hgood j hj).1)
  have hte : L.TabUpTo M g s ini.bytes ini.next n e :=
    L.tabUpTo_of_E hL hg M s _ _ n e (fun j hj => (hgood j hj).2) (fun j hj => by
      rcases Nat.lt_or_ge (j + 1) n with hlt | hge
      · exact (hgood (j + 1) hlt).1
      · obtain rfl : n = j + 1 := by omega
        exact hret'.ret.err) hteE
  exact ⟨us, outs, wf, n, e, hus, hlen, hhold, hmem, hrs, hret', htr, hte,
    hcnt g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun us outs wf n e hret' htr
      hte⟩

/-- **The induction step of `ThmPRBRLE`** (`thmPRBRL_succS` with the prefix-closed table). -/
theorem thmPRBRLE_succS (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.ThmPRBRLE κ (M' + 1) :=
  L.thmPRBRL_ofZSE hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L ih)
    (fun _ => by rw [Nat.add_sub_cancel]; exact hdet) hret
    (L.stage2PRBZS_ofE hL hκ hN ih hdet hdt hret) (L.countPRB_succE hL hκ hN ih hdet hdt hret)

/-- **`ThmPRBRLE` at every depth** under `NeedSlots` (without program callees with slots the
oracle is not needed: `Thm`), from the scope conditions `BaseRetOk`, `RetCount` and the
determinism premises `DetPRB`, `DetTabPRBE`. -/
theorem thmPRBRLE_allC (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRB κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (M : Nat) : L.ThmPRBRLE κ M := by
  induction M with
  | zero =>
    exact L.thmPRBRL_ofZSE hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
      (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSE_zero hL)
      (L.countPRBE_zero hL)
  | succ M ih =>
    exact L.thmPRBRLE_succS hL hκ hN ih (hdet M) (hdt (M + 1))
      (L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1))

/-- **`thmPRBRL_ofZSE` with the determinism premise `DetPRBRU`** (#732; same proof). -/
theorem thmPRBRL_ofZSERU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSE κ M) (hcnt : L.CountPRBE κ M) :
    L.ThmPRBRLE κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
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
    hWE.args (trapsExplicit_of_returned hrun') fuel
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall⟩ := h.1 rvals cm' hrun'
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun n => L.calleeOkXPBTGZSRU hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun _ n => L.calleeTryOkXPBTGZSRU hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  obtain ⟨n, hret', htr, hgood, -⟩ := hall (L.hooks M) G (L.A g).base ra (κ M g) (spv w₀)
    (L.BP M g s) (L.RP M g s) s hAE
  have hnr := L.noRetAt_of hL hg he hra htr hret'.ret.err
  obtain ⟨e, hteE⟩ := htab n hnr (fun j hj => (hgood j hj).1)
  have hte : L.TabUpTo M g s ini.bytes ini.next n e :=
    L.tabUpTo_of_E hL hg M s _ _ n e (fun j hj => (hgood j hj).2) (fun j hj => by
      rcases Nat.lt_or_ge (j + 1) n with hlt | hge
      · exact (hgood (j + 1) hlt).1
      · obtain rfl : n = j + 1 := by omega
        exact hret'.ret.err) hteE
  exact ⟨us, outs, wf, n, e, hus, hlen, hhold, hmem, hrs, hret', htr, hte,
    hcnt g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun us outs wf n e hret' htr
      hte⟩

/-- **`thmPRBRL_ofZSE` with the determinism premise `DetPRBR`** (#719; `thmPRBRL_ofZSERU`). -/
theorem thmPRBRL_ofZSER (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSE κ M) (hcnt : L.CountPRBE κ M) :
    L.ThmPRBRLE κ M :=
  L.thmPRBRL_ofZSERU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hret h2 hcnt

/-- **The induction step of `ThmPRBRLE`, determinism `DetPRBRU`** (#732). -/
theorem thmPRBRLE_succSRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBRU κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.ThmPRBRLE κ (M' + 1) :=
  L.thmPRBRL_ofZSERU hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L ih)
    (fun _ => by rw [Nat.add_sub_cancel]; exact hdet) hret
    (L.stage2PRBZS_ofERU hL hκ hN ih hdet hdt hret) (L.countPRB_succERU hL hκ hN ih hdet hdt hret)

/-- **The induction step of `ThmPRBRLE`, determinism `DetPRBR`** (#719; `thmPRBRLE_succSRU`). -/
theorem thmPRBRLE_succSR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRLE κ M') (hdet : L.DetPRBR κ M') (hdt : L.DetTabPRBE κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) : L.ThmPRBRLE κ (M' + 1) :=
  L.thmPRBRLE_succSRU hL hκ hN ih (DetPRBR.toU L hdet) hdt hret

/-- **`ThmPRBRLE` at every depth from the determinism premises `DetPRBRU`, `DetTabPRBE`**
(#732). -/
theorem thmPRBRLE_allCRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBRU κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (M : Nat) : L.ThmPRBRLE κ M := by
  induction M with
  | zero =>
    exact L.thmPRBRL_ofZSERU hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
      (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSE_zero hL)
      (L.countPRBE_zero hL)
  | succ M ih =>
    exact L.thmPRBRLE_succSRU hL hκ hN ih (hdet M) (hdt (M + 1))
      (L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1))

/-- **`ThmPRBRLE` at every depth from the determinism premises `DetPRBR`, `DetTabPRBE`** (#719:
`thmPRBRLE_allC` with the satisfiable determinism premise; `thmPRBRLE_allCRU`). -/
theorem thmPRBRLE_allCR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBR κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (M : Nat) : L.ThmPRBRLE κ M :=
  L.thmPRBRLE_allCRU hL hκ hN hB hC (fun M => DetPRBR.toU L (hdet M)) hdt M

end LinkSys

end E2E
