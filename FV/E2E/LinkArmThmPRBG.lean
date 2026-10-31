import FV.E2E.LinkArmStage2E
import FV.E2E.BackendWorldPRGYNX
import FV.E2E.LinkGood
import FV.E2E.LinkArmActualEntry

/-!
# The per-state facts of the linked machine under the slot-byte oracle (SEM1 #537, executable level (b))

The executable-level theorem needs, for the model's run, the per-state facts `actGoodX` at every
reachable state of every nested activation (`RunGoodL`, `LinkGood.lean`). `ThmG` gives them in the
oracle-less world (`WorldEntry`). Here: **`ThmPRBG`**, the same at the entries of `ThmPRBRLE`
(`WorldEntryB`, `MachEntryPR` with the run's own prophecies, the prefix-closed table `TableOfE`).

* the activation's own states: the trace of `backend_correct_world_pipelinePRGYNX` (`actGoodX`
  for the guarded semantics `XPBTGY … .at m` of some `m`; `GoodAt` asks for some semantics only);
* its call states: the prefix theorem `prefix_relatedPRI_atEG` at the call's count (the CLIF run
  has as many calls as the machine before its return), whose answer of `XPBTGY … .at m` is, by
  stage 2 (`Stage2ZS` at the call state, `XPBTGY_subZS`), the answer of `XPRBT … m`
  (inside `thmPRBG_of`);
* **`ansDecode`**: at such a call of the function `h` of `P` the answer is a program call
  (`progXPRBT`), with `h`'s argument registers, `RaOk`, and for a `blr` the `BlrTo` fact
  (`BlrAt`);
* the nested activations: the program call's `CondBT` (callee CLIF run returns, canonical
  `TableOf`) gives the callee's actual entry (`actualEntry`) and its table (`DetTabPRBr`, the
  reverse determinism transfer, a premise; then `TableOfE`), and `ThmPRBG` one level down.

Results: `ansDecode`, `ThmPRBG`, **`thmPRBG_of`**, `thmPRBG_noSlots`, **`thmPRBG_allC`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The answer of the call semantics at a machine call of a function of `P`** (module doc). -/
theorem ansDecode (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {u : Arm.ArmState}
    {i : MInst} {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : i.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i')
    (himgU : ∀ a, L.Img a → u.mem a = L.imgMem a)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs u))
    {M : Nat} {F : BitVec 64 → Prop} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {m : Nat} {w : Arm.ArmState} {r : List CV × Arm.ArmState}
    (hx : (L.XPRBT κ M g F P R m).call (callDest info) (useVals ops regs u) w = some r)
    {h : Clif.Function} (hct : L.CallsTo g u h) :
    h ∈ L.P.funcs ∧ L.Callee g h ∧ ∃ Lu : List (Nat × Reg), Lu.map (·.2) = regLocs h.sig ∧
      RaOk (L.A h) (Arm.r .PC u) ∧
      L.progXPRBT κ M F h (Lu.map (fun q => regVal u q.2)) (P m) (R m) w = some r ∧
      (∀ x, insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some (.blr x) →
        ∃ info tv, (L.A g).vcp.CallSite info ∧ info.dest = .reg (.vreg tv .int) ∧
          L.BlrTo g tv h) := by
  obtain ⟨hops0, ic, hasg0, hpi0⟩ := call_of_callLike hi hops hasg hpi
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨x, hins, hx'⟩ := L.insnAt_callAt hL hg hpi0
  have hcp := hpi0.callPc
  cases hd : info.dest with
  | sym n =>
    obtain ⟨d0, us0, ds0⟩ := info
    simp only at hd
    subst hd
    obtain ⟨us', ds', hic⟩ := assign_call_sym hasg0
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have hpf : L.P.func? n = some h := by
      rcases hct with ⟨n', hn', hpf'⟩ | ⟨⟨r', hr'⟩, -⟩
      · rw [hins] at hn'; cases hn'; exact hpf'
      · rw [hins] at hr'; cases hr'
    obtain ⟨hh, -⟩ := Clif.Program.func?_some hpf
    have hps : L.ProgSite g ⟨.sym n, us0, ds0⟩ h := ⟨hS, n, rfl, hpf⟩
    obtain ⟨n', Lu, Ld, hinfo, hLu, -⟩ := hL.callRegs g hg _ h hps
    cases hinfo
    rw [operands_call_sym] at hops0
    cases hops0
    have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    have hx2 : L.progXPRBT κ M F h (Lu.map (fun q => regVal u q.2)) (P m) (R m) w = some r := by
      rw [← L.XPRBT_prog hpf, ← call_useVals hregs]; exact hx
    exact ⟨hh, .inl ⟨_, hps⟩, Lu, hLu, hL.raCall g hg _ h hps _ hcp, hx2,
      fun x' hx'' => by rw [hins] at hx''; cases hx''⟩
  | reg r' =>
    have hreg : ∀ n, info.dest ≠ .sym n := fun n => by rw [hd]; simp
    obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hS hreg
    rw [operands_call_reg] at hops0
    cases hops0
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨r1, us', ds', hr1, he⟩ := assign_call_reg hasg0
    injection he with he
    subst he
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have htgt : blrTarget u = some (lo64 (regVal u (.x n0))) := by
      obtain ⟨j, x', tt, hj, hx'', hpc⟩ := hpi0
      simp only [MInst.callInsn?, Option.some.injEq] at hx''
      subst hx''
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg u himgU k wd hk)
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
      rcases hct with ⟨n', hn', -⟩ | ⟨-, hb⟩
      · rw [hins] at hn'; cases hn'
      · rw [htgt] at hb; exact hb
    have hx2 : (L.XPRBT κ M g F P R m).call none
        (regVal u (.x n0) :: Lu.map (fun q => regVal u q.2)) w = some r := by
      rw [← call_useVals_reg hregs0]; exact hx
    rw [L.XPRBT_ind hs] at hx2
    split at hx2
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hgd tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
        rw [call_useVals_reg hregs0] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_target hL hs e
      obtain ⟨hLu, -⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
      exact ⟨hh, .inr (.inr ⟨hh, hdecl.1.1⟩), Lu, hLu,
        hL.raBlr g hg _ hS hreg h hh hdecl.1.1 _ hcp, hx2,
        fun _ _ => ⟨_, tv, hS, rfl, hdecl.1, hgot⟩⟩
    · cases hx2

/-- **The per-state part of `ThmPRBRLE`** (module doc): at `ThmPRBRLE`'s entries, a returning
CLIF run gives every state of the machine run (the activation's and the nested ones) whose step
ends without error the per-state facts. -/
def ThmPRBG (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s) →
    RaOk (L.A g) (ra - 4) →
    L.TableOfE M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    L.RunGoodL M g s

/-- **The induction step of `ThmPRBG`** (module doc), determinism `DetPRBRU` (#719, #732): from
`thmPRBRL_ofZSERU`'s premises, `ThmPRBG` one level down and the reverse table transfer
`DetTabPRBr`. -/
theorem thmPRBG_ofRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSE κ M)
    (ihG : 0 < M → L.ThmPRBG κ (M - 1)) (hdtr : 0 < M → L.DetTabPRBr κ M) :
    L.ThmPRBG κ M := by
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
  have hpipe := backend_correct_world_pipelinePRGYNX (hL.subset g hg) hc
    (XI := L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) (syms := L.syms)
    (env := L.envOfB M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    hnrc (hret g hg F vals cs w₀ ini hWE) (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel
    hWE.args (trapsExplicit_of_returned hrun') fuel
  obtain ⟨_us, _outs, _wf, -, -, -, -, -, hall⟩ := hpipe.1 rvals cm' hrun'
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hZS := h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
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
  obtain ⟨n, hret', -, -, hgood, u, hu, -⟩ := hall (L.hooks M) G (L.A g).base ra (κ M g) (spv w₀)
    (L.BP M g s) (L.RP M g s) s hAE
  change ReachN _ _ cs u (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n) at hu
  -- the call data at the machine's call states before the return (the prefix theorem)
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
    have hpre := prefix_relatedPRI_atEG (hL.subset g hg) hc (instCallsOne_all g)
      (tryCallsOne_all g) (hL.covered g hg) hnrc hX (fun n b hn => hL.symOk n b hn) rfl hWE.clif
      hWE.rel hWE.args (trapsExplicit_of_returned hrun') hrun' hAE' hrtl hcnl
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
  -- every state before the return whose step ends without error is before `n`
  have hbound : ∀ k, (∀ j ≤ k, ¬ RetL (L.A g) s (runX (L.mach M g) j s)) → k < n :=
    fun k hno => Nat.lt_of_not_le fun hle => hno n hle (L.retL_of_actRet he.abi hret')
  have hcode : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hc.layout]; have := hL.fits g hg; omega
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  intro M' g' c' t hRL herrt
  cases hRL with
  | act hno =>
    rename_i k
    obtain ⟨m, hG⟩ := hgood k (hbound k hno)
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
      hxP, -⟩ := hcall k (hbound k hno) ⟨j, _, tt, hj', .inr ⟨xr, rfl⟩, hpcj⟩
    have himgU : ∀ a, L.Img a → (runX (L.mach M g) k s).mem a = L.imgMem a :=
      fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
    obtain ⟨-, -, -, -, -, -, hblr⟩ := L.ansDecode hL hg hci hCS hops hst hasg hpi himgU hgd hxP
      (h := h) (.inr ⟨⟨xr, hx'⟩, hb⟩)
    exact hblr xr hx'
  | nest hno hcl herr1 hR' =>
    rename_i M0 k h
    obtain ⟨m, hG⟩ := hgood k (hbound k hno)
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
      hxP, hcs⟩ := hcall k (hbound k hno) hcp
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

/-- **The induction step of `ThmPRBG`**, determinism `DetPRBR` (`thmPRBG_ofRU`,
`DetPRBR.toU`). -/
theorem thmPRBG_ofR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSE κ M)
    (ihG : 0 < M → L.ThmPRBG κ (M - 1)) (hdtr : 0 < M → L.DetTabPRBr κ M) :
    L.ThmPRBG κ M :=
  L.thmPRBG_ofRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hret h2 ihG hdtr

/-- **The induction step of `ThmPRBG`** (`thmPRBG_ofR` with `DetPRB`). -/
theorem thmPRBG_of (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSE κ M)
    (ihG : 0 < M → L.ThmPRBG κ (M - 1)) (hdtr : 0 < M → L.DetTabPRBr κ M) :
    L.ThmPRBG κ M :=
  L.thmPRBG_ofR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hret h2 ihG hdtr

/-- **`ThmPRBG` without program callees with slots** (the oracle unused): from `ThmG`. -/
theorem thmPRBG_noSlots (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) (hN : ¬ L.NeedSlots) (M : Nat) :
    L.ThmPRBG κ M :=
  fun g hg F vals cs w₀ fuel rvals cm' _ G ra s hWE hME _ _ hrun =>
    (L.thmG hL hκ M g hg F vals cs w₀ fuel rvals cm' (hWE.toWorldEntry L hN) hrun).1 G ra s
      hME.entryP.entry

/-- **`ThmPRBG` at every depth** under `NeedSlots`, from `thmPRBRLE_allC`'s premises and the
reverse table transfer `DetTabPRBr`. -/
theorem thmPRBG_allC (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRB κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hdtr : ∀ M, L.DetTabPRBr κ M) (M : Nat) :
    L.ThmPRBG κ M := by
  induction M with
  | zero =>
    exact L.thmPRBG_of hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
      (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSE_zero hL)
      (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0))
  | succ M ihM =>
    have ihE := L.thmPRBRLE_allC hL hκ hN hB hC hdet hdt M
    have hret := L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1)
    exact L.thmPRBG_of hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L ihE)
      (fun _ => by rw [Nat.add_sub_cancel]; exact hdet M) hret
      (L.stage2PRBZS_ofE hL hκ hN ihE (hdet M) (hdt (M + 1)) hret)
      (fun _ => by rw [Nat.add_sub_cancel]; exact ihM) (fun _ => hdtr (M + 1))

/-- **`ThmPRBG` at every depth from the determinism premises `DetPRBR`, `DetTabPRBE`,
`DetTabPRBr`** (#719: `thmPRBG_allC` with the satisfiable determinism premise). -/
theorem thmPRBG_allCR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBR κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hdtr : ∀ M, L.DetTabPRBr κ M) (M : Nat) :
    L.ThmPRBG κ M := by
  induction M with
  | zero =>
    exact L.thmPRBG_ofR hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
      (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSE_zero hL)
      (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0))
  | succ M ihM =>
    have ihE := L.thmPRBRLE_allCR hL hκ hN hB hC hdet hdt M
    have hret := L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1)
    exact L.thmPRBG_ofR hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L ihE)
      (fun _ => by rw [Nat.add_sub_cancel]; exact hdet M) hret
      (L.stage2PRBZS_ofER hL hκ hN ihE (hdet M) (hdt (M + 1)) hret)
      (fun _ => by rw [Nat.add_sub_cancel]; exact ihM) (fun _ => hdtr (M + 1))

/-- **`ThmPRBG` at every depth from the determinism premises `DetPRBRU`, `DetTabPRBE`,
`DetTabPRBr`** (#732: `thmPRBG_allCR` with the determinism premise at the result registers of a
`rets` site). -/
theorem thmPRBG_allCRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBRU κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hdtr : ∀ M, L.DetTabPRBr κ M) (M : Nat) :
    L.ThmPRBG κ M := by
  induction M with
  | zero =>
    exact L.thmPRBG_ofRU hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
      (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSE_zero hL)
      (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0))
  | succ M ihM =>
    have ihE := L.thmPRBRLE_allCRU hL hκ hN hB hC hdet hdt M
    have hret := L.retOkPRB_of (κ := κ) hL hN hB hC (M + 1)
    exact L.thmPRBG_ofRU hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L ihE)
      (fun _ => by rw [Nat.add_sub_cancel]; exact hdet M) hret
      (L.stage2PRBZS_ofERU hL hκ hN ihE (hdet M) (hdt (M + 1)) hret)
      (fun _ => by rw [Nat.add_sub_cancel]; exact ihM) (fun _ => hdtr (M + 1))

end LinkSys

end E2E
