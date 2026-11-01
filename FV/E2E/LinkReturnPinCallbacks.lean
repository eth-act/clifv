import FV.E2E.LinkReturnPinCall

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Clif Opt
set_option autoImplicit false
set_option Elab.async false
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem X_ext_return_pins (hL : L.OkReturnPins modes) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.XMode modes κ M g F).call d uses w = some (outs, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.XMode_base hpf _ _ F] at hx
      exact hL.baseExt _ _ _ _ _ (.inr ⟨n, rfl, hpf⟩) hx herr
    | some h =>
      rw [L.XMode_prog hpf _ _ F] at hx
      exact L.progXMode_ext hx
  | none =>
    cases uses with
    | nil => exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.XMode_none hs] at hx
        exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.XMode_ind hs] at hx
        split at hx
        · exact L.progXMode_ext hx
        · cases hx
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem budget_K_return_pins (hL : L.OkReturnPins modes) : L.Budget fun M _ => L.K M := by
  intro M g _ h hc
  have := hL.depth h (L.callee_mem hc)
  simp only [K, Nat.mul_succ]
  omega
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem progOsCore_return_pins (hL : L.OkReturnPins modes) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : CallReturnPins Ld (modeReturnPins modes h))
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : L.progXMode modes κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  have hpf := func?_of_mem hL.names hh
  have hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves) ∨ L.NeedNI := by
    by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
    · by_cases h1 : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
      · exact .inl ⟨h0, h1⟩
      · exact .inr ⟨g, hg, h, hcallee, .inr h1⟩
    · exact .inr ⟨g, hg, h, hcallee, .inl h0⟩
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lu.map (fun q => regVal t q.2) = uses at hx
  unfold progXMode progXWithPins at hx
  have hcond : L.Cond κ M F h uses w ∧
      Arm.r .ERR (L.pcall M h (L.canon h uses w)) = .None :=
    Classical.byContradiction fun hc => by rw [if_neg hc] at hx; cases hx
  rw [if_pos hcond] at hx
  obtain ⟨⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, rvals, cm', hmr, hargs, hsav, hpl, hinit,
    hrun⟩,
    -⟩ := hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, hrs, hcall, -⟩ :=
    L.progCall_return_pins hL hM (ih hM) hpf ⟨g, hg, hcallee⟩ hib himgF herrw halw hroom hdead hmr hargs hsav hpl
      hinit hrun
  -- the caller state is compatible with the canonical one
  have hcOk : L.CallerOk F h uses w t := by
    refine ⟨hsw, fun a ha => (hG a (himgG a ha)).trans (himgS a ha), fun r hr => ?_,
      hra⟩
    rw [← hLu] at hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
    have hu : uses[j]? = some (regVal t r) := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      simp [← huses, hq]
    rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
      setVal_regVal]
  obtain ⟨ks, hs_eq, hs_ret⟩ := hcall t hcOk
  obtain ⟨kc, hc_eq, hc_ret⟩ := hcall _ (L.callerOk_canon_return_pins hL hh himgF uses w)
  -- the allocated call
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the world
    rw [hs_eq, hc_eq]
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · rw [r_set_program, r_set_program]
      by_cases h29 : f = .GPR 29#5
      · subst h29
        have e1 := hs_ret.ret.savedX 29 (by decide)
        have e2 := hc_ret.ret.savedX 29 (by decide)
        simp only [xreg] at e1 e2
        rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          (L.callerOk_canon_return_pins hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hs_ret.ret.sp
        have e2 := hc_ret.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          (L.callerOk_canon_return_pins hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
      · rw [hs_ret.fields f hf h29 h31, hc_ret.fields f hf h29 h31]
    · simp only [mem_set_program]
      rw [hs_ret.mem a ha, hc_ret.mem a ha]
    · simp only [program_set_program]
      rw [hsw.2.2, L.program_canon]
  · -- the frame outside the dead stack
    rw [hs_eq]
    refine ⟨?_, fun a ⟨ha, hb⟩ => ?_, ?_⟩
    · show spv (Arm.set_program _ _) = spv t
      simp only [spv]; rw [r_set_program]
      have := hs_ret.ret.sp
      simp only [spv] at this
      rw [this, r_enterAt _ _ (by simp) (by simp)]
    · rw [mem_set_program, hs_ret.gkeep a ⟨ha, fun hb' => hb ?_⟩, mem_enterAt]
      have hsp : spv w = spOf t := (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
      rw [hsp] at hb'
      exact stackBelow_mono hb' (L.budget_step hκ hM hg hcallee)
    · rw [r_set_program]
      exact (hs_ret.ret.savedX 29 (by simp [calleeSavedX]; exact ⟨10, by omega, rfl⟩)).trans
        (r_enterAt _ _ (by simp) (by simp))
  · -- the results use the caller's actual matching return pins
    obtain ⟨Nr, hrunN⟩ := hR.runs M cs _ hrun (.inl ⟨_, _, rfl⟩)
    have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm'
      (runInv_entry hh (clifEntry_initState hpf hinit)) hrunN
    have hbot : cs.bottom = h := by
      have hce := clifEntry_initState (f := h) hpf hinit
      simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have hlr : (sigRets h.sig).length ≤ us.length := by
      cases hsr : h.sig.params.any (·.purpose == .sret) with
      | true => exact hL.sretRets h hh hsr us hrs
      | false =>
        rw [sigRets_of_noSret hsr, hlen]
        have := congrArg List.length hrt
        simp only [List.length_map, Clif.AbiParam.tys] at this
        rw [← this]; exact hhold.1
    have same : ∀ pin ∈ modeReturnPins modes h,
        regVal (L.pcall M h t) pin = regVal (L.pcall M h (L.canon h uses w)) pin := by
      intro pin member
      have returnedPin : pin ∈ us.map (·.2) := by
        have selected := ReturnPinMode.pins_prefix_of_valid hus hlr
        change pin ∈ (modes h).pins h (sigRets h.sig).length at member
        rw [selected] at member
        exact List.mem_of_mem_take member
      rw [hs_eq,hc_eq,regVal_set_program,regVal_set_program]
      exact hs_ret.pins_agree hc_ret hlen pin returnedPin
    have resultRegs := hLd.defRegs hdefs same
    simpa only [List.map_map,Function.comp_def] using resultRegs
  · -- the registers the callee preserves
    intro r hr hnd' hnc
    rw [hs_eq, regVal_set_program]
    have hnotd : r ∉ Ld.map (·.1) := by
      intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      have hmem : (⟨⟨q.2, .int, .def, .late, .fixed q.1⟩, q.1⟩ : Operand × Reg) ∈
          (ops.zip regs).toList := by
        have h1 : (⟨⟨q.2, .int, .def, .late, .fixed q.1⟩, q.1⟩ : Operand × Reg) ∈
            (callDefOps Ld).zip (Ld.map (·.1)) := List.mem_iff_getElem?.mpr (by
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
          exact ⟨i, by simp [callDefOps, List.getElem?_zip_eq_some, hi]⟩)
        rw [← hdefs] at h1
        exact (List.mem_filter.mp h1).1
      exact hnd' _ hmem rfl rfl
    have hnD : r ∉ defaultAapcsClobbers := by
      intro hm
      apply hnc
      simp only [MInst.clobbers, List.mem_filter, hm, true_and, hdefs0, callDefs]
      simp only [List.any_map, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      exact fun q hq e => hnotd (List.mem_map.mpr ⟨q, hq, by simpa using e⟩)
    rcases allocatable_cases hr with ⟨m, rfl, hm, h16, h17, h18⟩ | ⟨m, rfl, hm⟩
    · have h19 : 19 ≤ m :=
        Classical.byContradiction fun hc => hnD (by simp [defaultAapcsClobbers]; omega)
      have e := hs_ret.ret.savedX m (by simp [calleeSavedX]; exact ⟨m - 19, by omega, by omega⟩)
      simp only [xreg] at e
      simp only [regVal]
      rw [show rnum m = BitVec.ofNat 5 m from rfl, e, r_enterAt _ _ (by simp) (fun e' => by
        have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e'
        simp [rnum_toNat (show m < 32 by omega)] at this; omega)]
    · exact absurd (by simp [defaultAapcsClobbers]; omega) hnD
  · -- the callee-saved registers the call clobbers: the low halves of v8–v15
    intro r hr hcs
    rw [hs_eq, regVal_set_program]
    have hrD : r ∈ defaultAapcsClobbers := (List.mem_filter.mp hr).1
    simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hcs
    rcases hcs with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact absurd hrD (by simp [defaultAapcsClobbers]; omega)
    · have e := hs_ret.ret.savedV (8 + i) (by omega) (by omega)
      simp only [ckeep, regVal]
      rw [show rnum (8 + i) = BitVec.ofNat 5 (8 + i) from rfl, e,
        r_enterAt _ _ (by simp) (by simp)]
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem got_target_return_pins (hL : L.OkReturnPins modes) {a : BitVec 64} {h : Clif.Function} {n : String}
    (hs : symCallee L.Xb L.P a = some h) (e : a = L.Xb.sym n 0) : n = h.name := by
  have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
  have := List.find?_some hs
  simp only [beq_iff_eq] at this
  exact hL.symInj h hh n (this.trans e)
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem progOs_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XMode modes κ M g F)) (.call info) .next := by
  have ⟨_, n, hdest, hpf⟩ := hsite
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  obtain ⟨n', Lu, Ld, hinfo, hLu, hLd⟩ := hL.callRegs g hg info h hsite
  subst hinfo
  cases hdest
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  replace hsem := csemV_sub hsem
  rw [operands_call_sym] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  rw [call_useVals hregs] at hsem
  have hx : L.progXMode modes κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w') := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.XMode_prog hpf] at hx
    exact hx
  have matched : CallReturnPins Ld (modeReturnPins modes h) :=
    (hL.compiled g hg).calls.direct _ h hsite Ld rfl
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_some hpf],
    L.progOsCore_return_pins hL hκ ih hg hh (.inl ⟨_, hsite⟩) himgF himgG himgS hLu matched rfl (call_defs hregs) hK hG
      (hL.raCall g hg _ h hsite _ hP.callPc) hsw hx⟩
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem progOsReg_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XMode modes κ M g F)) (.call info) .next := by
  obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  have hguard := csemV_guard hsem
  replace hsem := csemV_sub hsem
  have hops0 := hops
  rw [operands_call_reg] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  -- the target register: an allocatable X register
  obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
    have hmem : (tgtOp tv, Loc.reg r0) ∈
        (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
      simp [Array.toList_zip, Array.toList_map, hregs0]
    obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
    exact ⟨n, hn, h29, h16⟩
  have hsem0 := hsem
  rw [call_useVals_reg hregs0] at hsem
  -- the allocated call: `blr x n0`
  obtain ⟨r1, us', ds', hr1, rfl⟩ := assign_call_reg hasg
  have h0 : regs[0]? = some (.x n0) := by
    rw [← Array.getElem?_toList, hregs0]; rfl
  rw [h0] at hr1
  cases hr1
  -- the target the machine reads
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rw [lo64_regVal_x]
    exact blrTarget_of hc.layout hlm hj hn0 hpc
      (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (himgG a ha)).trans (himgS a ha)) k wd hk)
  -- the external semantics' call
  have hx : (L.XMode modes κ M g F).call none (regVal t (.x n0) :: Lu.map (fun q => regVal t q.2)) w =
      some (outs, w') := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    exact hx
  cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
  | none =>
    -- no function of `P` at the target: the base's contract
    have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
    rw [L.XMode_none hs] at hx
    have hsem' : csem F ctx L.Xb (.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩)
        (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
        some (outs, w', .next) := by
      rw [call_useVals_reg hregs0]; simp [csem, hx]
    obtain ⟨s', hex, rest⟩ := hL.baseOs g hg _ hsite (.inl rfl) F (κ M g) G s0
      (CallAt (L.A g).fa (L.A g).base) ctx t hK hD hG c wh _ regs _ w outs w' hops0 hst hasg hP hsw
      hal herr hsem'
    refine ⟨s', ?_, rest⟩
    simp only [callExec] at hex ⊢
    rw [L.hooks_base (.inl rfl) t (fun _ => hb)]
    exact hex
  | some h =>
    rw [L.XMode_ind hs] at hx
    split at hx
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
        rw [call_useVals_reg hregs0] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_target_return_pins hL hs e
      obtain ⟨hLu, hLd⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
      have matched : CallReturnPins Ld (modeReturnPins modes h) :=
        (hL.compiled g hg).calls.indirect _ hsite tv rfl h hh ⟨hdecl.1,hgot⟩
          (by simpa only [retPairs,List.length_map] using hdecl.2.symm) Ld rfl
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
      exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_none hb],
        L.progOsCore_return_pins hL hκ ih hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) himgF himgG himgS hLu matched rfl
          (call_defs_reg hregs0) hK hG
          (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hP.callPc) hsw hx⟩
    · cases hx
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem calleeOk_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XMode modes κ M g F) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) where
  os ctx info hsite := by
    cases hd : info.dest with
    | reg r =>
      exact L.progOsReg_return_pins hL hκ ih hg he.imgF he.imgG he.imgS hsite (fun n => by rw [hd]; simp) ctx
    | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h => exact L.progOs_return_pins hL hκ ih hg he.imgF he.imgG he.imgS ⟨hsite, n, hdest, hpf⟩ ctx
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      have h0 := hL.baseOs g hg info hsite hb F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) ctx
      intro t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.call ⟨.sym n, us, ds⟩) (useVals ops regs t) w =
          some (outs, w', .next) := by
        rw [← csemV_sub hsem]; simp [csem, L.XMode_base hpf _ _ F]
      obtain ⟨s', hex, rest⟩ :=
        h0 t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem'
      refine ⟨s', ?_, rest⟩
      obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
      simp only [callExec] at hex ⊢
      rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
      exact hex
  pc d u herr hal := by
    cases d with
    | none =>
      cases hb : (blrTarget u).bind (symCallee L.Xb L.P) with
      | none =>
        rw [L.hooks_base (.inl rfl) u (fun _ => hb)]; exact hL.basePc _ _ (.inl rfl) herr hal
      | some h => rw [L.hooks_none hb]; exact (L.pcall_pc M h u).2
    | some n =>
      cases hpf : L.P.func? n with
      | none =>
        rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) u (fun h => by cases h)]
        exact hL.basePc _ _ (.inr ⟨n, rfl, hpf⟩) herr hal
      | some h => rw [L.hooks_some hpf]; exact (L.pcall_pc M h u).2
  ext _ _ _ _ _ hx herr := L.X_ext_return_pins hL hx herr
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem calleeTryOk_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeTryOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XMode modes κ M g F) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  intro ctx info ti hsite
  cases hd : info.dest with
  | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact calleeTryOkG_of_call (S := fun i t => i = info ∧ t = ti)
        (fun ctx' i t ⟨e1, _⟩ => e1 ▸ (L.calleeOk_return_pins hL hκ ih hg he).os ctx' info hsite.callSite)
        (fun _ _ _ h => callAt_tryCall_call h)
        (fun i t ⟨_, e2⟩ => e2 ▸ trySite_clobberAll (hL.compiled g hg).alloc hsite)
        ctx info ti ⟨rfl, rfl⟩
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      intro c wh ops regs i' t w outs w' s' _ _ _ hops hst hasg _ hsw hal herr hsem hex
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.sym n, us, ds⟩ ti) (useVals ops regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem]; simp [csem, L.XMode_base hpf _ _ F]
      obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
      obtain ⟨us', ds', hic⟩ := assign_call_sym hasg'
      cases hic
      have hex' : callExec L.Hb (.tryCall ⟨.sym n, us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, hb⟩ c wh ops regs _ t w outs w' s' hops hst hasg
        hsw hal herr hsem' hex'
  | reg r =>
    obtain ⟨tv, Lu, Ld, hinfo, -⟩ :=
      hL.blrRegs g hg info hsite.callSite (fun n => by rw [hd]; simp)
    subst hinfo
    intro c wh ops regs i' t w outs w' s' hK hD hG hops hst hasg hP hsw hal herr hsem hex
    have hcl := trySite_clobberAll (hL.compiled g hg).alloc hsite
    have hopsC : (MInst.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩).operands = .ok ops := by
      rw [← operands_tryCall_call _ ti]; exact hops
    have hops1 := hopsC
    rw [operands_call_reg] at hops1
    cases hops1
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs)
      (by have := hsz'; simp only [Array.size_map] at this ⊢; simpa using this)
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasg'
    cases hic
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
      obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
      simp only [MInst.callInsn?, Option.some.injEq] at hx
      subst hx
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (he.imgG a ha)).trans (he.imgS a ha)) k wd hk)
    have huv := call_useVals_reg (tv := tv) (s := t) hregs0
    cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
    | none =>
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩ ti)
          (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem, huv]; simp [csem, L.XMode_none hs]
      have hex' : callExec L.Hb (.tryCall ⟨.reg (.x n0), us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inl rfl) t (fun _ => hb)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, .inl rfl⟩ c wh _ regs _ t w outs w' s' hops hst
        hasg hsw hal herr hsem' hex'
    | some h =>
      exact calleeTry_at ((L.calleeOk_return_pins hL hκ ih hg he).os ctx _ hsite.callSite)
        (fun _ _ h => callAt_tryCall_call h) hcl hK hD hG hops hst hasg hP hsw hal herr hsem hex
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem find_sym_return_pins (hL : L.OkReturnPins modes) (n : String) :
    (∀ h, L.P.func? n = some h → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = some h) ∧
    (L.P.func? n = none → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = none) := by
  constructor
  · intro h hpf
    cases hf : L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) with
    | none =>
      obtain ⟨hh, rfl⟩ := Clif.Program.func?_some hpf
      have := List.find?_eq_none.mp hf h hh
      simp at this
    | some h' =>
      have hh' := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      simp only [beq_iff_eq] at he
      have := hL.symInj h' hh' n he
      subst this
      rw [func?_of_mem hL.names hh'] at hpf
      cases hpf; rfl
  · intro hn
    cases hf : L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) with
    | none => rfl
    | some h' =>
      have hh' := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      simp only [beq_iff_eq] at he
      have := hL.symInj h' hh' n he
      subst this
      rw [func?_of_mem hL.names hh'] at hn
      cases hn
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem progResult_return_pins (hL : L.OkReturnPins modes) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals rvals : List Clif.Val} {cm' : Clif.Mem} {cs : Clif.State}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : L.NeedSlots → L.PlaceAt cm c) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : L.crun M cs = .returned rvals cm') :
    ∃ outs w', L.progXMode modes κ M F h args w = some (outs, w') ∧ outs.length = (sigRets h.sig).length ∧
      PrefixHold rvals outs ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' := by
  have hpf := func?_of_mem hL.names hh
  have hM : 0 < M := by
    cases M with
    | zero => exact absurd hret (hR.zero cs rvals cm')
    | succ M => omega
  obtain ⟨Nr, hretN⟩ := hR.runs M cs _ hret (.inl ⟨_, _, rfl⟩)
  obtain ⟨⟨hmemR0, hslot, hout⟩, hsp, herrw⟩ := hmr
  have hroom' : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat := by
    rw [hsp]; have := L.budget_step hκ hM hg hcallee; omega
  have hdead' : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha =>
    hdead a (by rw [← hsp]; exact stackBelow_mono ha (L.budget_step hκ hM hg hcallee))
  have hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves) ∨ L.NeedNI := by
    by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
    · by_cases h1 : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
      · exact .inl ⟨h0, h1⟩
      · exact .inr ⟨g, hg, h, hcallee, .inr h1⟩
    · exact .inr ⟨g, hg, h, hcallee, .inl h0⟩
  have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hN => by rw [hsp]; exact hpl hN
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, hrs, hcall, -⟩ :=
    L.progCall_return_pins hL hM (ih hM) hpf ⟨g, hg, hcallee⟩ hib himgF herrw (by rw [hsp]; exact halign)
      hroom' hdead' hmemR0 hargs hsav hplw hinit hret
  obtain ⟨kc, hc_eq, hc_ret⟩ := hcall _ (L.callerOk_canon_return_pins hL hh himgF args w)
  have hcond : L.Cond κ M F h args w ∧ Arm.r .ERR (L.pcall M h (L.canon h args w)) = .None := by
    refine ⟨⟨hM, herrw, by rw [hsp]; exact halign, hroom', hdead', vals, cm, cs, rvals, cm',
      hmemR0, hargs, hsav, hplw, hinit, hret⟩, ?_⟩
    rw [hc_eq, r_set_program]; exact hc_ret.ret.err
  have hspT : spv (L.pcall M h (L.canon h args w)) = spv w := by
    rw [hc_eq]
    simp only [spv]
    rw [r_set_program]
    have := hc_ret.ret.sp
    simp only [spv] at this
    rw [this, r_enterAt _ _ (by simp) (by simp)]
    exact (L.callerOk_canon_return_pins hL hh himgF args w).world.1 _ (by simp [Masked])
  have hce := clifEntry_initState (f := h) hpf hinit
  have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm' (runInv_entry hh hce) hretN
  have hbot : cs.bottom = h := by simp [Clif.State.bottom,hce.callers,hce.func]
  rw [hbot] at hrt
  have sourceLength : rvals.length = h.sig.returns.length := by
    simpa only [List.length_map,Clif.AbiParam.tys] using congrArg List.length hrt
  have hlr : rvals.length ≤ (sigRets h.sig).length := by
    rw [sourceLength]
    exact returns_le_sigRets _
  have abiBound : (sigRets h.sig).length ≤ us.length := by
    cases sret : h.sig.params.any (·.purpose == .sret) with
    | true => exact hL.sretRets h hh sret us hrs
    | false =>
      rw [sigRets_of_noSret sret,← sourceLength,hlen]
      exact hhold.1
  have selected := ReturnPinMode.pins_prefix_of_valid hus abiBound
  have selectedLength : (modeReturnPins modes h).length = (sigRets h.sig).length := by
    change ((modes h).pins h (sigRets h.sig).length).length = _
    rw [selected,List.length_take,List.length_map,Nat.min_eq_left abiBound]
  refine ⟨_, _, by rw [progXMode,progXWithPins,if_pos hcond], ?_, ⟨by simpa only [List.length_map,selectedLength] using hlr, fun j v x hv hx => ?_⟩,
    ⟨⟨⟨fun a b hv hb => ?_, hmemR.valid, hmemR.symbols⟩, ?_, ?_⟩, ?_, hcond.2⟩⟩
  · rw [List.length_map,selectedLength]
  · -- the results
    have hjr : j < rvals.length := (List.getElem?_eq_some_iff.mp hv).1
    have hju : j < us.length := by have := hhold.1; omega
    have chosen : (modeReturnPins modes h)[j]? = some (us[j]'hju).2 := by
      change ((modes h).pins h (sigRets h.sig).length)[j]? = _
      rw [selected,List.getElem?_take,if_pos (by omega)]
      simp only [List.getElem?_map,List.getElem?_eq_getElem hju,Option.map_some]
    simp only [List.getElem?_map,chosen,Option.map_some,Option.some.injEq] at hx
    subst x
    have hus_j : us[j]? = some ((us[j]'hju).1,(us[j]'hju).2) :=
      List.getElem?_eq_getElem hju
    have hoj : outsV[j]? = some (outsV[j]'(by omega)) := List.getElem?_eq_getElem _
    rw [hc_eq, regVal_set_program, hc_ret.regs j _ _ _ hus_j hoj]
    exact hhold.2 j v _ hv hoj
  · -- the bytes of the live allocations
    rw [← hmemR.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [hc_eq, mem_set_program, hc_ret.mem _ (by simpa using (hmemR.valid a 1 hv).2 0 (by omega))]
  · simpa [Rel.slotReg, hspT] using hslot
  · -- the caller's outgoing area: the callee's run creates no allocation there
    by_cases hib0 : (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase = 0
    · rw [hib0]; exact outRel_zero _ _ _
    · refine ⟨hout.1, by rw [hspT]; exact hout.2.1, fun a n hv k hk j hj => ?_⟩
      rw [hspT]
      by_cases hN : L.NeedSlots
      · exact hout.2.2 a n (Clif.runLoop_allocs hL.free (hL.baseKeepsAllocs hN) Nr cs rvals cm'
          (runInv_entry hh hce) (Clif.initState_allocInv hinit) hretN a n hv) k hk j hj
      have hsl : h.slots = [] := Classical.byContradiction fun hne =>
        hN ⟨g, hg, h, hcallee, hne⟩
      obtain ⟨-, pl, hcs⟩ := initState_noSlots hpf hsl hinit
      have hv0 := runLoop_valid hL.free (hL.baseNoAlloc ⟨g, hg, hib0⟩) (L.slotFree hN) Nr
        cs rvals cm' (runInv_entry hh hce)
        (fun hkk => by
          have ⟨k0, hk0, hnk⟩ := hkk
          refine ⟨(hL.indScope k0 hk0 hnk).keep, fun h' hh' hs' => hL.addrSlots hN ⟨g, hg, hib0⟩ hkk h' hh' ?_⟩
          rw [hcs] at hs'; simpa [hmemR0.symbols] using hs') hretN a n hv
      rw [hcs] at hv0
      exact hout.2.2 a n hv0 k hk j hj
  · rw [hspT, hsp]
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem envOf_keeps_return_pins (hL : L.OkReturnPins modes) [hR : L.CrunOk] {M : Nat} {g : Clif.Function} {c : BitVec 64}
    (hk : Opt.EnvKeepsSymbols L.base) : Opt.EnvKeepsSymbols (L.envOf M g c) := by
  intro n G hG vals m rvals m' hr
  rcases L.envOf_some hG with ⟨hpf, hb⟩ | ⟨_, _, _, G0, h, hG0⟩
  · have hl : (Clif.linkEnvR L.P L.base (L.crun M)).extern n = some G := by
      rw [Clif.linkEnvR_none hpf]; exact hb
    exact Clif.linkEnvR_keeps (hR.runs M) hL.free hk n G hl vals m rvals m' hr
  · exact Clif.linkEnvR_keeps (hR.runs M) hL.free hk n G0 h vals m rvals m'
      (hG0 vals m rvals m' hr).2
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem xCallsOk_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsOk (L.envOf M g c) (g.externs.map (·.2))
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XMode modes κ M g F) := by
  intro ext hin gsem sl cm w d uses args vals rvals cm' hgs hd hargs hmr hret hrl
  rcases L.envOf_some hgs with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseX g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
      (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) gsem sl cm w d uses args vals rvals cm' hgs hd
      hargs hmr hret hrl
    refine ⟨outs, w', ?_, h1, h2, h3⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
    · rw [L.XMode_base hpf _ _ F]; exact hx
    · rw [L.XMode_none (by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
        rw [lo64_ofX]; exact (L.find_sym_return_pins hL ext.name).2 hpf)]
      exact hx
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hsig := hL.declSig g hg ext hin h hpf
    obtain ⟨hpl, hret⟩ := hG0 _ _ _ _ hret
    rw [Clif.linkEnvR_some hpf] at hgs
    cases hgs
    -- the callee's whole-program run
    simp only at hret
    cases hinit : Clif.initState L.P ext.name vals cm with
    | trap c' => rw [hinit] at hret; cases hret
    | stuck m' => rw [hinit] at hret; cases hret
    | ok cs =>
    rw [hinit] at hret
    simp only at hret
    rw [hsig] at hargs
    have hout := hmr.1.2.2
    have hsp := hmr.2.1
    -- the stack-passed arguments are in the caller's outgoing area, outside `F`
    have hsav : StackArgsAvoid F h.sig vals w := by
      intro off v hm k hk
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      rw [List.getElem?_zip_eq_some] at hi
      obtain ⟨hli, hvi⟩ := hi
      have hty := (clifEntry_initState (f := h) (by rw [hname]; exact hpf)
        (by rw [hname]; exact hinit)).sig
      obtain ⟨p, hp⟩ : ∃ p, h.sig.params[i]? = some p := by
        have := congrArg (·[i]?) hty
        simp only [List.getElem?_map, hvi, Option.map_some] at this
        cases hp : h.sig.params[i]? with
        | none => rw [hp] at this; cases this
        | some p => exact ⟨p, rfl⟩
      have hvp : v.ty = p.ty := by
        have := congrArg (·[i]?) hty
        simp only [List.getElem?_map, hvi, hp, Option.map_some, Option.some.injEq] at this
        exact this
      have hfit := hL.outFits g hg ext hin (by simp [hpf]) i off p (by rw [hsig]; exact hli)
        (by rw [hsig]; exact hp)
      rw [hvp] at hk
      rw [add_ofNat_add]
      have hav : Avoids F (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase (spv w) := hout.2.1
      exact hav (off + k) (by omega)
    rw [← hname] at hinit
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResult_return_pins hL hκ ih hg hh (.inr (.inl ⟨ext, hin, hpf⟩)) himgF hroom hdead halign hargs hsav
        hmr hpl hinit hret
    refine ⟨outs, w', ?_, by rw [hol, hsig], hho, hmr'⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hcol, rfl⟩
    · rw [L.XMode_prog hpf]; exact hx
    · have hs : symCallee L.Xb L.P (lo64 (ofX ((L.XMode modes κ M g F).sym ext.name 0))) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
        rw [lo64_ofX]; exact (L.find_sym_return_pins hL ext.name).1 h hpf
      have hto : L.IndTo g h := by
        refine ⟨by rw [hname]; exact hdecl, ?_⟩
        rcases hdecl with hdn | ⟨-, -, hall⟩
        · exact .inl ⟨by rw [hname]; exact hdn, ext, hin, hname.symm, hcol⟩
        · obtain ⟨sig, hs, hm⟩ := hall h hpf
          exact .inr ⟨sig, hs, hm, hm.returns_length⟩
      rw [L.XMode_ind hs, if_pos ⟨hto, argsAt_regLocs hargs⟩]
      exact hx
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem xCallsIndOk_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsIndOk (L.envOf M g c) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XMode modes κ M g F) := by
  intro sig hsig n gsem sl cm w u args vals rvals cm' hgs hsg hu hl8 hall hmr hret hrl hty
  rcases L.envOf_some hgs with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · have hs : symCallee L.Xb L.P (lo64 u) = none := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
      rw [hu]; exact (L.find_sym_return_pins hL n).2 hpf
    obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseXI g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hsig n gsem sl cm w u args vals rvals
      cm' hgs (fun _ h => nomatch h) hu hl8 hall hmr hret hrl hty
    exact ⟨outs, w', by rw [L.XMode_none hs]; exact hx, h1, h2, h3⟩
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    have hnf : ¬ Clif.IndFree g := fun hif => by
      rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
    have hdeclS := hL.indSig g hg hnf
    have hs : symCallee L.Xb L.P (lo64 u) = some h := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
      rw [hu]; exact (L.find_sym_return_pins hL h.name).1 h hpf
    obtain ⟨hpl, hret⟩ := hG0 _ _ _ _ hret
    rw [Clif.linkEnvR_some hpf] at hgs
    cases hgs
    simp only at hret
    cases hinit : Clif.initState L.P h.name vals cm with
    | trap c' => rw [hinit] at hret; cases hret
    | stuck m' => rw [hinit] at hret; cases hret
    | ok cs =>
    rw [hinit] at hret
    simp only at hret
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    -- the call site's signature matches `h`'s (`Clif.callExternAt` checks it against `sigOf`)
    have hm : IndSigMatch sig h :=
      hsg h.sig (by simp only [envOf, Clif.linkEnvR_sigOf, hpf, Option.map_some])
    obtain ⟨⟨bytes, hb, hb8⟩, hsr⟩ := hdeclS h hh hdecl (.inl ⟨sig, hsig, hm⟩)
    have hargs : ArgsAt h.sig vals args w := (argsAt_iff_of_regs hb hb8 hvl).mpr hall
    have hsav : StackArgsAvoid F h.sig vals w := by
      intro off v hm
      obtain ⟨r, hr⟩ := (locsOf_small hb hb8).2 _ (List.of_mem_zip hm).1
      cases hr
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResult_return_pins hL hκ ih hg hh (.inr (.inr ⟨hh, hdecl⟩)) himgF hroom hdead halign hargs hsav
        hmr hpl hinit hret
    refine ⟨outs, w', ?_, ?_, hho, hmr'⟩
    · rw [L.XMode_ind hs, if_pos ⟨⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩,
        argsAt_regLocs hargs⟩]
      exact hx
    · rw [hol]
      exact hsr sig hsig hm.ty hm.returns_length
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem regVal_canon_eq_return_pins (hL : L.OkReturnPins modes) {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hlen : args.length = (regLocs h.sig).length) (w w' : Arm.ArmState) :
    ∀ r ∈ regLocs h.sig, regVal (L.canon h args w') r = regVal (L.canon h args w) r := by
  intro r hr
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  have hjl : j < args.length := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
  rw [L.regVal_canon _ _ _ (harg r hr), L.regVal_canon _ _ _ (harg r hr),
    placeArgs_regVal _ _ _ hnd harg hj (List.getElem?_eq_getElem hjl),
    placeArgs_regVal _ _ _ hnd harg hj (List.getElem?_eq_getElem hjl)]
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem progX_ni_return_pins (hL : L.OkReturnPins modes) [hR : L.CrunOk] (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1))
    {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F Z : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (hFZ : ∀ a, F a → Z a) {w w' : Arm.ArmState}
    (hsw : SameWorld Z w w') {cm : Clif.Mem} {vals : List Clif.Val} {args : List CV}
    (hm : MemRel F L.syms cm w) (hm' : MemRel F L.syms cm w') (ha : ArgsAt h.sig vals args w)
    (ha' : ArgsAt h.sig vals args w') {cs : Clif.State} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hpl : L.NeedSlots → L.PlaceAt cm (spv w)) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm') {o o' : List CV}
    {x x' : Arm.ArmState} (hx : L.progXMode modes κ M F h args w = some (o, x))
    (hx' : L.progXMode modes κ M F h args w' = some (o', x')) : o = o' ∧ SameWorld Z x x' := by
  have hpf := func?_of_mem hL.names hh
  unfold progXMode progXWithPins at hx hx'
  split at hx
  case isFalse => cases hx
  rename_i hc
  split at hx'
  case isFalse => cases hx'
  simp only [Option.some.injEq, Prod.mk.injEq] at hx hx'
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨rfl, rfl⟩ := hx'
  obtain ⟨⟨hM, herr, hal, hroom, hdead, vals1, cm1, cs1, rvals1, cm1', -, -, hsav1, -, hinit1, -⟩,
    -⟩ :=
    hc
  have hty : vals.map (·.ty) = vals1.map (·.ty) := by
    rw [(clifEntry_initState hpf hinit).sig, (clifEntry_initState hpf hinit1).sig]
  have hsav := stackArgsAvoid_tys hsav1 hty
  obtain ⟨us, outs, wf, hus, hlen, hhold, -, hrs, hall, hni⟩ :=
    L.progCall_return_pins hL hM (ih hM) hpf ⟨g, hg, hcallee⟩ (.inr hN) himgF herr hal hroom hdead hm ha
      hsav hpl hinit hrun
  have hc0 := L.callerOk_canon_return_pins hL hh himgF args w
  have hc1 := L.callerOk_canon_return_pins hL hh himgF args w'
  have hsp' : spv w' = spv w := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨k, heq, hret⟩ := hall _ hc0
  obtain ⟨k', heq', hret'⟩ := hni hN Z (L.canon h args w') hFZ
    ((SameWorld.mono hFZ hc1.world).trans hsw.symm) hc1.img
    (L.regVal_canon_eq_return_pins hL hh (argsAt_regLocs ha) w w') hc1.ra (L.memRel_canon himgF hm' h args)
    (fun off v hmz j hj => by
      rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmz j hj (himgF _ hi))]
      exact stackArgs_bytes ha.2.2 ha'.2.2 hsp' off v hmz j hj)
  -- the callee's ABI results are among the defs of its return site
  have hsr : (sigRets h.sig).length ≤ us.length := by
    cases hs : h.sig.params.any (·.purpose == .sret)
    · have hce := clifEntry_initState hpf hinit
      obtain ⟨Nr, hrunN⟩ := hR.runs M cs _ hrun (.inl ⟨_, _, rfl⟩)
      have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm' (runInv_entry hh hce) hrunN
      have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
      rw [hbot] at hrt
      have e := congrArg List.length hrt
      simp only [List.length_map, Clif.AbiParam.tys] at e
      rw [sigRets_of_noSret hs, ← e]
      have := hhold.1
      omega
    · exact hL.sretRets h hh hs us hrs
  refine ⟨?_,?_⟩
  · apply List.map_congr_left
    intro pin member
    have returnedPin : pin ∈ us.map (·.2) := by
      have selected := ReturnPinMode.pins_prefix_of_valid hus hsr
      change pin ∈ (modes h).pins h (sigRets h.sig).length at member
      rw [selected] at member
      exact List.mem_of_mem_take member
    rw [heq,heq',regVal_set_program,regVal_set_program]
    exact hret.pins_agree hret' hlen pin returnedPin
  · rw [heq, heq']
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · rw [r_set_program, r_set_program]
      by_cases h29 : f = .GPR 29#5
      · subst h29
        have e1 := hret.ret.savedX 29 (by unfold calleeSavedX; decide)
        have e2 := hret'.ret.savedX 29 (by unfold calleeSavedX; decide)
        simp only [xreg] at e1 e2
        rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hc0.world.1 _ hf, hc1.world.1 _ hf, hsw.1 _ hf]
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hret.ret.sp
        have e2 := hret'.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hc0.world.1 _ hf, hc1.world.1 _ hf, hsw.1 _ hf]
      rw [hret.fields f hf h29 h31, hret'.fields f hf h29 h31]
    · rw [mem_set_program, mem_set_program, hret.mem a (fun hf => ha (hFZ a hf)), hret'.mem a ha]
    · rw [program_set_program, program_set_program, L.program_canon, L.program_canon]
      exact hsw.2.2
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem xni_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (c : BitVec 64) :
    XNI F L.syms (g.externs.map (·.2)) (indSigs g) c
      (CallLg (L.envOf M g c) (g.externs.map (·.2)) (indSigs g)) (L.XMode modes κ M g F) := by
  intro n sig vals cm args d uses Z w w' o x o' x' hlg hd hFZ hsw hm hm' hc1 hc2 hA hx hx'
  obtain ⟨hkind, G, rv, cm'', hG, hGo⟩ := hlg
  rcases L.envOf_some hG with ⟨hpf, hb⟩ | ⟨h, hpf, hdecl, G0, hGl, hG0⟩
  · have hbase := hL.baseNI hN g hg F c n sig vals cm args d uses Z w w' o x o' x'
      ⟨hpf, hkind, G, rv, cm'', hb, hGo⟩ hd hFZ hsw hm hm' hc1 hc2 hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XMode_base hpf] at hx hx'
      exact hbase hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hu]; exact (L.find_sym_return_pins hL n).2 hpf
      rw [L.XMode_none hs] at hx hx'
      exact hbase hx hx'
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    obtain ⟨hpl, hGo⟩ := hG0 _ _ _ _ hGo
    have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hS => hc1 ▸ hpl hS
    rw [Clif.linkEnvR_some hpf] at hGl
    cases hGl
    simp only at hGo
    cases hinit : Clif.initState L.P h.name vals cm with
    | trap c' => rw [hinit] at hGo; cases hGo
    | stuck m' => rw [hinit] at hGo; cases hGo
    | ok cs =>
    rw [hinit] at hGo
    simp only at hGo
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    have hcallee : L.Callee g h := .inr (.inr ⟨hh, hdecl⟩)
    have hAA : ArgsAt h.sig vals args w ∧ ArgsAt h.sig vals args w' := by
      rcases hA with ⟨⟨e', he', hen', hes⟩, h1, h2⟩ | ⟨hsig, h8, hall⟩
      · have := hL.declSig g hg e' he' h (by rw [hen']; exact hpf)
        rw [← hes, this] at h1 h2
        exact ⟨h1, h2⟩
      · have hnf : ¬ Clif.IndFree g := fun hif => by
          rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
        have hdeclS := hL.indSig g hg hnf
        -- the call entered `h`: its parameter types are the call's signature's
        have hmatch : IndTyMatch sig h := by
          rcases hkind with ⟨e', he', hen', hes⟩ | ⟨-, hty⟩
          · have := hL.declSig g hg e' he' h (by rw [hen']; exact hpf)
            rw [← hes, this]
            rfl
          · exact hce.sig.symm.trans hty
        obtain ⟨⟨bytes, hb, hb8⟩, -⟩ := hdeclS h hh hdecl (L.indReach hpf hdecl hsig hmatch)
        exact ⟨(argsAt_iff_of_regs hb hb8 hvl).mpr hall, (argsAt_iff_of_regs hb hb8 hvl).mpr hall⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XMode_prog hpf] at hx hx'
      exact L.progX_ni_return_pins hL hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit hGo hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
        rw [hu]; exact (L.find_sym_return_pins hL h.name).1 h hpf
      rw [L.XMode_ind hs] at hx hx'
      split at hx
      · rename_i hif
        rw [if_pos hif] at hx'
        exact L.progX_ni_return_pins hL hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit hGo hx
          hx'
      · cases hx
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem xTls_return_pins (hL : L.OkReturnPins modes) (hN : L.NeedNI) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} :
    XTls F (L.XMode modes κ M g F) :=
  fun Z n w w' hFZ hsw => hL.baseTlsNI hN F Z n w w' hFZ hsw
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}


end LinkSys
end E2E
