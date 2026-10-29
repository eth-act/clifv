import FV.E2E.LinkArmUCallNI

/-!
# The callee contracts of the linked machine with unwinding (S10f, #233)

`LinkSys.progOsCore`/`progOs`/`progOsReg`/`calleeOk`/`calleeTryOk` (`FV/E2E/LinkArm.lean`) for
the linked machine with unwinding (without non-interference), and the raising callees' contract
`CalleeUnwOkG` of an activation: at a call of a function of `P` whose external semantics raises
(`XRU`: the callee run ends `unwound`), the linked machine's raise (`UU`) is the canonical one up
to the world (`progRaiseCoreU`); at a call whose external semantics returns, the linked machine's
callee does not raise (`progOsCoreU`); at a base call site the base's contracts (`OkU.baseUnw`,
`OkU.baseNoRaise`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## What an ABI return keeps -/

/-- An ABI return from a callee entered at `enterAt a t` keeps the allocatable registers outside
the default clobbers and the callee-saved part of the callee-saved registers of `t`. -/
theorem keep_of_armRet {a : Art} {t rs : Arm.ArmState} {ra : BitVec 64}
    (h : ArmRet ra (enterAt a t) rs) :
    (∀ r, r.allocatable = true → r ∉ defaultAapcsClobbers → regVal rs r = regVal t r) ∧
    (∀ r ∈ calleeSaved, ckeep r (regVal rs r) = ckeep r (regVal t r)) := by
  have hx : ∀ m, 19 ≤ m → m < 29 → regVal rs (.x m) = regVal t (.x m) := by
    intro m h19 h29
    have e := h.savedX m (by simp [calleeSavedX]; exact ⟨m - 19, by omega, by omega⟩)
    simp only [xreg] at e
    simp only [regVal]
    rw [show rnum m = BitVec.ofNat 5 m from rfl, e, r_enterAt _ _ (by simp) (fun e' => by
      have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e'
      simp at this; omega)]
  refine ⟨fun r hr hnD => ?_, fun r hcs => ?_⟩
  · rcases allocatable_cases hr with ⟨m, rfl, hm, h16, h17, h18⟩ | ⟨m, rfl, hm⟩
    · have h19 : 19 ≤ m :=
        Classical.byContradiction fun hc => hnD (by simp [defaultAapcsClobbers]; omega)
      exact hx m h19 (by omega)
    · exact absurd (by simp [defaultAapcsClobbers]; omega) hnD
  · simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hcs
    rcases hcs with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · simp only [ckeep]
      exact hx (19 + i) (by omega) (by omega)
    · have e := h.savedV (8 + i) (by omega) (by omega)
      simp only [ckeep, regVal]
      rw [show rnum (8 + i) = BitVec.ofNat 5 (8 + i) from rfl, e,
        r_enterAt _ _ (by simp) (by simp)]

/-- A register no def of the call writes and the call (or `try_call`) does not clobber is not a
default AAPCS clobber. -/
theorem notDefault_of {info : CallInfo} {i : MInst}
    (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti) {Ld : List (Reg × Nat)}
    (hdefs0 : info.defs = callDefs Ld) {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {r : Reg} (hnd' : ∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r)
    (hnc : r ∉ i.clobbers) : r ∉ defaultAapcsClobbers := by
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
  have hnany : ∀ l : List Reg, r ∈ l → r ∈ l.filter (fun r => !(info.defs.any (·.1 == r))) := by
    intro l hl
    simp only [List.mem_filter, hl, true_and, hdefs0, callDefs]
    simp only [List.any_map, Bool.not_eq_true', List.any_eq_false]
    exact fun q hq e => hnotd (List.mem_map.mpr ⟨q, hq, by simpa using e⟩)
  intro hm
  apply hnc
  rcases hi with rfl | ⟨ti, rfl⟩
  · simp only [MInst.clobbers]
    exact hnany _ hm
  · simp only [MInst.clobbers]
    apply hnany
    cases ti.clobberAll
    · simpa using hm
    · simp only [defaultAapcsClobbers, List.mem_append, List.mem_map, List.mem_range] at hm
      simp only [↓reduceIte, allClobbers, List.mem_append, List.mem_map, List.mem_range]
      rcases hm with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact .inl ⟨j, by omega, rfl⟩
      · exact .inr ⟨j, hj, rfl⟩

/-- **Two returns related to one world give worlds that agree**: from caller states `t` and `c`
agreeing with `w` outside `F`, two ABI returns of a callee entered there whose memory outside `F`
and unmasked fields but x29/`sp` are a world `wf`'s are the same world outside `F`. -/
theorem sameWorld_ends {a : Art} {F : BitVec 64 → Prop} {t c w rs rc wf : Arm.ArmState}
    (ht : SameWorld F t w) (hc : SameWorld F c w)
    (rts : ArmRet (Arm.r .PC t + 4) (enterAt a t) rs)
    (rtc : ArmRet (Arm.r .PC c + 4) (enterAt a c) rc)
    (ms : ∀ x, ¬ F x → rs.mem x = wf.mem x) (mc : ∀ x, ¬ F x → rc.mem x = wf.mem x)
    (fs : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f rs = Arm.r f wf)
    (fc : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f rc = Arm.r f wf) :
    SameWorld F (Arm.set_program rs t.program) (Arm.set_program rc c.program) := by
  refine ⟨fun f hf => ?_, fun x hx => ?_, ?_⟩
  · rw [r_set_program, r_set_program]
    by_cases h29 : f = .GPR 29#5
    · subst h29
      have e1 := rts.savedX 29 (by decide)
      have e2 := rtc.savedX 29 (by decide)
      simp only [xreg] at e1 e2
      rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
      rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
        hc.1 _ hf, ht.1 _ hf]
    by_cases h31 : f = .GPR 31#5
    · subst h31
      have e1 := rts.sp
      have e2 := rtc.sp
      simp only [spv] at e1 e2
      rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
        hc.1 _ hf, ht.1 _ hf]
    · rw [fs f hf h29 h31, fc f hf h29 h31]
  · simp only [mem_set_program]
    rw [ms x hx, mc x hx]
  · simp only [program_set_program]
    rw [ht.2.2, hc.2.2]

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- The callee's results world keeps the caller's frame outside the dead stack. -/
theorem frameKeep_end {a : Art} {t rs w : Arm.ArmState} {F : BitVec 64 → Prop} {K D : Nat}
    (hDK : D ≤ K) (hsp : spv w = spOf t)
    (rts : ArmRet (Arm.r .PC t + 4) (enterAt a t) rs)
    (hgk : ∀ x, (F x ∧ ¬ StackBelow D (spv w) x) → rs.mem x = (enterAt a t).mem x) :
    FrameKeep (fun x => F x ∧ ¬ StackBelow K (spOf t) x) t (Arm.set_program rs t.program) := by
  refine ⟨?_, fun x ⟨ha, hb⟩ => ?_, ?_⟩
  · show spv (Arm.set_program _ _) = spv t
    simp only [spv]; rw [r_set_program]
    have := rts.sp
    simp only [spv] at this
    rw [this, r_enterAt _ _ (by simp) (by simp)]
  · rw [mem_set_program, hgk x ⟨ha, fun hb' => hb ?_⟩, mem_enterAt]
    rw [hsp] at hb'
    exact stackBelow_mono hb' hDK
  · rw [r_set_program]
    exact (rts.savedX 29 (by simp [calleeSavedX]; exact ⟨10, by omega, rfl⟩)).trans
      (r_enterAt _ _ (by simp) (by simp))

/-- **The core of the operand-view obligation of a call of the function `h` of `P`** on the
linked machine with unwinding at depth `M` (`progOsCore`'s counterpart): from a caller state `t`
whose arguments are in `h`'s parameter registers, the linked call gives `progXU`'s results and
world, and the callee does not raise. -/
theorem progOsCoreU (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX]
    (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs) (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {o outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : L.progXU κ M F h (Lu.map (fun q => regVal t q.2)) w = some (o, w'))
    (houts : ∃ n, outs = o.take n) :
    SameWorld F (L.pcallU M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcallU M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcallU M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcallU M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcallU M h t) r) = ckeep r (regVal t r)) ∧
      L.praiseU M h t = none := by
  have hpf := func?_of_mem hL.names hh
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lu.map (fun q => regVal t q.2) = uses at hx
  unfold progXU at hx
  have hcond : L.CondU κ M F h uses w ∧
      Arm.r .ERR (L.pcallU M h (L.canon h uses w)) = .None :=
    Classical.byContradiction fun hc => by rw [if_neg hc] at hx; cases hx
  rw [if_pos hcond] at hx
  obtain ⟨⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, hmr, hargs, hsav, hpl, hinit, rvals, cm',
    hrun⟩, -⟩ := hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hbud : frameDrop (L.A h).af + κ M' h ≤ κ (M' + 1) g := L.budget_step hκ hM hg hcallee
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, hrs, hcall, -⟩ :=
    (L.progCallUN hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herrw halw hroom hdead hmr
      hargs hsav hpl hinit).1 rvals cm' hrun
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
  have hcOkC := L.callerOk_canon hL hh himgF uses w
  obtain ⟨ks, hs_eq, hs_none, hs_ret⟩ := hcall t hcOk
  obtain ⟨kc, hc_eq, -, hc_ret⟩ := hcall _ hcOkC
  have hkeep := keep_of_armRet hs_ret.ret
  refine ⟨?_, ?_, ?_, fun r hr hnd' hnc => ?_, fun r _ hcs => ?_, hs_none⟩
  · rw [hs_eq, hc_eq]
    exact sameWorld_ends hsw hcOkC.world hs_ret.ret hc_ret.ret hs_ret.mem hc_ret.mem
      hs_ret.fields hc_ret.fields
  · rw [hs_eq]
    exact frameKeep_end hbud (hsw.1 (.GPR 31#5) (by simp [Masked])).symm hs_ret.ret hs_ret.gkeep
  · -- the results
    intro p hp
    obtain ⟨⟨op, r⟩, x⟩ := p
    rw [defRegs] at hp
    obtain ⟨n, rfl⟩ := houts
    replace hp := LinkSys.mem_zip_of_mem_zip_take hp
    rw [hdefs] at hp
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
    simp only [List.getElem?_zip_eq_some] at hj
    obtain ⟨⟨-, hr⟩, hx⟩ := hj
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨j2, hj2, rfl⟩ := hx
    have hjr' : j < h.sig.returns.length := by
      have := (List.getElem?_eq_some_iff.mp hj2).1; simpa using this
    have hjr : j < (sigRets h.sig).length := Nat.lt_of_lt_of_le hjr' (returns_le_sigRets _)
    have hjL : j < Ld.length := by
      have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    have e : ((Ld.map (·.1)).take (sigRets h.sig).length)[j]? = (Ld.map (·.1))[j]? := by
      rw [List.getElem?_take]; simp [hjr]
    rw [← e, hLd] at hr
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hr
    obtain ⟨j1, hj1, rfl⟩ := hr
    rw [List.getElem?_range (by omega : j < min (sigRets h.sig).length Ld.length),
      Option.some.injEq] at hj1
    rw [List.getElem?_range hjr', Option.some.injEq] at hj2
    subst hj1 hj2
    show regVal _ (Reg.x j) = regVal _ (Reg.x j)
    rw [hs_eq, regVal_set_program, hc_eq, regVal_set_program]
    -- the `j`-th result register is a return register of the callee
    obtain ⟨Nr, hrunN⟩ := hR.runs (M' + 1) cs _ hrun (.inl ⟨_, _, rfl⟩)
    have hrt := Clif.runLoopX_returned_tys hL.free Nr cs.toX rvals cm'
      (Clif.initState_xinv hinit) hrunN
    have hbot : cs.toX.s.bottom = h := by
      have hce := clifEntry_initState (f := h) hpf hinit
      simp [Clif.State.toX, Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have hrl : rvals.length = h.sig.returns.length := by
      have := congrArg List.length hrt
      simpa only [List.length_map, Clif.AbiParam.tys] using this
    have hju : j < us.length := by have := hhold.1; omega
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq, retX_lt (hrl ▸ hjr')] at this
      rw [List.getElem?_eq_getElem hju, ← this]
    have hoj : outsV[j]? = some (outsV[j]'(by omega)) := List.getElem?_eq_getElem _
    rw [hs_ret.regs j _ _ _ hus_j hoj, hc_ret.regs j _ _ _ hus_j hoj]
  · rw [hs_eq, regVal_set_program]
    exact hkeep.1 r hr (notDefault_of (.inl rfl) hdefs0 hdefs hnd' hnc)
  · rw [hs_eq, regVal_set_program]
    exact hkeep.2 r hcs

/-- **The core of the raising callees' obligation at a call of the function `h` of `P`** on the
linked machine with unwinding at depth `M`: from a caller state `t` whose arguments are in `h`'s
parameter registers, where the external semantics raises (`progXR`: the callee run ends
`unwound`), the linked machine's callee raises the same object, the unwinder's state at the call
in `progXR`'s world (outside `F`), keeping the frame, the program, the allocatable registers
outside the default clobbers and the callee-saved registers. -/
theorem progRaiseCoreU (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX]
    (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs) (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig)
    {t w w' : Arm.ArmState} {obj : BitVec 64}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : L.progXR κ M F h (Lu.map (fun q => regVal t q.2)) w = some (obj, w')) :
    ∃ t', L.praiseU M h t = some (obj, t') ∧ SameWorld F t' w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t t' ∧
      Arm.r .ERR t' = .None ∧ t'.program = t.program ∧
      (∀ r, r.allocatable = true → r ∉ defaultAapcsClobbers → regVal t' r = regVal t r) ∧
      (∀ r ∈ calleeSaved, ckeep r (regVal t' r) = ckeep r (regVal t r)) := by
  have hpf := func?_of_mem hL.names hh
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lu.map (fun q => regVal t q.2) = uses at hx
  obtain ⟨hcond, hpr, -, -, -⟩ := L.progXR_ext hx
  obtain ⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, hmr, hargs, hsav, hpl, hinit, e, cm',
    hrun⟩ := hcond
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hbud : frameDrop (L.A h).af + κ M' h ≤ κ (M' + 1) g := L.budget_step hκ hM hg hcallee
  obtain ⟨obj0, wf, -, -, hall, -⟩ :=
    (L.progCallUN hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herrw halw hroom hdead hmr
      hargs hsav hpl hinit).2 e cm' hrun
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
  have hcOkC := L.callerOk_canon hL hh himgF uses w
  obtain ⟨ks, hs_eq, hs_ret⟩ := hall t hcOk
  obtain ⟨kc, hc_eq, hc_ret⟩ := hall _ hcOkC
  rw [hc_eq, Option.some.injEq, Prod.mk.injEq] at hpr
  obtain ⟨rfl, rfl⟩ := hpr
  have hkeep := keep_of_armRet hs_ret.ret
  refine ⟨_, by rw [hs_eq, hs_ret.x0, hc_ret.x0], sameWorld_ends hsw hcOkC.world hs_ret.ret
    hc_ret.ret hs_ret.mem hc_ret.mem hs_ret.fields hc_ret.fields,
    frameKeep_end hbud (hsw.1 (.GPR 31#5) (by simp [Masked])).symm hs_ret.ret hs_ret.gkeep,
    by rw [r_set_program]; exact hs_ret.ret.err, by simp, fun r hr hnD => ?_, fun r hcs => ?_⟩
  · rw [regVal_set_program]; exact hkeep.1 r hr hnD
  · rw [regVal_set_program]; exact hkeep.2 r hcs

end LinkSysU

/-! ## The call sites -/

/-- A `call` or the call of a `try_call`: the plain call's operands and allocated form. -/
theorem callOrTry_call {info : CallInfo} {i : MInst}
    (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti) {ops : Array Operand} {regs : Array Reg}
    {i' : MInst} (hops : i.operands = .ok ops) (hasg : i.assign regs = .ok i')
    {fa : FnAsm} {base pc : BitVec 64} (hP : CallAt fa base pc i') :
    (MInst.call info).operands = .ok ops ∧
      ∃ ic, (MInst.call info).assign regs = .ok (.call ic) ∧ CallAt fa base pc (.call ic) := by
  rcases hi with rfl | ⟨ti, rfl⟩
  · obtain ⟨ic, rfl⟩ := assign_call_form hasg
    exact ⟨hops, ic, hasg, hP⟩
  · obtain ⟨ic, rfl, hc⟩ := (assign_call_tryCall info regs).2 ti i' hasg
    exact ⟨by rw [← operands_tryCall_call info ti]; exact hops, ic, hc, callAt_tryCall_call hP⟩

theorem callDest_sym {n : String} {us ds : List (Reg × Reg)} :
    callDest ⟨.sym n, us, ds⟩ = some n := rfl

theorem callDest_reg {r : Reg} {us ds : List (Reg × Reg)} :
    callDest ⟨.reg r, us, ds⟩ = none := rfl

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- **A `bl` site of `g` calling the function `h` of `P`**: the call's register operands are `h`'s
parameter registers and its results' registers x0.., its uses the parameter registers' values, its
return address one `h` may return to (`RaOk`). -/
theorem symSite (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {info : CallInfo}
    (hsite : (L.A g).vcp.CallSite info) {n : String} {h : Clif.Function} (hd : info.dest = .sym n)
    (hpf : L.P.func? n = some h) {i : MInst} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    {pc : BitVec 64} (hops : i.operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') (hP : CallAt (L.A g).fa (L.A g).base pc i') :
    ∃ Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h.sig ∧
      (Ld.map (·.1)).take (sigRets h.sig).length =
        (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x ∧
      (∀ s, useVals ops regs s = Lu.map (fun q => regVal s q.2)) ∧
      ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)) ∧
      RaOk (L.A h) pc := by
  have hps : L.ProgSite g info h := ⟨hsite, n, hd, hpf⟩
  obtain ⟨n', Lu, Ld, hinfo, hLu, hLd⟩ := hL.callRegs g hg info h hps
  obtain ⟨hopsC, ic, -, hPc⟩ := callOrTry_call hi hops hasg hP
  subst hinfo
  cases hd
  rw [operands_call_sym] at hopsC
  cases hopsC
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  exact ⟨Lu, Ld, rfl, hLu, hLd, fun s => call_useVals hregs s, call_defs hregs,
    hL.raCall g hg _ h hps _ hPc.callPc⟩

/-- **A `blr` site of `g`**: its target register (an allocatable X register) holds the machine's
`blr` target, its register operands are the parameter registers of every function of `P` it may
enter (`BlrTo`) with as many register parameters and its results' registers x0... -/
theorem regSite (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {info : CallInfo}
    (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n) {i : MInst}
    (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    {t s0 : Arm.ArmState} {G : BitVec 64 → Prop} (hops : i.operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') (hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC t) i')
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    (hG : ∀ a, G a → t.mem a = s0.mem a) :
    ∃ tv Lu Ld n0, info = ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩ ∧
      ops = (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray ∧
      (∀ h ∈ L.P.funcs, L.BlrTo g tv h → (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x) ∧
      useVals ops regs t = regVal t (.x n0) :: Lu.map (fun q => regVal t q.2) ∧
      ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)) ∧
      blrTarget t = some (lo64 (regVal t (.x n0))) ∧
      CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) := by
  obtain ⟨tv, Lu, Ld, hinfo, hregs⟩ := hL.blrRegs g hg info hsite hreg
  obtain ⟨hopsC, ic, hasgC, hPc⟩ := callOrTry_call hi hops hasg hP
  subst hinfo
  rw [operands_call_reg] at hopsC
  cases hopsC
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
    have hmem : (tgtOp tv, Loc.reg r0) ∈
        (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
      simp [Array.toList_zip, Array.toList_map, hregs0]
    obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
    exact ⟨n, hn, h29, h16⟩
  obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasgC
  cases hic
  have h0 : regs[0]? = some (.x n0) := by
    rw [← Array.getElem?_toList, hregs0]; rfl
  rw [h0] at hr1
  cases hr1
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hPc
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rw [lo64_regVal_x]
    exact blrTarget_of hc.layout hlm hj hn0 hpc
      (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (himgG a ha)).trans (himgS a ha)) k wd hk)
  exact ⟨tv, Lu, Ld, n0, rfl, rfl, hregs, call_useVals_reg hregs0 t, call_defs_reg hregs0, htgt,
    hPc.callPc⟩

/-- The target of a `blr` through the GOT entry of `n` that is a function of `P` is `n`'s
(`gotGuard`). -/
theorem got_of_guard (hL : L.Ok) {g : Clif.Function} {tv : Nat} {Lu : List (Nat × Reg)}
    {Ld : List (Reg × Nat)} {X : ExtSem} (hX : X.sym = L.Xb.sym) {regs : Array Reg}
    {t : Arm.ArmState} {n0 : Nat} {h : Clif.Function}
    (hguard : gotGuard (GotV (L.A g).vcp) X ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩
      (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t))
    (huv : useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t =
      regVal t (.x n0) :: Lu.map (fun q => regVal t q.2))
    (hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) = some h) :
    ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
  intro n hn
  have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
  rw [huv] at e
  simp only [List.head?_cons, Option.map_some, Option.some.injEq, hX] at e
  exact L.toLinkSys.got_target hL hs e

/-- **The operand-view obligation of a `bl` call of a function of `P`** on the linked machine
with unwinding at depth `M` (`progOs`'s counterpart). -/
theorem progOsU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooksU M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XU κ M g F)) (.call info) .next := by
  have ⟨hsite', n, hdest, hpf⟩ := hsite
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  replace hsem := csemV_sub hsem
  obtain ⟨Lu, Ld, rfl, hLu, hLd, huv, hdefs, hra⟩ :=
    L.symSite hL hg hsite' hdest hpf (.inl rfl) hops hst hasg hP
  rw [huv] at hsem
  obtain ⟨o, hx, hout⟩ : ∃ o, L.progXU κ M F h (Lu.map (fun q => regVal t q.2)) w = some (o, w') ∧
      outs = o.take (callDefs Ld).length := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.XU_prog hpf] at hx
    exact ⟨o, hx, rfl⟩
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := L.progOsCoreU hL hU hκ ih hg hh (.inl ⟨_, hsite⟩) himgF
    himgG himgS hLu hLd (info := ⟨.sym n, retPairs Lu, callDefs Ld⟩) rfl hdefs hK hG hra hsw hx
    ⟨_, hout⟩
  exact ⟨L.pcallU M h t, by simp only [callExec, hal, ↓reduceIte, L.hooksU_some hpf],
    a1, a2, a3, a4, a5⟩

/-- **The operand-view obligation of a `blr` call** on the linked machine with unwinding at depth
`M` (`progOsReg`'s counterpart). -/
theorem progOsRegU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooksU M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XU κ M g F)) (.call info) .next := by
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  have hguard := csemV_guard hsem
  replace hsem := csemV_sub hsem
  have hops0 := hops
  have hst0 := hst
  have hasg0 := hasg
  obtain ⟨tv, Lu, Ld, n0, rfl, rfl, hregs, huv, hdefs, htgt, hcpc⟩ :=
    L.regSite hL hg hsite hreg (.inl rfl) hops hst hasg hP himgG himgS hG
  obtain ⟨o, hx, hout⟩ : ∃ o, (L.XU κ M g F).call none (regVal t (.x n0) :: Lu.map (fun q => regVal t q.2)) w =
      some (o, w') ∧ outs = o.take (callDefs Ld).length := by
    rw [huv] at hsem
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    exact ⟨o, hx, rfl⟩
  obtain ⟨r1, us', ds', -, rfl⟩ := assign_call_reg hasg
  cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
  | none =>
    have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
    rw [L.XU_none hs] at hx
    have hsem' : csem F ctx L.Xb (.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩)
        (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
        some (outs, w', .next) := by
      rw [huv, hout]; simp [csem, hx]
    obtain ⟨s', hex, rest⟩ := hL.baseOs g hg _ hsite (.inl rfl) F (κ M g) G s0
      (CallAt (L.A g).fa (L.A g).base) ctx t hK hD hG c wh _ regs _ w outs w' hops0 hst0 hasg0 hP
      hsw hal herr hsem'
    refine ⟨s', ?_, rest⟩
    simp only [callExec] at hex ⊢
    rw [L.hooksU_base (.inl rfl) t (fun _ => hb)]
    exact hex
  | some h =>
    rw [L.XU_ind hs] at hx
    split at hx
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
        rw [huv] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.toLinkSys.got_target hL hs e
      obtain ⟨hLu, hLd⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
      obtain ⟨a1, a2, a3, a4, a5, -⟩ := L.progOsCoreU hL hU hκ ih hg hh
        (.inr (.inr ⟨hh, hdecl.1.1⟩)) himgF himgG himgS hLu hLd
        (info := ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩) rfl hdefs hK hG
        (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hcpc) hsw hx ⟨_, hout⟩
      exact ⟨L.pcallU M h t, by simp only [callExec, hal, ↓reduceIte, L.hooksU_none hb],
        a1, a2, a3, a4, a5⟩
    · cases hx

/-- **The callee contract of the linked machine with unwinding at depth `M`** for an activation of
`g` (`calleeOk`'s counterpart). -/
theorem calleeOkU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XU κ M g F) (L.hooksU M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) where
  os ctx info hsite := by
    cases hd : info.dest with
    | reg r =>
      exact L.progOsRegU hL hU hκ ih hg he.imgF he.imgG he.imgS hsite
        (fun n => by rw [hd]; simp) ctx
    | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact L.progOsU hL hU hκ ih hg he.imgF he.imgG he.imgS ⟨hsite, n, hdest, hpf⟩ ctx
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      have h0 := hL.baseOs g hg info hsite hb F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) ctx
      intro t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.call ⟨.sym n, us, ds⟩) (useVals ops regs t) w =
          some (outs, w', .next) := by
        rw [← csemV_sub hsem]; simp [csem, L.XU_base hpf _ _ F]
      obtain ⟨s', hex, rest⟩ :=
        h0 t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem'
      refine ⟨s', ?_, rest⟩
      obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
      simp only [callExec] at hex ⊢
      rw [L.hooksU_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
      exact hex
  pc d u herr hal := by
    cases d with
    | none =>
      cases hb : (blrTarget u).bind (symCallee L.Xb L.P) with
      | none =>
        rw [L.hooksU_base (.inl rfl) u (fun _ => hb)]; exact hL.basePc _ _ (.inl rfl) herr hal
      | some h => rw [L.hooksU_none hb]; exact (L.pcallU_pc M h u).2
    | some n =>
      cases hpf : L.P.func? n with
      | none =>
        rw [L.hooksU_base (.inr ⟨n, rfl, hpf⟩) u (fun h => by cases h)]
        exact hL.basePc _ _ (.inr ⟨n, rfl, hpf⟩) herr hal
      | some h => rw [L.hooksU_some hpf]; exact (L.pcallU_pc M h u).2
  ext _ _ _ _ _ hx herr := L.XU_ext hL hx herr

/-- **The `try_call` contract of the linked machine with unwinding at depth `M`**
(`calleeTryOk`'s counterpart). -/
theorem calleeTryOkU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeTryOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XU κ M g F) (L.hooksU M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  intro ctx info ti hsite
  cases hd : info.dest with
  | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact calleeTryOkG_of_call (S := fun i t => i = info ∧ t = ti)
        (fun ctx' i t ⟨e1, _⟩ => e1 ▸ (L.calleeOkU hL hU hκ ih hg he).os ctx' info
          hsite.callSite)
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
        rw [← csemV_sub hsem]; simp [csem, L.XU_base hpf _ _ F]
      obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
      obtain ⟨us', ds', hic⟩ := assign_call_sym hasg'
      cases hic
      have hex' : callExec L.Hb (.tryCall ⟨.sym n, us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooksU_base (M := M) (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, hb⟩ c wh ops regs _ t w outs w' s' hops hst hasg
        hsw hal herr hsem' hex'
  | reg r =>
    obtain ⟨tv, Lu, Ld, hinfo, -⟩ :=
      hL.blrRegs g hg info hsite.callSite (fun n => by rw [hd]; simp)
    subst hinfo
    intro c wh ops regs i' t w outs w' s' hK hD hG hops hst hasg hP hsw hal herr hsem hex
    have hcl := trySite_clobberAll (hL.compiled g hg).alloc hsite
    have hopsC : (MInst.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩).operands =
        .ok ops := by
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
        (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (he.imgG a ha)).trans (he.imgS a ha))
          k wd hk)
    have huv := call_useVals_reg (tv := tv) (s := t) hregs0
    cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
    | none =>
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩ ti)
          (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem, huv]; simp [csem, L.XU_none hs]
      have hex' : callExec L.Hb (.tryCall ⟨.reg (.x n0), us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooksU_base (M := M) (.inl rfl) t (fun _ => hb)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, .inl rfl⟩ c wh _ regs _ t w outs w' s' hops hst
        hasg hsw hal herr hsem' hex'
    | some h =>
      exact calleeTry_at ((L.calleeOkU hL hU hκ ih hg he).os ctx _ hsite.callSite)
        (fun _ _ h => callAt_tryCall_call h) hcl hK hD hG hops hst hasg hP hsw hal herr hsem hex

/-- **The raising callees' contract of the linked machine with unwinding at depth `M`** for an
activation of `g` (`CalleeUnwOkG` for its external semantics `XU`, raising callees `XRU` and the
machine's raising callees `UU`): at a call of a function of `P` (`bl`, or `blr` of the address of
one `g` may enter) the linked machine's raise and its normal return (`progRaiseCoreU`,
`progOsCoreU`); at a call of a base callee the base's (`OkU.baseUnw`, `OkU.baseNoRaise`). -/
theorem calleeUnwOkU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeUnwOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XU κ M g F) (L.XRU κ M g F)
      (L.UU M) (L.A g).vcp.CallSite (GotV (L.A g).vcp) where
  os info i hsite hi := by
    intro t hK hD hG c wh ops regs i' w hops hst hasg hP hsw hal herr hgg obj w' hraise
    cases hd : info.dest with
    | sym n =>
      cases hpf : L.P.func? n with
      | none =>
        have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hd], hpf⟩
        have hcd : callDest info = some n := by
          obtain ⟨d, us, ds⟩ := info; simp only at hd; subst hd; rfl
        rw [hcd, L.XRU_base hpf] at hraise
        obtain ⟨t', h1, rest⟩ := hU.baseUnw g hg info hsite hb i hi F (κ M g) G s
          (CallAt (L.A g).fa (L.A g).base) t hK hD hG c wh ops regs i' w hops hst hasg hP hsw hal
          herr hgg obj w' (by rw [hcd]; exact hraise)
        refine ⟨t', ?_, rest⟩
        rw [hcd] at h1 ⊢
        rw [L.UU_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
        exact h1
      | some h =>
        have hh : h ∈ L.P.funcs := (Clif.Program.func?_some hpf).1
        obtain ⟨Lu, Ld, rfl, hLu, -, huv, hdefs, hra⟩ :=
          L.symSite hL hg hsite hd hpf hi hops hst hasg hP
        rw [callDest_sym, huv t, L.XRU_prog hpf] at hraise
        obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := L.progRaiseCoreU hL hU hκ ih hg hh
          (.inl ⟨_, hsite, n, rfl, hpf⟩) he.imgF he.imgG he.imgS hLu hK hG hra hsw hraise
        refine ⟨t', by rw [callDest_sym, L.UU_some hpf]; exact h1, h2, h3, h4, h5,
          fun r hr hnd' hnc => h6 r hr (notDefault_of hi rfl hdefs hnd' hnc), fun r _ hcs => h7 r hcs⟩
    | reg r =>
      have hreg : ∀ n, info.dest ≠ .sym n := fun n => by rw [hd]; simp
      obtain ⟨tv, Lu, Ld, n0, rfl, rfl, hregs, huv, hdefs, htgt, hcpc⟩ :=
        L.regSite hL hg hsite hreg hi hops hst hasg hP he.imgG he.imgS hG
      have hraise0 := hraise
      rw [callDest_reg, huv] at hraise
      cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
      | none =>
        have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
        rw [L.XRU_none hs] at hraise
        obtain ⟨t', h1, rest⟩ := hU.baseUnw g hg _ hsite (.inl rfl) i hi F (κ M g) G s
          (CallAt (L.A g).fa (L.A g).base) t hK hD hG c wh _ regs i' w hops hst hasg hP hsw hal
          herr hgg obj w' (by rw [callDest_reg, huv]; exact hraise)
        refine ⟨t', ?_, rest⟩
        rw [callDest_reg] at h1 ⊢
        rw [L.UU_base (.inl rfl) t (fun _ => hb)]
        exact h1
      | some h =>
        rw [L.XRU_ind hs] at hraise
        split at hraise
        · rename_i hdecl
          have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
          have hgot := L.got_of_guard hL (X := L.XU κ M g F) rfl hgg huv hs
          obtain ⟨hLu, -⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
          have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
          obtain ⟨t', h1, h2, h3, h4, h5, h6, h7⟩ := L.progRaiseCoreU hL hU hκ ih hg hh
            (.inr (.inr ⟨hh, hdecl.1.1⟩)) he.imgF he.imgG he.imgS hLu hK hG
            (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hcpc) hsw hraise
          refine ⟨t', by rw [callDest_reg, L.UU_none hb]; exact h1, h2, h3, h4, h5,
            fun r hr hnd' hnc => h6 r hr (notDefault_of hi rfl hdefs hnd' hnc),
            fun r _ hcs => h7 r hcs⟩
        · cases hraise
  noRaise info i hsite hi := by
    intro t hK hD hG c wh ops regs i' w hops hst hasg hP hsw hal herr hgg hx
    cases hd : info.dest with
    | sym n =>
      cases hpf : L.P.func? n with
      | none =>
        have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hd], hpf⟩
        have hcd : callDest info = some n := by
          obtain ⟨d, us, ds⟩ := info; simp only at hd; subst hd; rfl
        rw [hcd, L.XU_base hpf] at hx
        have h1 := hU.baseNoRaise g hg info hsite hb i hi F (κ M g) G s
          (CallAt (L.A g).fa (L.A g).base) t hK hD hG c wh ops regs i' w hops hst hasg hP hsw hal
          herr hgg (by rw [hcd]; exact hx)
        rw [hcd] at h1 ⊢
        rw [L.UU_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
        exact h1
      | some h =>
        have hh : h ∈ L.P.funcs := (Clif.Program.func?_some hpf).1
        obtain ⟨Lu, Ld, rfl, hLu, hLd, huv, hdefs, hra⟩ :=
          L.symSite hL hg hsite hd hpf hi hops hst hasg hP
        rw [callDest_sym, huv t, L.XU_prog hpf] at hx
        obtain ⟨⟨outs, w'⟩, hx⟩ := Option.ne_none_iff_exists'.mp hx
        obtain ⟨-, -, -, -, -, h6⟩ := L.progOsCoreU hL hU hκ ih hg hh
          (.inl ⟨_, hsite, n, rfl, hpf⟩) he.imgF he.imgG he.imgS hLu hLd
          (info := ⟨.sym n, retPairs Lu, callDefs Ld⟩) rfl hdefs hK hG hra hsw hx (outs := outs)
          ⟨outs.length, by simp⟩
        rw [callDest_sym, L.UU_some hpf]
        exact h6
    | reg r =>
      have hreg : ∀ n, info.dest ≠ .sym n := fun n => by rw [hd]; simp
      obtain ⟨tv, Lu, Ld, n0, rfl, rfl, hregs, huv, hdefs, htgt, hcpc⟩ :=
        L.regSite hL hg hsite hreg hi hops hst hasg hP he.imgG he.imgS hG
      have hx0 := hx
      rw [callDest_reg, huv] at hx
      cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
      | none =>
        have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
        rw [L.XU_none hs] at hx
        have h1 := hU.baseNoRaise g hg _ hsite (.inl rfl) i hi F (κ M g) G s
          (CallAt (L.A g).fa (L.A g).base) t hK hD hG c wh _ regs i' w hops hst hasg hP hsw hal
          herr hgg (by rw [callDest_reg, huv]; exact hx)
        rw [callDest_reg] at h1 ⊢
        rw [L.UU_base (.inl rfl) t (fun _ => hb)]
        exact h1
      | some h =>
        rw [L.XU_ind hs] at hx
        split at hx
        · rename_i hdecl
          have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
          have hgot := L.got_of_guard hL (X := L.XU κ M g F) rfl hgg huv hs
          obtain ⟨hLu, hLd⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
          have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
          obtain ⟨⟨outs, w'⟩, hx⟩ := Option.ne_none_iff_exists'.mp hx
          obtain ⟨-, -, -, -, -, h6⟩ := L.progOsCoreU hL hU hκ ih hg hh
            (.inr (.inr ⟨hh, hdecl.1.1⟩)) he.imgF he.imgG he.imgS hLu hLd
            (info := ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩) rfl hdefs hK hG
            (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hcpc) hsw hx (outs := outs)
            ⟨outs.length, by simp⟩
          rw [callDest_reg, L.UU_none hb]
          exact h6
        · exact absurd rfl hx
  excl := L.XU_excl hU.baseExcl

end LinkSysU

end E2E
