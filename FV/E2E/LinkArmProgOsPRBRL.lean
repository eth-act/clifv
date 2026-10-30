import FV.E2E.LinkArmProgOsP
import FV.E2E.LinkArmXPBT
import FV.E2E.LinkArmProgCallPRBRL

/-!
# The calls on `ThmPRBRL` (SEM1 #537, #680 (3), #694)

`LinkArmProgOsPRBR` with the induction hypothesis `ThmPRBRL` (#694): `progOsCorePRBRL`,
`progOsCoreXPRRBRL`, `progOsPRBRL`, `progOsRegPRBRL`, `calleeOkPRBRL`, `calleeTryOkPRBRL` (same
proofs). The `…R` forms take the determinism premise `DetPRBR` (#719, `progCallPRBRLR`); the
names without `R` are their corollaries (`DetPRB.toR`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`progOsCore` on `ThmPRB`** (`progCallPRB`): from a caller state `t` whose arguments are in
`h`'s parameter registers and that agrees with the canonical callee state on the masked
registers but `x30`/pc and on the callee's frame and region (`hmsk`, `hrgn`), the linked call
gives `progXBT`'s results and world. -/
theorem progOsCorePRBRLRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) w))
    (hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) w).mem a)
    (hx : L.progXBT κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  have hpf := func?_of_mem hL.names hh
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lu.map (fun q => regVal t q.2) = uses at hx hmsk hrgn
  unfold progXBT at hx
  have hcond : L.CondBT κ M F h uses w ∧
      Arm.r .ERR (L.pcall M h (L.canon h uses w)) = .None :=
    Classical.byContradiction fun hc => by rw [if_neg hc] at hx; cases hx
  rw [if_pos hcond] at hx
  obtain ⟨⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, rvals, cm', ini, hmr, hargs, hsav, hpl,
    htab, hinit, hrun⟩, -⟩ := hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨us, outsV, wf, e, hus, hlen, hhold, hmemR, hrs, -, hcall⟩ :=
    L.progCallPRBRLRU hL hM (ih hM) (hdet hM) hpf ⟨g, hg, hcallee⟩ himgF herrw halw hroom hdead hmr
      hargs hsav (fun hN => (hpl hN).1) (fun hN => (hpl hN).2) htab hinit hrun
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
  obtain ⟨ks, hs_eq, hs_ret, -⟩ := hcall t hcOk hmsk hrgn
  obtain ⟨kc, hc_eq, hc_ret, -⟩ := hcall _ (L.callerOk_canon hL hh himgF uses w)
    (L.canon_agree (κ := κ) h uses w M).1 (L.canon_agree (κ := κ) h uses w M).2
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
          (L.callerOk_canon hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hs_ret.ret.sp
        have e2 := hc_ret.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          (L.callerOk_canon hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
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
  · -- the results
    intro p hp
    obtain ⟨⟨op, r⟩, x⟩ := p
    rw [defRegs, hdefs] at hp
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
    simp only [List.getElem?_zip_eq_some] at hj
    obtain ⟨⟨-, hr⟩, hx⟩ := hj
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨j2, hj2, rfl⟩ := hx
    have hjr : j < (sigRets h.sig).length := by
      have := (List.getElem?_eq_some_iff.mp hj2).1; simpa using this
    have hjL : j < Ld.length := by
      have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    have e : ((Ld.map (·.1)).take (sigRets h.sig).length)[j]? = (Ld.map (·.1))[j]? := by
      rw [List.getElem?_take]; simp [hjr]
    rw [← e, hLd] at hr
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hr
    obtain ⟨j1, hj1, rfl⟩ := hr
    rw [List.getElem?_range (by omega : j < min (sigRets h.sig).length Ld.length),
      Option.some.injEq] at hj1
    rw [List.getElem?_range hjr, Option.some.injEq] at hj2
    subst hj1 hj2
    show regVal _ (Reg.x j) = regVal _ (Reg.x j)
    rw [hs_eq, regVal_set_program, hc_eq, regVal_set_program]
    -- the `j`-th result register is a return register of the callee
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
    have hju : j < us.length := by omega
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq] at this
      rw [List.getElem?_eq_getElem hju, ← this]
    have hoj : outsV[j]? = some (outsV[j]'(by omega)) := List.getElem?_eq_getElem _
    rw [hs_ret.regs j _ _ _ hus_j hoj, hc_ret.regs j _ _ _ hus_j hoj]
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

/-- **`progOsCoreP` at the world with both prophecies of call `n`**: a caller state `t` with the
masked registers of `R n` and `P n` in the `κ M g` bytes below its `sp` (`hmskQ`, `hrgnQ`) meets
`progOsCoreP`'s agreement premises for the canonical state of `worldPR … (P n) (R n) w`. -/
theorem progOsCoreXPRRBRLRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcal : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  let W := L.worldPR κ M h (P n) (R n) w
  replace hx : L.progXBT κ M F h (Lu.map (fun q => regVal t q.2)) W = some (outs, w') := hx
  obtain ⟨-, harg, -⟩ := hL.argRegs h hh
  -- `CondBT` of the world with the prophecies
  have hcondW : L.CondBT κ M F h (Lu.map (fun q => regVal t q.2)) W := by
    have hx' := hx
    unfold progXBT at hx'
    exact Classical.byContradiction fun hc => by rw [if_neg (fun h' => hc h'.1)] at hx'; cases hx'
  obtain ⟨hM, -, -, -, hdeadW, -⟩ := hcondW
  have hspW : spv W = spv w :=
    L.r_worldPR_out (κ := κ) (M := M) h (P n) (R n) w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)
  rw [hspW] at hdeadW
  have hst : spv t = spv w := hsw.1 _ (by simp [Masked])
  -- `t`'s arguments are `W`'s
  have hmaskedF : ∀ (r : Reg) (f : Arm.StateField), r.isArgReg = true → r.field = some f → MaskedReg f := by
    intro r f hr hf
    refine ⟨?_, (argReg_ne29 hr hf).2.2.2⟩
    cases r with
    | x k =>
      simp only [Reg.isArgReg, decide_eq_true_eq] at hr
      simp only [Reg.field, Option.some.injEq] at hf
      subst hf
      simp only [Masked, rnum_toNat (show k < 32 by omega)]
      omega
    | v k =>
      simp only [Reg.field, Option.some.injEq] at hf
      subst hf
      trivial
    | _ => simp [Reg.isArgReg] at hr
  have hargW : ∀ r ∈ regLocs h.sig, regVal t r = regVal W r := fun r hr =>
    regVal_eq_of_field (harg r hr) fun f hf => by
      have hm := hmaskedF r f (harg r hr) hf
      rw [hmskQ f hm, L.r_worldPR_in h (P n) w hm]
  have huses : Lu.map (fun q => regVal t q.2) = (regLocs h.sig).map (regVal W) := by
    rw [← hLu, List.map_map]
    exact List.map_congr_left fun q hq => hargW q.2 (by rw [← hLu]; exact List.mem_map_of_mem hq)
  have hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) W) := by
    intro f hf hpc _
    rw [huses, L.canon_self_r h W hpc, L.r_worldPR_in h (P n) w ⟨hf, hpc⟩, hmskQ f ⟨hf, hpc⟩]
  have hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) W).mem a := by
    intro a ha
    rw [hspW] at ha
    have hFI := hdeadW a ha
    rw [L.mem_canon, mem_withImg, if_neg hFI.2, L.mem_worldPR, worldP,
      mem_overlay_in (show L.calleeRgn κ M h w a from ha)]
    exact hrgnQ a (stackBelow_mono (by rw [hst]; exact ha) (L.budget_step hκ hM hg hcal))
  have hsw' : SameWorld F t W :=
    ⟨fun f hf => (hsw.1 f hf).trans (L.r_worldPR_out h _ _ w (fun hm => hf hm.1)).symm,
      fun a ha => (hsw.2.1 a ha).trans (by
        rw [L.mem_worldPR, worldP, mem_overlay_out (R := L.calleeRgn κ M h w)
          (fun hr => ha (hdeadW a hr).1)]),
      hsw.2.2.trans (L.program_worldPR h _ _ w).symm⟩
  exact L.progOsCorePRBRLRU hL hκ ih hdet hg hh hcal himgF himgG himgS hLu hLd hdefs0 hdefs hK hG hra hsw' hmsk
    hrgn hx

/-- **`progOs` for call number `n` with both prophecies, on `ThmPRB`** (module doc). -/
theorem progOsPRBRLRU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next := by
  have ⟨_, nm, hdest, hpf⟩ := hsite
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  obtain ⟨n', Lu, Ld, hinfo, hLu, hLd⟩ := hL.callRegs g hg info h hsite
  subst hinfo
  cases hdest
  intro t hQt hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  replace hsem := csemV_sub hsem
  rw [operands_call_sym] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  rw [call_useVals hregs] at hsem
  have hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (outs, w') := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.XPRBT_prog hpf] at hx
    exact hx
  obtain ⟨hmskQ, hrgnQ⟩ := hQ t hQt hP.callPc
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_some hpf],
    L.progOsCoreXPRRBRLRU hL hκ ih hdet hg hh (.inl ⟨_, hsite⟩) himgF himgG himgS hLu hLd rfl (call_defs hregs)
      hK hG (hL.raCall g hg _ h hsite _ hP.callPc) hsw hmskQ hrgnQ hx⟩

/-- **`progOsReg` for call number `n` with both prophecies, on `ThmPRB`**: a `blr` to a declared
function of `P` (`progOsCoreXPR`), to another function of `P` (`XPRBT` undefined), or to no function
of `P` (the base's). -/
theorem progOsRegPRBRLRU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next := by
  obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
  intro t hQt hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
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
  have hx : (L.XPRBT κ M g F P R n).call none (regVal t (.x n0) :: Lu.map (fun q => regVal t q.2)) w =
      some (outs, w') := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    exact hx
  cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
  | none =>
    -- no function of `P` at the target: the base's contract
    have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
    rw [L.XPRBT_none hs] at hx
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
    rw [L.XPRBT_ind hs] at hx
    split at hx
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
        rw [call_useVals_reg hregs0] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_target hL hs e
      obtain ⟨hLu, hLd⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
      exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_none hb],
        L.progOsCoreXPRRBRLRU hL hκ ih hdet hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) himgF himgG himgS hLu hLd rfl
          (call_defs_reg hregs0) hK hG
          (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hP.callPc) hsw (hQ t hQt hP.callPc).1
          (hQ t hQt hP.callPc).2 hx⟩
    · cases hx

/-- **`calleeOk` for call number `n` with both prophecies, on `ThmPRB`**: the call contract of an
activation of `g` for `XPRBT … n`, at the call states `Q` (masked registers of `R n`, `P n` below
`sp`). -/
theorem calleeOkPRBRLRU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) where
  os ctx info hsite := by
    cases hd : info.dest with
    | reg r =>
      exact L.progOsRegPRBRLRU hL hκ ih hdet hg he.imgF he.imgG he.imgS hsite (fun n => by rw [hd]; simp) ctx
        hQ
    | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h => exact L.progOsPRBRLRU hL hκ ih hdet hg he.imgF he.imgG he.imgS ⟨hsite, n, hdest, hpf⟩ ctx hQ
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      have h0 := hL.baseOs g hg info hsite hb F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) ctx
      intro t _ h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.call ⟨.sym n, us, ds⟩) (useVals ops regs t) w =
          some (outs, w', .next) := by
        rw [← csemV_sub hsem]; simp [csem, L.XPRBT_base hpf]
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
  ext _ _ _ _ _ hx herr := L.XPRBT_ext hL hx herr

/-- **`calleeTryOk` for call number `n` with both prophecies, on `ThmPRB`**, at the call states
`Q`. -/
theorem calleeTryOkPRBRLRU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n)
      (L.hooks M) (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  intro ctx info ti hsite
  cases hd : info.dest with
  | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact calleeTryOkGP_of_call (S := fun i t => i = info ∧ t = ti)
        (fun ctx' i t ⟨e1, _⟩ => e1 ▸ (L.calleeOkPRBRLRU hL hκ ih hdet hg he hQ).os ctx' info hsite.callSite)
        (fun _ _ _ h => callAt_tryCall_call h)
        (fun i t ⟨_, e2⟩ => e2 ▸ trySite_clobberAll (hL.compiled g hg).alloc hsite)
        ctx info ti ⟨rfl, rfl⟩
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      intro c wh ops regs i' t w outs w' s' _ _ _ _ hops hst hasg _ hsw hal herr hsem hex
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.sym n, us, ds⟩ ti) (useVals ops regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem]; simp [csem, L.XPRBT_base hpf]
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
    intro c wh ops regs i' t w outs w' s' hQt hK hD hG hops hst hasg hP hsw hal herr hsem hex
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
        rw [← csemV_sub hsem, huv]; simp [csem, L.XPRBT_none hs]
      have hex' : callExec L.Hb (.tryCall ⟨.reg (.x n0), us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inl rfl) t (fun _ => hb)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, .inl rfl⟩ c wh _ regs _ t w outs w' s' hops hst
        hasg hsw hal herr hsem' hex'
    | some h =>
      exact calleeTryP_at ((L.calleeOkPRBRLRU hL hκ ih hdet hg he hQ).os ctx _ hsite.callSite)
        (fun _ _ h => callAt_tryCall_call h) hcl hQt hK hD hG hops hst hasg hP hsw hal herr hsem hex

/-! ### The statements with `DetPRBR` (corollaries, `DetPRBR.toU`) -/

/-- **`progOsCore` on `ThmPRB`, determinism `DetPRBR`** (`progOsCorePRBRLRU`). -/
theorem progOsCorePRBRLR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) w))
    (hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) w).mem a)
    (hx : L.progXBT κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) :=
  L.progOsCorePRBRLRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg hh hcallee himgF himgG himgS
    hLu hLd hdefs0 hdefs hK hG hra hsw hmsk hrgn hx

/-- **`progOsCoreP` at the world with both prophecies of call `n`, determinism `DetPRBR`**
(`progOsCoreXPRRBRLRU`). -/
theorem progOsCoreXPRRBRLR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcal : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) :=
  L.progOsCoreXPRRBRLRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg hh hcal himgF himgG himgS
    hLu hLd hdefs0 hdefs hK hG hra hsw hmskQ hrgnQ hx

/-- **`progOs` for call number `n` with both prophecies, determinism `DetPRBR`**
(`progOsPRBRLRU`). -/
theorem progOsPRBRLR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsPRBRLRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg himgF himgG himgS hsite ctx hQ

/-- **`progOsReg` for call number `n` with both prophecies, determinism `DetPRBR`**
(`progOsRegPRBRLRU`). -/
theorem progOsRegPRBRLR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsRegPRBRLRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg himgF himgG himgS hsite hreg
    ctx hQ

/-- **`calleeOk` for call number `n` with both prophecies, determinism `DetPRBR`**
(`calleeOkPRBRLRU`). -/
theorem calleeOkPRBRLR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  L.calleeOkPRBRLRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg he hQ

/-- **`calleeTryOk` for call number `n` with both prophecies, determinism `DetPRBR`**
(`calleeTryOkPRBRLRU`). -/
theorem calleeTryOkPRBRLR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n)
      (L.hooks M) (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  L.calleeTryOkPRBRLRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg he hQ

/-! ### The statements with `DetPRB` (corollaries, `DetPRB.toR`) -/

/-- **`progOsCore` on `ThmPRB`** (`progOsCorePRBRLR` with `DetPRB`). -/
theorem progOsCorePRBRL (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) w))
    (hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) w).mem a)
    (hx : L.progXBT κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) :=
  L.progOsCorePRBRLR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg hh hcallee himgF himgG himgS hLu
    hLd hdefs0 hdefs hK hG hra hsw hmsk hrgn hx

/-- **`progOsCoreP` at the world with both prophecies of call `n`** (`progOsCoreXPRRBRLR` with
`DetPRB`). -/
theorem progOsCoreXPRRBRL (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcal : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) :=
  L.progOsCoreXPRRBRLR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg hh hcal himgF himgG himgS hLu
    hLd hdefs0 hdefs hK hG hra hsw hmskQ hrgnQ hx

/-- **`progOs` for call number `n` with both prophecies, on `ThmPRB`** (`progOsPRBRLR` with
`DetPRB`). -/
theorem progOsPRBRL (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsPRBRLR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg himgF himgG himgS hsite ctx hQ

/-- **`progOsReg` for call number `n` with both prophecies, on `ThmPRB`** (`progOsRegPRBRLR`
with `DetPRB`). -/
theorem progOsRegPRBRL (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsRegPRBRLR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg himgF himgG himgS hsite hreg ctx
    hQ

/-- **`calleeOk` for call number `n` with both prophecies, on `ThmPRB`** (`calleeOkPRBRLR` with
`DetPRB`). -/
theorem calleeOkPRBRL (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  L.calleeOkPRBRLR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg he hQ

/-- **`calleeTryOk` for call number `n` with both prophecies, on `ThmPRB`**
(`calleeTryOkPRBRLR` with `DetPRB`). -/
theorem calleeTryOkPRBRL (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n)
      (L.hooks M) (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  L.calleeTryOkPRBRLR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg he hQ

end LinkSys

end E2E
