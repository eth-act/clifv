import FV.E2E.LinkArmUCallNI

/-!
# The per-state facts of the linked machine's runs with unwinding (S10g, #404)

`FV/E2E/LinkGood.lean` for the linked machine with unwinding (`LinkSysU.machU`): the linking
statement with unwinding and per-state facts (`ThmGU`) gives every activation the per-state facts
of its run (`RunGoodLU`: `GoodAtU` at every state of `ReachLU` whose step ends without error).
Here the pieces its induction step (`thm_ofGU`, `thm_ofUNG`, `FV/E2E/LinkArmUIndGood.lean`) uses:

* `actRLU`: the register-level activation with unwinding that the induction step instantiates the
  per-function world theorem with (`XU`, `XRU`, `hooksU`, `UU`, the tables).
* `callData`: the facts of a call state common to a callee that returns (`RL.CallPre`) and one
  that raises (`RLU.CallPreU`): the allocated call at the pc and the callee's result (`XU`) or raise
  (`XRU`).
* `blrToU`: the callee of a `blr` at such a state is one `g` may enter (`BlrAtU`).
* `progGoodCoreU`, `callGoodU`: **the callee's states**: at such a state where the machine calls
  `h`, every state of `h`'s run (returning or raising) whose step ends without error has the
  per-state facts — from the callee's CLIF run (`CondU`/`CondR`), `progCallUNQ` and the linking
  statement one level down.
* `runGood_of_traceU`: an activation's `RunGoodLU` from its register-level trace (`actGoodXU`)
  and a bound on its states before the return.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- The register-level activation with unwinding of `g` at depth `M` entered in `s` (keeping `G`,
exterior `F`) that the induction step instantiates the world theorem with. -/
noncomputable def actRLU (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F G : BitVec 64 → Prop) (s : Arm.ArmState) : RLU :=
  ⟨⟨(L.A g).vcp, (L.A g).rf, (L.A g).af, (L.A g).fa, (L.A g).fb, {}, (L.A g).base, s,
    L.XU κ M g F, L.hooksU M, {}, κ M g, G, GotV (L.A g).vcp⟩, L.XRU κ M g F, L.UU M,
    (L.A g).tables⟩

/-- **The facts of a call state** of the activation `actRLU` where the callee contract's premise
holds for a callee that returns (`RL.CallPre`) or raises (`RLU.CallPreU`): the allocated call at
the pc, its operands and registers, the world, the GOT guard, and the callee's result or raise. -/
theorem callData {M : Nat} {g : Clif.Function} {F G : BitVec 64 → Prop} {s : Arm.ArmState}
    (hFe : (L.actRLU κ M g F G s).F = F) {u : Arm.ArmState}
    (hpre : (L.actRLU κ M g F G s).CallPre u ∨ (L.actRLU κ M g F G s).CallPreU u) :
    ∃ (info ic : CallInfo) (regs : Array Reg) (ops : Array Operand) (w : Arm.ArmState),
      (L.A g).vcp.CallSite info ∧ (MInst.call info).assign regs = .ok (.call ic) ∧
      CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) (.call ic) ∧
      (MInst.call info).operands = .ok ops ∧
      (∃ (c : CheckCtx) (wh : String) (clob : List Reg),
        c.checkStatic wh ops (regs.map .reg) clob = .ok ()) ∧ SameWorld F u w ∧
      gotGuard (GotV (L.A g).vcp) (L.XU κ M g F) info (useVals ops regs u) ∧
      (((L.XU κ M g F).call (callDest info) (useVals ops regs u) w).isSome ∨
        ((L.XRU κ M g F).raise (callDest info) (useVals ops regs u) w).isSome) := by
  rcases hpre with hpre | hpre
  · obtain ⟨ctx, i, ctl, ⟨info, hsite, hi⟩, -, -, -, c, wh, ops, regs, i', w, outs, w', hops, hst,
      hasg, hP, hsw, -, -, hsem⟩ := hpre
    have hsw : SameWorld F u w := hFe ▸ hsw
    have hsem : csemV (GotV (L.A g).vcp) F ctx (L.XU κ M g F) i (useVals ops regs u) w =
        some (outs, w', ctl) := hFe ▸ hsem
    rcases hi with rfl | ⟨ti, rfl⟩
    · obtain ⟨ic, rfl⟩ := (assign_call_tryCall info regs).1 i' hasg
      have h0 := csemV_sub hsem
      simp only [csem, Option.map_eq_some_iff] at h0
      obtain ⟨⟨o, w2⟩, hx, -⟩ := h0
      exact ⟨info, ic, regs, ops, w, hsite, hasg, hP, hops, ⟨c, wh, _, hst⟩, hsw,
        csemV_guard hsem, .inl (Option.isSome_iff_exists.mpr ⟨_, hx⟩)⟩
    · obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      have h0 := csemV_sub hsem
      simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h0
      obtain ⟨⟨o, w2⟩, ⟨hx, -⟩, -⟩ := h0
      exact ⟨info, ic, regs, ops, w, hsite, hasg', callAt_tryCall_call hP,
        by rw [← operands_tryCall_call info ti]; exact hops, ⟨c, wh, _, hst⟩, hsw,
        csemV_guard_try hsem, .inl (Option.isSome_iff_exists.mpr ⟨_, hx⟩)⟩
  · obtain ⟨i, info, hsite, hi, -, -, -, c, wh, ops, regs, i', w, obj, w', hops, hst, hasg, hP, hsw,
      -, -, hgg, hr⟩ := hpre
    have hsw : SameWorld F u w := hFe ▸ hsw
    rcases hi with rfl | ⟨ti, rfl⟩
    · obtain ⟨ic, rfl⟩ := (assign_call_tryCall info regs).1 i' hasg
      exact ⟨info, ic, regs, ops, w, hsite, hasg, hP, hops, ⟨c, wh, _, hst⟩, hsw, hgg,
        .inr (Option.isSome_iff_exists.mpr ⟨_, hr⟩)⟩
    · obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      exact ⟨info, ic, regs, ops, w, hsite, hasg', callAt_tryCall_call hP,
        by rw [← operands_tryCall_call info ti]; exact hops, ⟨c, wh, _, hst⟩, hsw, hgg,
        .inr (Option.isSome_iff_exists.mpr ⟨_, hr⟩)⟩

/-- **The callee of a `blr` at a call state is one `g` may enter through the call's register**
(`LinkSys.blrTo_of_pre` for a callee that returns or raises): `XU`/`XRU` call a function of `P`
through a register only when `g` may enter it (`IndTo`), and the GOT guard pins a call through
the GOT to its symbol. -/
theorem blrToU (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) {u : Arm.ArmState}
    (hpre : (L.actRLU κ M g F G s).CallPre u ∨ (L.actRLU κ M g F G s).CallPreU u) :
    L.BlrAtU g u := by
  intro xr h hx0 hb
  obtain ⟨info, ic, regs, ops, w, hsite, hasgC, hPC, hopsC, ⟨c, wh, clob, hst'⟩, -, hguard, hx⟩ :=
    L.callData he.hF hpre
  obtain ⟨j, x, tt, hj, hx', hpc⟩ := hPC
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hsz : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hc.layout]; have := hL.fits g hg; omega
  have hins : insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some x := by
    rw [hpc]; exact insnAt_line hsz hj
  rw [hins] at hx0
  cases hd : info.dest with
  | sym n =>
    obtain ⟨d0, us0, ds0⟩ := info
    simp only at hd
    subst hd
    obtain ⟨us', ds', hic⟩ := assign_call_sym hasgC
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    cases hx0
  | reg r =>
    have hreg : ∀ n, info.dest ≠ .sym n := fun n => by rw [hd]; simp
    obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
    rw [operands_call_reg] at hopsC
    cases hopsC
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst'
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasgC
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have htgt : blrTarget u = some (lo64 (regVal u (.x n0))) := by
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg u (fun a ha => by
          have hpre' := hpre
          rcases hpre' with ⟨-, -, -, -, -, -, hGk, -⟩ | ⟨-, -, -, -, -, -, hGk, -⟩
          · exact (hGk a (he.imgG a ha)).trans (he.imgS a ha)
          · exact (hGk a (he.imgG a ha)).trans (he.imgS a ha)) k wd hk)
    have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
      rw [htgt] at hb; exact hb
    have huse := call_useVals_reg (tv := tv) hregs0 u
    simp only [callDest] at hx
    rw [huse] at hx
    have hdecl : L.IndTo g h ∧ (Lu.map fun q => regVal u q.2).length = (regLocs h.sig).length := by
      rcases hx with hx | hx
      · rw [L.XU_ind hs] at hx
        split at hx
        · rename_i hc'; exact hc'
        · cases hx
      · rw [L.XRU_ind hs] at hx
        split at hx
        · rename_i hc'; exact hc'
        · cases hx
    have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
      intro n hn
      have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
      rw [call_useVals_reg hregs0] at e
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
      exact L.got_target hL hs e
    exact ⟨_, tv, hsite, rfl, hdecl.1, hgot⟩

/-- **The callee's states of a call of a function of `P` that returns or raises**
(`LinkSys.progGoodCore` with unwinding): from the callee's CLIF run (`CondU`/`CondR` of
`progXU`/`progXR`), the caller state compatible with the call's world (`CallerOk`) and
`progCallUNQ` one level down (with the budget `hκ`, #581: the callee's budget holds its probes). -/
theorem progGoodCoreU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmGU κ (M - 1)) {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    (hh : h ∈ L.P.funcs) (hcallee : L.Callee g h) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    (himgF : ∀ a, L.Img a → F a) (himgG : ∀ a, L.Img a → G a)
    (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig)
    {t w : Arm.ArmState} (hG : ∀ a, G a → t.mem a = s0.mem a) (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : (L.progXU κ M F h (Lu.map (fun q => regVal t q.2)) w).isSome ∨
      (L.progXR κ M F h (Lu.map (fun q => regVal t q.2)) w).isSome) :
    L.RunGoodLU (M - 1) h (enterAt (L.A h) t) := by
  have hpf := func?_of_mem hL.names hh
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lu.map (fun q => regVal t q.2) = uses at hx
  have hcOk : L.CallerOk F h uses w t := by
    refine ⟨hsw, fun a ha => (hG a (himgG a ha)).trans (himgS a ha), fun r hr => ?_, hra⟩
    rw [← hLu] at hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
    have hu : uses[j]? = some (regVal t r) := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      simp [← huses, hq]
    rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
      setVal_regVal]
  rcases hx with hx | hx
  · unfold progXU at hx
    split at hx
    · rename_i hcond
      obtain ⟨⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, hmr, hargs, hsav, hpl, hinit, rvals, cm',
        hrun⟩, -⟩ := hcond
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      obtain ⟨_, _, _, -, -, -, -, -, hcall, -⟩ :=
        (L.progCallUNQ hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herrw halw hroom hdead
          (hκ.2 _ h hh) hmr
          hargs hsav hpl hinit).1 rvals cm' hrun
      obtain ⟨_, -, -, -, hrg⟩ := hcall t hcOk
      exact hrg
    · cases hx
  · unfold progXR at hx
    split at hx
    · rename_i hcond
      obtain ⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, hmr, hargs, hsav, hpl, hinit, e, cm',
        hrun⟩ := hcond
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      obtain ⟨_, _, -, -, hcall, -⟩ :=
        (L.progCallUNQ hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herrw halw hroom hdead
          (hκ.2 _ h hh) hmr
          hargs hsav hpl hinit).2 e cm' hrun
      obtain ⟨_, -, -, hrg⟩ := hcall t hcOk
      exact hrg
    · cases hx

/-- **The crux: the callee's states at a call state** (`LinkSys.callGood` with unwinding). At a
state `u` of the activation of `g` at depth `M` where the callee contract's premise holds for a
callee that returns (`RL.CallPre`) or raises (`RLU.CallPreU`) and the machine calls `h`
(`CallsAtU`), every state of `h`'s run entered from `u` whose step ends without error has the
per-state facts (`progGoodCoreU`; with the budget `hκ`, #581). -/
theorem callGoodU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmGU κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) {u : Arm.ArmState} {h : Clif.Function}
    (hpre : (L.actRLU κ M g F G s).CallPre u ∨ (L.actRLU κ M g F G s).CallPreU u)
    (hprog : u.program = (L.A g).fb.program (L.A g).base) (hcall : L.CallsAtU g u h) :
    L.RunGoodLU (M - 1) h (enterAt (L.A h) u) := by
  obtain ⟨info, ic, regs, ops, w, hsite, hasgC, hPC, hopsC, ⟨c, wh, clob, hst'⟩, hsw, hguard, hx⟩ :=
    L.callData he.hF hpre
  have hGk : ∀ a, G a → u.mem a = s.mem a := by
    rcases hpre with ⟨-, -, -, -, -, -, hGk, -⟩ | ⟨-, -, -, -, -, -, hGk, -⟩ <;> exact hGk
  have hcp := hPC.callPc
  obtain ⟨j, x, tt, hj, hx', hpc⟩ := hPC
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hsz : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hc.layout]; have := hL.fits g hg; omega
  have hne : (L.A g).fb.words.toList ≠ [] := by
    obtain ⟨_, wd, hw, hk⟩ := FnAsm.layout_word hc.layout hlm hj rfl
    intro h
    have : (L.A g).fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hins : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some x := by
    rw [progBase_eq (by rw [hprog]; rfl) hne, hpc]; exact insnAt_line hsz hj
  cases hd : info.dest with
  | sym n =>
    obtain ⟨d0, us0, ds0⟩ := info
    simp only at hd
    subst hd
    obtain ⟨us', ds', hic⟩ := assign_call_sym hasgC
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have hpf : L.P.func? n = some h := by
      rcases hcall with ⟨n', hn', hpf'⟩ | ⟨⟨r', hr'⟩, -⟩
      · rw [hins] at hn'; cases hn'; exact hpf'
      · rw [hins] at hr'; cases hr'
    obtain ⟨hh, -⟩ := Clif.Program.func?_some hpf
    have hps : L.ProgSite g ⟨.sym n, us0, ds0⟩ h := ⟨hsite, n, rfl, hpf⟩
    obtain ⟨n', Lu, Ld, hinfo, hLu, -⟩ := hL.callRegs g hg _ h hps
    cases hinfo
    rw [operands_call_sym] at hopsC
    cases hopsC
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst'
    have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    simp only [callDest] at hx
    rw [L.XU_prog hpf, L.XRU_prog hpf, call_useVals hregs] at hx
    exact L.progGoodCoreU hL hU hκ ih hg hh (.inl ⟨_, hps⟩) he.imgF he.imgG he.imgS hLu hGk
      (hL.raCall g hg _ h hps _ hcp) hsw hx
  | reg r =>
    have hreg : ∀ n, info.dest ≠ .sym n := fun n => by rw [hd]; simp
    obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
    rw [operands_call_reg] at hopsC
    cases hopsC
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst'
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasgC
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have htgt : blrTarget u = some (lo64 (regVal u (.x n0))) := by
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg u (fun a ha => (hGk a (he.imgG a ha)).trans
          (he.imgS a ha)) k wd hk)
    have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
      rcases hcall with ⟨n', hn', -⟩ | ⟨-, hb⟩
      · rw [hins] at hn'; cases hn'
      · rw [htgt] at hb; exact hb
    have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
    simp only [callDest] at hx
    rw [call_useVals_reg (tv := tv) hregs0 u, L.XU_ind hs, L.XRU_ind hs] at hx
    have hdecl : L.IndTo g h ∧ (Lu.map fun q => regVal u q.2).length = (regLocs h.sig).length := by
      by_cases hn : L.IndTo g h ∧ (Lu.map fun q => regVal u q.2).length = (regLocs h.sig).length
      · exact hn
      · simp only [hn, ↓reduceIte] at hx
        rcases hx with hx | hx <;> cases hx
    simp only [hdecl, and_self, ↓reduceIte] at hx
    have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
      intro n hn
      have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
      rw [call_useVals_reg hregs0] at e
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
      exact L.got_target hL hs e
    obtain ⟨hLu, -⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
    exact L.progGoodCoreU hL hU hκ ih hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) he.imgF he.imgG he.imgS
      hLu hGk (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hcp) hsw hx

/-- A returning activation (`ActRet`) has returned in the sense of `RetU`. -/
theorem retU_of_actRet {g : Clif.Function} {ra : BitVec 64} {s t : Arm.ArmState}
    {F G : BitVec 64 → Prop} {us : List (Reg × Reg)} {outs : List CV} {wf : Arm.ArmState}
    (habi : AbiCall (L.A g).fb (L.A g).base ra s) (hret : ActRet ra F G us outs wf s t) :
    RetU (L.A g) s t :=
  ⟨hret.ret.pc.trans habi.lr.symm, hret.ret.err, hret.prog.trans habi.program, hret.ret.sp⟩

/-- An activation left by unwinding (`ActUnw`) has returned in the sense of `RetU`. -/
theorem retU_of_actUnw {g : Clif.Function} {ra : BitVec 64} {s t : Arm.ArmState}
    {F G : BitVec 64 → Prop} {obj : BitVec 64} {wf : Arm.ArmState}
    (habi : AbiCall (L.A g).fb (L.A g).base ra s) (hu : ActUnw ra F G obj wf s t) :
    RetU (L.A g) s t :=
  ⟨hu.ret.pc.trans habi.lr.symm, hu.ret.err, hu.prog.trans habi.program, hu.ret.sp⟩

/-- The callee contract's premise at a call line of a state with the per-state facts with
unwinding: `RL.GoodX.call` at a state of the old trace, `RLU.RaiseX.pre` at a raising one. -/
theorem pre_of_good {M : Nat} {g : Clif.Function} {F G : BitVec 64 → Prop} {s u : Arm.ArmState}
    (hsz : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64)
    (hG : actGoodXU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (L.A g).base s
      (L.XU κ M g F) (L.hooksU M) (L.XRU κ M g F) (L.UU M) (L.A g).tables (κ M g) G
      (GotV (L.A g).vcp) u)
    {x : Insn} (hx : insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some x)
    (hc : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r) :
    (L.actRLU κ M g F G s).CallPre u ∨ (L.actRLU κ M g F G s).CallPreU u := by
  rcases hG with ⟨hg, -⟩ | ⟨hr, -⟩
  · obtain ⟨x0, ⟨j, tt, hj, hpc⟩, -⟩ := hg.line
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x0 tt) := hj
    have h0 : insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some x0 := by
      rw [hpc]; exact insnAt_line hsz hj'
    rw [h0] at hx
    cases hx
    exact .inl (hg.call _ ⟨j, tt, hj, hpc⟩ hc)
  · exact .inr hr.pre

/-- The program at a state with the per-state facts with unwinding. -/
theorem prog_of_good {M : Nat} {g : Clif.Function} {F G : BitVec 64 → Prop} {s u : Arm.ArmState}
    (hG : actGoodXU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (L.A g).base s
      (L.XU κ M g F) (L.hooksU M) (L.XRU κ M g F) (L.UU M) (L.A g).tables (κ M g) G
      (GotV (L.A g).vcp) u) : u.program = (L.A g).fb.program (L.A g).base := by
  rcases hG with ⟨hg, -⟩ | ⟨hr, -⟩
  · exact hg.prog
  · exact hr.prog

/-- **The states of the activation of `g` at depth `M` entered in `s`** from its trace with
unwinding (`actGoodXU` of every state before `n`), when every state before its return whose step
ends without error is before `n` (`LinkSys.runGood_of_trace` with unwinding): its own states from
the trace, the nested ones from the call states (`callGoodU`; with the budget `hκ`, #581). -/
theorem runGood_of_traceU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmGU κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) {n : Nat}
    (hgood : ∀ i < n, actGoodXU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s (L.XU κ M g F) (L.hooksU M) (L.XRU κ M g F) (L.UU M) (L.A g).tables (κ M g)
      G (GotV (L.A g).vcp) (runX (L.machU M g) i s))
    (hbound : ∀ k, (∀ j ≤ k, ¬ RetU (L.A g) s (runX (L.machU M g) j s)) →
      Arm.r .ERR (runX (L.machU M g) (k + 1) s) = .None → k < n) :
    L.RunGoodLU M g s := by
  have hc := hL.compiled g hg
  have hsz : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hc.layout]; have := hL.fits g hg; omega
  intro M' g' c' t hR herrt
  cases hR with
  | act hno =>
    rename_i k
    have hG := hgood k (hbound k hno (by rw [runX_add]; exact herrt))
    refine ⟨L.XU κ M g F, L.XRU κ M g F, κ M g, G, GotV (L.A g).vcp, rfl, hG, he.imgG, he.imgS,
      fun a ha hb => he.gfree a (he.imgG a ha) (stackBelow_mono hb (by omega)), ?_⟩
    intro xr h hx hb
    exact L.blrToU hL hg he (L.pre_of_good hsz hG hx (.inr ⟨xr, rfl⟩)) xr h hx hb
  | nest hno hcall herr1 hR' =>
    rename_i M0 k h
    have hG := hgood k (hbound k hno herr1)
    have hprog := L.prog_of_good hG
    have hne : (L.A g).fb.words.toList ≠ [] := by
      obtain ⟨x0, ⟨j, tt, hj, -⟩, -⟩ : ∃ x, (L.actRLU κ (M0 + 1) g F G s).AtLine
          (runX (L.machU (M0 + 1) g) k s) x ∧ True := by
        rcases hG with ⟨hg', -⟩ | ⟨hr, -⟩
        · obtain ⟨x, hx, -⟩ := hg'.line; exact ⟨x, hx, trivial⟩
        · obtain ⟨x, -, -, -, hx, -⟩ := hr.raise; exact ⟨x, hx, trivial⟩
      obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
      obtain ⟨_, wd, hw, hk⟩ := FnAsm.layout_word hc.layout hlm hj rfl
      intro h1
      have : (L.A g).fb.words.size = 0 := by simpa using congrArg List.length h1
      simp [this] at hk
    have hb0 : progBase (runX (L.machU (M0 + 1) g) k s) = (L.A g).base :=
      progBase_eq (by rw [hprog]; rfl) hne
    obtain ⟨x, hx, hcx⟩ : ∃ x, insnAt (L.A g).fa (L.A g).base
        (Arm.r .PC (runX (L.machU (M0 + 1) g) k s)) = some x ∧
        ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) := by
      rcases hcall with ⟨n, hn, -⟩ | ⟨⟨r, hr⟩, -⟩
      · exact ⟨_, by rw [← hb0]; exact hn, .inl ⟨n, rfl⟩⟩
      · exact ⟨_, by rw [← hb0]; exact hr, .inr ⟨r, rfl⟩⟩
    exact L.callGoodU hL hU hκ ih hg he (L.pre_of_good hsz hG hx hcx) hprog hcall _ _ _ _ hR' herrt

end LinkSysU

end E2E
