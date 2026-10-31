import FV.E2E.LinkArmUCallNI

/-!
# The external contracts of an activation with unwinding (S10f, #233)

`LinkSys.progResult`/`xCallsOk`/`xCallsIndOk` (`FV/E2E/LinkArm.lean`) for the activation's
environment with unwinding (`envOfX`) and external semantics (`XU`), and their exceptional
counterparts `XRaiseOk`/`XRaiseIndOk` for the activation's raising callees (`XRU`): a call of a
function of `P` whose callee run with unwinding ends `unwound` raises an exception object related
to the CLIF exception, the world after the linked machine's raise related to the callee run's
memory (`progRaiseResultU`, from `progCallU`); a base extern's raise is the base's (`OkU.baseXR`,
`OkU.baseXRI`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- An extern of `envOfX`: the base's outside `P`, or (for a function of `P` that `g` may reach)
the linked environment's, defined only from a memory whose oracle has `c` (when program callees
have slots). -/
theorem envOfX_some {M : Nat} {g : Clif.Function} {c : BitVec 64} {n : String}
    {G : List Clif.Val → Clif.Mem → Clif.XOutcome} (h : (L.envOfX M g c).extern n = some G) :
    (L.P.func? n = none ∧ L.envX.extern n = some G) ∨
    (∃ h', L.P.func? n = some h' ∧ L.MayCall g n ∧ ∃ G0,
      (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n = some G0 ∧
      ∀ vals cm, (∀ m, G vals cm ≠ .stuck m) →
        (L.NeedSlots → L.PlaceAt cm c) ∧ G0 vals cm = G vals cm) := by
  simp only [envOfX] at h
  split at h
  · cases h
  · rename_i hn
    cases hpf : L.P.func? n with
    | none =>
      rw [if_neg (by simp [hpf]), Clif.linkEnvRX_none hpf] at h
      exact .inl ⟨rfl, h⟩
    | some h' =>
      rw [if_pos (by simp [hpf])] at h
      refine .inr ⟨h', rfl, Classical.byContradiction fun hd => hn ⟨by simp [hpf], hd⟩, ?_⟩
      cases hG0 : (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n with
      | none => rw [hG0] at h; cases h
      | some G0 =>
        rw [hG0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨G0, rfl, fun vals cm hst => ?_⟩
        dsimp only at hst ⊢
        by_cases hp : L.NeedSlots → L.PlaceAt cm c
        · rw [if_pos hp]; exact ⟨hp, rfl⟩
        · rw [if_neg hp] at hst; exact absurd rfl (hst _)

/-- A call of a function `h` of `P` through the linked environment with unwinding: the callee's
entry state and run. -/
theorem linkEnvRX_run {M : Nat} {n : String} {h : Clif.Function} (hpf : L.P.func? n = some h)
    {G0 : List Clif.Val → Clif.Mem → Clif.XOutcome}
    (hG0 : (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n = some G0) {vals : List Clif.Val}
    {cm : Clif.Mem} {o : Clif.XOutcome} (ho : G0 vals cm = o)
    (hc : (∃ v m, o = .returned v m) ∨ ∃ e m, o = .unwound e m) :
    ∃ cs, Clif.initState L.P n vals cm = .ok cs ∧ L.crunX M cs = o := by
  rw [Clif.linkEnvRX_some hpf] at hG0
  cases hG0
  cases hinit : Clif.initState L.P n vals cm with
  | ok cs => simp only [hinit] at ho; exact ⟨cs, rfl, ho⟩
  | trap c => simp only [hinit] at ho; subst ho; rcases hc with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  | stuck m => simp only [hinit] at ho; subst ho; rcases hc with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- The stack-passed arguments of a declared function of `P` are in the caller's outgoing area,
outside `F`. -/
theorem stackArgsAvoid_decl (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {ext : Clif.ExtFunc} (hin : ext ∈ g.externs.map (·.2)) {h : Clif.Function}
    (hpf : L.P.func? ext.name = some h) {F : BitVec 64 → Prop} {c : BitVec 64}
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState}
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w) {vals : List Clif.Val} {cs : Clif.State}
    (hinit : Clif.initState L.P ext.name vals cm = .ok cs) : StackArgsAvoid F h.sig vals w := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  have hsig := hL.declSig g hg ext hin h hpf
  have hout := hmr.1.2.2
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

/-- **A call of a function `h` of `P` that `g` may call, from a world of `g`, whose callee run
with unwinding returns**: `progXU` is defined and gives the callee's CLIF results and memory in
`g`'s relation (`progResult`'s counterpart). -/
theorem progResultU (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX]
    (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g h : Clif.Function}
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
    (hret : L.crunX M cs = .returned rvals cm') :
    ∃ outs w', L.progXU κ M F h args w = some (outs, w') ∧
      outs.length = (sigRets h.sig).length ∧ PrefixHold rvals outs ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' := by
  have hpf := func?_of_mem hL.names hh
  have hM : 0 < M := by
    cases M with
    | zero => exact absurd hret ((hR.zero cs).1 rvals cm')
    | succ M => omega
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  obtain ⟨⟨hmemR0, hslot, hout⟩, hsp, herrw⟩ := hmr
  have hbud : frameDrop (L.A h).af + κ M' h ≤ κ (M' + 1) g := L.budget_step hκ hM hg hcallee
  have hroom' : frameDrop (L.A h).af + κ M' h ≤ (spv w).toNat := by rw [hsp]; omega
  have hdead' : ∀ a, StackBelow (frameDrop (L.A h).af + κ M' h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha =>
    hdead a (by rw [← hsp]; exact stackBelow_mono ha hbud)
  have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hN => by rw [hsp]; exact hpl hN
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, -, hcall, -⟩ :=
    (L.progCallUN hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herrw
      (by rw [hsp]; exact halign) hroom' hdead' (hκ.2 _ h hh) hmemR0 hargs hsav hplw hinit).1
      rvals cm' hret
  obtain ⟨kc, hc_eq, -, hc_ret⟩ := hcall _ (L.callerOk_canon hL hh himgF args w)
  have hcond : L.CondU κ (M' + 1) F h args w ∧
      Arm.r .ERR (L.pcallU (M' + 1) h (L.canon h args w)) = .None := by
    refine ⟨⟨hM, herrw, by rw [hsp]; exact halign, hroom', hdead', vals, cm, cs,
      hmemR0, hargs, hsav, hplw, hinit, rvals, cm', hret⟩, ?_⟩
    rw [hc_eq, r_set_program]; exact hc_ret.ret.err
  have hspT : spv (L.pcallU (M' + 1) h (L.canon h args w)) = spv w := by
    rw [hc_eq]
    simp only [spv]
    rw [r_set_program]
    have := hc_ret.ret.sp
    simp only [spv] at this
    rw [this, r_enterAt _ _ (by simp) (by simp)]
    exact (L.callerOk_canon hL hh himgF args w).world.1 _ (by simp [Masked])
  have hlr : rvals.length ≤ (sigRets h.sig).length := by
    obtain ⟨Nr, hretN⟩ := hR.runs (M' + 1) cs _ hret (.inl ⟨_, _, rfl⟩)
    have hrt := Clif.runLoopX_returned_tys hL.free Nr cs.toX rvals cm'
      (Clif.initState_xinv hinit) hretN
    have hce := clifEntry_initState (f := h) hpf hinit
    have hbot : cs.toX.s.bottom = h := by
      simp [Clif.State.toX, Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have := congrArg List.length hrt
    simp only [List.length_map, Clif.AbiParam.tys] at this
    rw [this]; exact returns_le_sigRets _
  refine ⟨_, _, by rw [progXU, if_pos hcond], ?_, ⟨by simpa using hlr, fun j v x hv hx => ?_⟩,
    ⟨⟨⟨fun a b hv hb => ?_, hmemR.valid, hmemR.symbols⟩, ?_, ?_⟩, ?_, hcond.2⟩⟩
  · rw [List.length_map, List.length_range]
  · -- the results
    have hjr : j < rvals.length := (List.getElem?_eq_some_iff.mp hv).1
    have hju : j < us.length := by have := hhold.1; omega
    simp only [List.getElem?_map, List.getElem?_range (by omega : j < (sigRets h.sig).length),
      Option.map_some, Option.some.injEq] at hx
    subst hx
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq] at this
      rw [List.getElem?_eq_getElem hju, ← this]
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
      exact hout.2.2 a n (L.crunX_allocs hL hU (.inr ⟨g, hg, hib0⟩) hinit hret
        (.inl ⟨_, rfl⟩) a n hv) k hk j hj
  · rw [hspT, hsp]

/-- **A call of a function `h` of `P` that `g` may call, from a world of `g`, whose callee run
with unwinding ends `unwound`**: `progXR` is defined and raises an exception object related to the
CLIF exception, the world related to the callee run's memory in `g`'s relation. -/
theorem progRaiseResultU (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX]
    (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals : List Clif.Val} {e : Clif.Exn} {cm' : Clif.Mem} {cs : Clif.State}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : L.NeedSlots → L.PlaceAt cm c) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : L.crunX M cs = .unwound e cm') :
    ∃ obj w', L.progXR κ M F h args w = some (obj, w') ∧ ExnRel e obj ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' := by
  have hpf := func?_of_mem hL.names hh
  have hM : 0 < M := by
    cases M with
    | zero => exact absurd hret ((hR.zero cs).2 e cm')
    | succ M => omega
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  obtain ⟨⟨hmemR0, hslot, hout⟩, hsp, herrw⟩ := hmr
  have hbud : frameDrop (L.A h).af + κ M' h ≤ κ (M' + 1) g := L.budget_step hκ hM hg hcallee
  have hroom' : frameDrop (L.A h).af + κ M' h ≤ (spv w).toNat := by rw [hsp]; omega
  have hdead' : ∀ a, StackBelow (frameDrop (L.A h).af + κ M' h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha =>
    hdead a (by rw [← hsp]; exact stackBelow_mono ha hbud)
  have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hN => by rw [hsp]; exact hpl hN
  obtain ⟨obj, wf, hex, hmemR, hall, -⟩ :=
    (L.progCallUN hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herrw
      (by rw [hsp]; exact halign) hroom' hdead' (hκ.2 _ h hh) hmemR0 hargs hsav hplw hinit).2
      e cm' hret
  obtain ⟨kc, hc_eq, hc_ret⟩ := hall _ (L.callerOk_canon hL hh himgF args w)
  have hcond : L.CondR κ (M' + 1) F h args w :=
    ⟨hM, herrw, by rw [hsp]; exact halign, hroom', hdead', vals, cm, cs,
      hmemR0, hargs, hsav, hplw, hinit, e, cm', hret⟩
  have hspT : spv (Arm.set_program (runX (L.machU M' h) kc (enterAt (L.A h) (L.canon h args w)))
      (L.canon h args w).program) = spv w := by
    simp only [spv]
    rw [r_set_program]
    have := hc_ret.ret.sp
    simp only [spv] at this
    rw [this, r_enterAt _ _ (by simp) (by simp)]
    exact (L.callerOk_canon hL hh himgF args w).world.1 _ (by simp [Masked])
  refine ⟨_, _, by rw [progXR, if_pos hcond]; exact hc_eq, by rw [hc_ret.x0]; exact hex,
    ⟨⟨⟨fun a b hv hb => ?_, hmemR.valid, hmemR.symbols⟩, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [← hmemR.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [mem_set_program, hc_ret.mem _ (by simpa using (hmemR.valid a 1 hv).2 0 (by omega))]
  · simpa [Rel.slotReg, hspT] using hslot
  · by_cases hib0 : (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase = 0
    · rw [hib0]; exact outRel_zero _ _ _
    · refine ⟨hout.1, by rw [hspT]; exact hout.2.1, fun a n hv k hk j hj => ?_⟩
      rw [hspT]
      exact hout.2.2 a n (L.crunX_allocs hL hU (.inr ⟨g, hg, hib0⟩) hinit hret
        (.inr ⟨_, rfl⟩) a n hv) k hk j hj
  · rw [hspT, hsp]
  · rw [r_set_program]; exact hc_ret.ret.err

/-- **The external contract of an activation of `g` at depth `M`** under its environment with
unwinding (`xCallsOk`'s counterpart). -/
theorem xCallsOkU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsOk (L.envOfX M g c).toEnv (g.externs.map (·.2))
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XU κ M g F) := by
  intro ext hin gsem sl cm w d uses args vals rvals cm' hgs hd hargs hmr hret hrl
  simp only [Clif.XEnv.toEnv, Option.map_eq_some_iff] at hgs
  obtain ⟨G, hG, rfl⟩ := hgs
  have hret' := Clif.toOutcome_returned hret
  rcases L.envOfX_some hG with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · have hb : L.base.extern ext.name = some fun vals mem => (G vals mem).toOutcome := by
      rw [← hU.envX]; simp [Clif.XEnv.toEnv, hgs]
    obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseX g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
      (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) _ sl cm w d uses args vals rvals cm' hb hd
      hargs hmr hret hrl
    refine ⟨outs, w', ?_, h1, h2, h3⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
    · rw [L.XU_base hpf _ _ F]; exact hx
    · rw [L.XU_none (by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
        rw [LinkSys.lo64_ofX]; exact (L.toLinkSys.find_sym hL ext.name).2 hpf)]
      exact hx
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hsig := hL.declSig g hg ext hin h hpf
    obtain ⟨hpl, he0⟩ := hG0 vals cm (by rw [hret']; intro _ e; cases e)
    rw [hret'] at he0
    obtain ⟨cs, hinit, hrun⟩ := L.linkEnvRX_run hpf hgs he0 (.inl ⟨_, _, rfl⟩)
    rw [hsig] at hargs
    have hsav := L.stackArgsAvoid_decl hL hg hin hpf hmr hinit
    rw [← hname] at hinit
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResultU hL hU hκ ih hg hh (.inr (.inl ⟨ext, hin, hpf⟩)) himgF hroom hdead halign
        hargs hsav hmr hpl hinit hrun
    refine ⟨outs, w', ?_, by rw [hol, hsig], hho, hmr'⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hcol, rfl⟩
    · rw [L.XU_prog hpf]; exact hx
    · have hs : symCallee L.Xb L.P (lo64 (ofX ((L.XU κ M g F).sym ext.name 0))) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
        rw [LinkSys.lo64_ofX]; exact (L.toLinkSys.find_sym hL ext.name).1 h hpf
      have hto : L.IndTo g h := by
        refine ⟨by rw [hname]; exact hdecl, ?_⟩
        rcases hdecl with hdn | ⟨-, -, hall⟩
        · exact .inl ⟨by rw [hname]; exact hdn, ext, hin, hname.symm, hcol⟩
        · obtain ⟨sig, hs, hm⟩ := hall h hpf
          exact .inr ⟨sig, hs, hm, hm.returns_length⟩
      rw [L.XU_ind hs, if_pos ⟨hto, argsAt_regLocs hargs⟩]
      exact hx

/-- **The indirect-call contract of an activation of `g` at depth `M`** under its environment
with unwinding (`xCallsIndOk`'s counterpart). -/
theorem xCallsIndOkU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsIndOk (L.envOfX M g c).toEnv (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XU κ M g F) := by
  intro sig hsig n gsem sl cm w u args vals rvals cm' hgs hsg hu hl8 hall hmr hret hrl hty
  simp only [Clif.XEnv.toEnv, Option.map_eq_some_iff] at hgs
  obtain ⟨G, hG, rfl⟩ := hgs
  have hret' := Clif.toOutcome_returned hret
  rcases L.envOfX_some hG with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · have hs : symCallee L.Xb L.P (lo64 u) = none := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
      rw [hu]; exact (L.toLinkSys.find_sym hL n).2 hpf
    have hb : ({ L.base with sigOf := fun _ => none } : Clif.Env).extern n =
        some fun vals mem => (G vals mem).toOutcome := by
      rw [← hU.envX]; simp [Clif.XEnv.toEnv, hgs]
    obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseXI g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hsig n _ sl cm w u args vals rvals
      cm' hb (fun _ h => nomatch h) hu hl8 hall hmr hret hrl hty
    exact ⟨outs, w', by rw [L.XU_none hs]; exact hx, h1, h2, h3⟩
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    have hnf : ¬ Clif.IndFree g := fun hif => by
      rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
    have hdeclS := hL.indSig g hg hnf
    have hs : symCallee L.Xb L.P (lo64 u) = some h := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
      rw [hu]; exact (L.toLinkSys.find_sym hL h.name).1 h hpf
    obtain ⟨hpl, he0⟩ := hG0 vals cm (by rw [hret']; intro _ e; cases e)
    rw [hret'] at he0
    obtain ⟨cs, hinit, hrun⟩ := L.linkEnvRX_run hpf hgs he0 (.inl ⟨_, _, rfl⟩)
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    have hm : LinkSys.IndSigMatch sig h :=
      hsg h.sig (by simp only [envOfX, Clif.XEnv.toEnv, Clif.linkEnvRX, hpf, Option.map_some])
    obtain ⟨⟨bytes, hb, hb8⟩, hsr⟩ := hdeclS h hh hdecl (.inl ⟨sig, hsig, hm⟩)
    have hargs : ArgsAt h.sig vals args w := (argsAt_iff_of_regs hb hb8 hvl).mpr hall
    have hsav : StackArgsAvoid F h.sig vals w := by
      intro off v hm
      obtain ⟨r, hr⟩ := (locsOf_small hb hb8).2 _ (List.of_mem_zip hm).1
      cases hr
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResultU hL hU hκ ih hg hh (.inr (.inr ⟨hh, hdecl⟩)) himgF hroom hdead halign hargs
        hsav hmr hpl hinit hrun
    refine ⟨outs, w', ?_, ?_, hho, hmr'⟩
    · rw [L.XU_ind hs, if_pos ⟨⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩,
        argsAt_regLocs hargs⟩]
      exact hx
    · rw [hol]
      exact hsr sig hsig hm.ty hm.returns_length

/-- **The raising callees' contract of an activation of `g` at depth `M`** (direct calls) under
its environment with unwinding (`XRaiseOk` for `XRU`). -/
theorem xRaiseOkU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XRaiseOk (L.envOfX M g c) (g.externs.map (·.2))
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XU κ M g F) (L.XRU κ M g F) := by
  intro ext hin G sl cm w d uses args vals e m hG hd hargs hmr hret
  rcases L.envOfX_some hG with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · obtain ⟨obj, w', hx, h1, h2⟩ := hU.baseXR g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
      (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) G sl cm w d uses args vals e m hgs hd
      hargs hmr hret
    refine ⟨obj, w', ?_, h1, h2⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
    · rw [L.XRU_base hpf _ _ F]; exact hx
    · rw [L.XRU_none (by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
        rw [LinkSys.lo64_ofX]; exact (L.toLinkSys.find_sym hL ext.name).2 hpf)]
      exact hx
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hsig := hL.declSig g hg ext hin h hpf
    obtain ⟨hpl, he0⟩ := hG0 vals cm (by rw [hret]; intro _ e; cases e)
    rw [hret] at he0
    obtain ⟨cs, hinit, hrun⟩ := L.linkEnvRX_run hpf hgs he0 (.inr ⟨_, _, rfl⟩)
    rw [hsig] at hargs
    have hsav := L.stackArgsAvoid_decl hL hg hin hpf hmr hinit
    rw [← hname] at hinit
    obtain ⟨obj, w', hx, hex, hmr'⟩ :=
      L.progRaiseResultU hL hU hκ ih hg hh (.inr (.inl ⟨ext, hin, hpf⟩)) himgF hroom hdead
        halign hargs hsav hmr hpl hinit hrun
    refine ⟨obj, w', ?_, hex, hmr'⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hcol, rfl⟩
    · rw [L.XRU_prog hpf]; exact hx
    · have hs : symCallee L.Xb L.P (lo64 (ofX ((L.XU κ M g F).sym ext.name 0))) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
        rw [LinkSys.lo64_ofX]; exact (L.toLinkSys.find_sym hL ext.name).1 h hpf
      have hto : L.IndTo g h := by
        refine ⟨by rw [hname]; exact hdecl, ?_⟩
        rcases hdecl with hdn | ⟨-, -, hall⟩
        · exact .inl ⟨by rw [hname]; exact hdn, ext, hin, hname.symm, hcol⟩
        · obtain ⟨sig, hs, hm⟩ := hall h hpf
          exact .inr ⟨sig, hs, hm, hm.returns_length⟩
      rw [L.XRU_ind hs, if_pos ⟨hto, argsAt_regLocs hargs⟩]
      exact hx

/-- **The raising callees' contract of an activation of `g` at depth `M`** (indirect calls)
under its environment with unwinding (`XRaiseIndOk` for `XRU`). -/
theorem xRaiseIndOkU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XRaiseIndOk (L.envOfX M g c) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XU κ M g F) (L.XRU κ M g F) := by
  intro sig hsig n G sl cm w u args vals e m hG hsg hu hl8 hall hmr hret hty
  rcases L.envOfX_some hG with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · have hs : symCallee L.Xb L.P (lo64 u) = none := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
      rw [hu]; exact (L.toLinkSys.find_sym hL n).2 hpf
    obtain ⟨obj, w', hx, h1, h2⟩ := hU.baseXRI g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hsig n G sl cm w u args vals e m
      hgs (fun _ h => nomatch h) hu hl8 hall hmr hret hty
    exact ⟨obj, w', by rw [L.XRU_none hs]; exact hx, h1, h2⟩
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    have hnf : ¬ Clif.IndFree g := fun hif => by
      rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
    have hdeclS := hL.indSig g hg hnf
    have hs : symCallee L.Xb L.P (lo64 u) = some h := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
      rw [hu]; exact (L.toLinkSys.find_sym hL h.name).1 h hpf
    obtain ⟨hpl, he0⟩ := hG0 vals cm (by rw [hret]; intro _ e; cases e)
    rw [hret] at he0
    obtain ⟨cs, hinit, hrun⟩ := L.linkEnvRX_run hpf hgs he0 (.inr ⟨_, _, rfl⟩)
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    have hm : LinkSys.IndSigMatch sig h :=
      hsg h.sig (by simp only [envOfX, Clif.linkEnvRX, hpf, Option.map_some])
    obtain ⟨⟨bytes, hb, hb8⟩, -⟩ := hdeclS h hh hdecl (.inl ⟨sig, hsig, hm⟩)
    have hargs : ArgsAt h.sig vals args w := (argsAt_iff_of_regs hb hb8 hvl).mpr hall
    have hsav : StackArgsAvoid F h.sig vals w := by
      intro off v hm
      obtain ⟨r, hr⟩ := (locsOf_small hb hb8).2 _ (List.of_mem_zip hm).1
      cases hr
    obtain ⟨obj, w', hx, hex, hmr'⟩ :=
      L.progRaiseResultU hL hU hκ ih hg hh (.inr (.inr ⟨hh, hdecl⟩)) himgF hroom hdead halign
        hargs hsav hmr hpl hinit hrun
    refine ⟨obj, w', ?_, hex, hmr'⟩
    rw [L.XRU_ind hs, if_pos ⟨⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩,
      argsAt_regLocs hargs⟩]
    exact hx

end LinkSysU

end E2E
