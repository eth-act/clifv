import FV.E2E.LinkArmStage2Base

/-!
# The CLIF result of a program call under `CondBT` (SEM1 #537, #680 (3), stage 2)

`progResult` (`LinkArm`) for the slot-byte statement: a call of a function `h` of `P` from a
world of `g` related to the CLIF memory (`RelW`), with the callee's CLIF run under the oracle
(`PlaceAtB`, the slot bytes of `h` the world's, the canonical callee run's table the callee
oracle's) returning: `progXBT` answers, with the CLIF results and memory in `g`'s relation
(`progCallPRBRL` in place of `progCall`). This is `CallPost`'s acceptance of `XPRBT`'s answer
at a program call.

* **`progResultBT`**; `progResultBTR` (determinism `DetPRBR`, #719; `progResultBT` its corollary).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A call of a function `h` of `P` from a world of `g`, under the slot-byte oracle**:
`progXBT` is defined and gives the callee's CLIF results and memory in `g`'s relation. -/
theorem progResultBTRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals rvals : List Clif.Val} {cm' : Clif.Mem} {cs : Clif.State} {ini : Clif.SlotInit}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : L.NeedSlots → L.PlaceAtB cm c ini)
    (hslotb : L.NeedSlots → ∀ a, L.SlotByte h c a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (htab : L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h args w)) (calleeIni h ini))
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : L.crun M cs = .returned rvals cm') :
    ∃ outs w', L.progXBT κ M F h args w = some (outs, w') ∧ outs.length = h.sig.returns.length ∧
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
  have hplw : L.NeedSlots → L.PlaceAtB cm (spv w) ini := fun hN => by rw [hsp]; exact hpl hN
  have hslotw : L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a) := fun hN => by
    rw [hsp]; exact hslotb hN
  obtain ⟨us, outsV, wf, e, hus, hlen, hhold, hmemR, -, -, hcall⟩ :=
    L.progCallPRBRLRU hL hM (ih hM) (hdet hM) hpf ⟨g, hg, hcallee⟩ himgF herrw
      (by rw [hsp]; exact halign) hroom' hdead' hmemR0 hargs hsav hplw hslotw htab hinit hret
  obtain ⟨kc, hc_eq, hc_ret, -⟩ := hcall _ (L.callerOk_canon hL hh himgF args w)
    (L.canon_agree (κ := κ) h args w M).1 (L.canon_agree (κ := κ) h args w M).2
  have hcond : L.CondBT κ M F h args w ∧
      Arm.r .ERR (L.pcall M h (L.canon h args w)) = .None := by
    refine ⟨⟨hM, herrw, by rw [hsp]; exact halign, hroom', hdead', vals, cm, cs, rvals, cm', ini,
      hmemR0, hargs, hsav, fun hN => ⟨hplw hN, hslotw hN⟩, htab, hinit, hret⟩, ?_⟩
    rw [hc_eq, r_set_program]; exact hc_ret.ret.err
  have hspT : spv (L.pcall M h (L.canon h args w)) = spv w := by
    rw [hc_eq]
    simp only [spv]
    rw [r_set_program]
    have := hc_ret.ret.sp
    simp only [spv] at this
    rw [this, r_enterAt _ _ (by simp) (by simp)]
    exact (L.callerOk_canon hL hh himgF args w).world.1 _ (by simp [Masked])
  have hce := clifEntry_initState (f := h) hpf hinit
  have hlr : rvals.length ≤ h.sig.returns.length := by
    have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm' (runInv_entry hh hce) hretN
    have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have := congrArg List.length hrt
    simp only [List.length_map, Clif.AbiParam.tys] at this
    omega
  refine ⟨_, _, by rw [progXBT, if_pos hcond], ?_, ⟨by simpa using hlr, fun j v x hv hx => ?_⟩,
    ⟨⟨⟨fun a b hv hb => ?_, hmemR.valid, hmemR.symbols⟩, ?_, ?_⟩, ?_, hcond.2⟩⟩
  · rw [List.length_map, List.length_range]
  · -- the results
    have hjr : j < rvals.length := (List.getElem?_eq_some_iff.mp hv).1
    have hju : j < us.length := by have := hhold.1; omega
    simp only [List.getElem?_map, List.getElem?_range (by omega : j < h.sig.returns.length),
      Option.map_some, Option.some.injEq] at hx
    subst hx
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq, retX_lt hjr] at this
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

/-- **A call of a function `h` of `P` from a world of `g`, under the slot-byte oracle,
determinism `DetPRBR`** (`progResultBTRU` with `DetPRBR.toU`). -/
theorem progResultBTR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals rvals : List Clif.Val} {cm' : Clif.Mem} {cs : Clif.State} {ini : Clif.SlotInit}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : L.NeedSlots → L.PlaceAtB cm c ini)
    (hslotb : L.NeedSlots → ∀ a, L.SlotByte h c a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (htab : L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h args w)) (calleeIni h ini))
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : L.crun M cs = .returned rvals cm') :
    ∃ outs w', L.progXBT κ M F h args w = some (outs, w') ∧ outs.length = h.sig.returns.length ∧
      PrefixHold rvals outs ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' :=
  L.progResultBTRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg hh hcallee himgF hroom hdead
    halign hargs hsav hmr hpl hslotb htab hinit hret

/-- **A call of a function `h` of `P` from a world of `g`, under the slot-byte oracle**
(`progResultBTR` with `DetPRB`). -/
theorem progResultBT (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals rvals : List Clif.Val} {cm' : Clif.Mem} {cs : Clif.State} {ini : Clif.SlotInit}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : L.NeedSlots → L.PlaceAtB cm c ini)
    (hslotb : L.NeedSlots → ∀ a, L.SlotByte h c a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (htab : L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h args w)) (calleeIni h ini))
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : L.crun M cs = .returned rvals cm') :
    ∃ outs w', L.progXBT κ M F h args w = some (outs, w') ∧ outs.length = h.sig.returns.length ∧
      PrefixHold rvals outs ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' :=
  L.progResultBTR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg hh hcallee himgF hroom hdead
    halign hargs hsav hmr hpl hslotb htab hinit hret

end LinkSys

end E2E
