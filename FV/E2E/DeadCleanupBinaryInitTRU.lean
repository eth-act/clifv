import FV.E2E.DeadCleanupBinaryInitRU
import FV.E2E.LinkArmThmPRBGT

/-!
# The executable machine on a trapping run under the slot-byte oracle, `InitOkRU` (SEM1 #537, #732)

`binary_correct_exec_initRU` (`DeadCleanupBinaryInitRU`) covers returning CLIF runs placed with the
machine's own slot table. With the per-state facts of a trapping run (`ThmPRBGT`,
`backend_correct_program_initETXRU`) the same proof covers trapping runs (their traps explicit,
as `binary_correct_exec_proven`'s `TrapsExplicit`):

* `model_init_sysSTRU`: the model's trapping run in the system keeping the slots `S`, with its
  per-state facts;
* **`binary_correct_exec_initTRU`**: the executable machine run from `r` reaches the trap site of a
  trapping whole-program CLIF run (`ExecRefines … (.trapped c)`), under `InitOkRU`.
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **`model_init_sysSRU` for a trapping run.** -/
theorem model_init_sysSTRU {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hbin : E2E.DeadCleanupBinCheck.BinOk I D file) (hB : BaseOk (sys I B)) {n : String}
    (hn : DeadCleanupStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOkRU (sysS I B f r S) (kapW I B f r))
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (.trapped c) ∧
    (sysS I B f r S).RunGoodL M f (modelOf I f r) := by
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)).Img a →
      worldF I f (DeadCleanupStackBound.bud I f) r a := fun _ h => .inr h
  have hL0 := okBCleanup_sound hI hB' himgF
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, -, hbe, hargs, hsav, hrel, hpl⟩ := premisesB hL0 hfm hro ho hr
  have hL : (sysS I B f r S).Ok := LinkSys.Ok.extImg hL0
    (fun a ha => mem_modelOf_img ha) fun a ha => by
      rcases ha with ha | ha
      · exact .inr (.inl ha)
      · exact .inr (.inr ha)
  have hκf := kapW_eq B hn hf r M
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_facts hL0 hfm
  have hN := ho.stack
  have hN' : frameDrop (art I f).af + DeadCleanupStackBound.bud I f ≤ (spv r).toNat := hN
  have hsp := (spv r).isLt
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  refine (fun hAG => ⟨by rw [← mach_sysS f r S]; exact hAG.1, hAG.2⟩)
    (backend_correct_program_initETXRU (sysS I B f r S) hL (κ := kapW I B f r)
    ((DeadCleanupStackBound.budget_of hI B (worldF I f (DeadCleanupStackBound.bud I f) r)).extImg _ _ _)
    hIO.baseRet hIO.retCount hIO.det hIO.detTab hIO.detTabR hIO.hooks hfm M hent
    (by rw [hκf]; exact ⟨hres, by rw [← hκf]; exact (DeadCleanupStackBound.budget_of hI B
      (worldF I f (DeadCleanupStackBound.bud I f) r)).2 M f hfm⟩) (by rw [hκf]; rfl)
    (fun a ha => ?_) (fun a _ => rfl) hbe hargs
    hr.entry (fun off v hm k hk hx => ?_)
    ⟨⟨hrel.1.bytes, fun a n hv => ?_, hrel.1.symbols⟩, hrel.2.1, hrel.2.2.1, fun j hj => ?_,
      hrel.2.2.2.2⟩ (fun hN => by rw [iniOf_sysS]; exact hpl hN) htr hrun)
  · rw [hκf]
    rcases ha with ha | ha
    · exact hgfree a ha
    · rw [spv_modelOf]; exact hav.stack a ha
  · rcases hx with hx | hx
    · exact hsav off v hm k hk hx
    · rw [spv_modelOf] at hx; exact hav.args off v hm k hk hx
  · obtain ⟨hfit, hk⟩ := hrel.1.valid a n hv
    exact ⟨hfit, fun k hkn => not_worldFS (hk k hkn) (hav.valid a n hv k hkn)⟩
  · refine not_worldFS (hrel.2.2.2.1 j hj) fun hS => hav.stack _ hS ?_
    change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
    rw [hspb]
    show StackBelow (frameDrop (art I f).af + DeadCleanupStackBound.bud I f) _ _
    simp only [StackBelow, BitVec.toNat_add, BitVec.toNat_ofNat, hspbN]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The binary theorem about the executable's own words under the slot-byte oracle, trapping
runs, `InitOkRU`** (module doc). -/
theorem binary_correct_exec_initTRU {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B)) (hH : HooksSim I B) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOkRU (sysS I B f r (GotSlot I file)) (kapW I B f r))
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (.trapped c) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨hA, hgS⟩ := model_init_sysSTRU hI hbin hB hn hf M hX ho hav hr hIO htr hrun
  have hG := runGoodL_of_sysS hgS
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  have hB'' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have hL0 := okBCleanup_sound hI hB'' fun _ h => .inr h
  obtain ⟨hent, -⟩ := premisesB hL0 hfm hro ho hr
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
  have hra : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hent.raOutside
  have hreads : RunReadsN I B file M f (modelOf I f r) := fun M' g t hR he => by
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm hG (raNotSecond_top (hF f hfm) hra)
    have hRL' : (sysS I B f r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t :=
      LinkSys.reachL_extImg (F := worldFS I f (DeadCleanupStackBound.bud I f) r (GotSlot I file))
        (S := GotSlot I file) (m := (modelOf I f r).mem)
        (E2E.DeadCleanupBinary.reachL_F (F := worldF I f (DeadCleanupStackBound.bud I f) r)
          (F' := fun _ => False) hRL)
    have hg := reachN_mem hR hfm
    exact ⟨insn_of_good hI hcm hF hg (hG _ _ _ _ hRL he),
      got_of_good hI hbin hgot hX hg (hF g hg) (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))⟩
  exact exec_of_modelN hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside
    (modelOf_diff hfacts hX f)
    (runOkSN_of_n hI hcm hF hH hfm
      (runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg) hfm hra hG hreads)) hA

end E2E.DeadCleanupExecBytes
