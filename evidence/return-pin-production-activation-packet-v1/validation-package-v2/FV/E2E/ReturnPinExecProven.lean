import FV.E2E.ReturnPinExecGot

namespace E2E.ReturnPinExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.SemanticExecBytes
set_option autoImplicit false
set_option Elab.async false
variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}
theorem exec_of_runGood {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) {B : BaseEnv} (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {M K : Nat}
    {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (hent : AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAtWithResults I I.results a) {o : Clif.Outcome}
    (hA : ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o)
    (hgood : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)) →
      (sys I B).RunGoodL M f (modelOf I f r) ∧
        (sysS I B f K r (GotSlot I file)).RunGoodL M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results) o := by
  by_cases hout : (∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)
  · obtain ⟨hG, hgS⟩ := hgood hout
    have hL' := ReturnPinBinary.okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    refine exec_of_modelN hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside hd
      (runOkSN_of_n hI hcm hF hH hfm (runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg)
        hfm hra hG fun M' g t hR he => ?_)) hA
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm hG (raNotSecond_top (hF f hfm) hra)
    have hg := reachN_mem hR hfm
    have hRL' : (sysS I B f K r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t :=
      LinkSys.reachL_extImg_semantic (SemanticBinary.reachL_F (F' := fun _ => False) hRL)
    exact ⟨insn_of_good hI hcm hF hg (hG _ _ _ _ hRL he), got_of_good hI hbin hgot hX hg (hF g hg)
      (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))⟩
  · cases o with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, rfl⟩) hout
    | trapped c => exact absurd (.inr ⟨c, rfl⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial


theorem binary_correct_exec_proven {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (ReturnPinStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨hA, hd, hG⟩ := ReturnPinBinary.binary_correctX (ReturnPinBinary.binFacts_of_checks hI hbin) B hB hn hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := ReturnPinBinary.okB_sound hI (baseOk_F (F' := worldF I f (SemanticStackBound.bud I f) r) hB)
    fun _ h => .inr h
  have hfacts := ReturnPinBinary.binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_returnPins hL) hfm hro ho hr
  exact exec_of_runGood hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS hI hbin hB hn hf M hX ho hav hr htr hout⟩


theorem binary_correct_exec_depth_proven {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hfacts := ReturnPinBinary.binFacts_of_checks hI hbin
  obtain ⟨hA, hd, hG⟩ := ReturnPinBinary.binary_correct_depthX hfacts B hB hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := ReturnPinBinary.okB_sound hI (baseOk_F (F' := worldF I f (I.D * M) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_returnPins hL) hfm hro ho hr
  exact exec_of_runGood hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS_depth hI hbin hB hfm M hX ho hav hr htr hout⟩


theorem binary_correct_exec_peak_proven {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results)
      (Clif.runLoop B.env (prog I) (F + 1) cs) := by
  have hfacts := ReturnPinBinary.binFacts_of_checks hI hbin
  obtain ⟨hA, hdiff, hG⟩ := ReturnPinBinary.binary_correct_peakX hfacts B hB hf F d hX ho hr hd htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := ReturnPinBinary.okB_sound hI (baseOk_F (F' := worldF I f (I.D * d) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_returnPins hL) hfm hro ho hr
  exact exec_of_runGood hI hcm hbin hgot hB hH hfm hX hent hdiff hA fun hout =>
    ⟨hG hout, runGood_sysS_peak hI hbin hB hfm F d hX ho hav hr hd htr hout⟩


end E2E.ReturnPinExecBytes
