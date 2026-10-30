import FV.E2E.ExecTlsSim
import FV.E2E.ExecGot
import FV.E2E.ExecGoodReads

/-! # The binary theorems without the TLS hook (T1)

`binary_correct_exec_proven_tls` (and `_depth_`, `_peak_`) are `binary_correct_exec_proven`
(`_depth_`, `_peak_`) for the hook-free executable machine `stepT`: the processor on every word
of the program, lld's local-exec TLS words included; only calls of code outside the program are
hooks. The TLS hook and its trusted contract `TlsOk` are gone: the model machine of the proof
uses the base environment `leBase I B file`, whose TLS hook meets `TlsOk` and `HooksSim` by
construction (`tlsOk_le`, `hooksSim_le`). What remains is the loader's thread-pointer contract
`TlsLoader`: the entry state's `TPIDR_EL0`, kept by code outside the program, and the running
thread's instance of each thread-local variable at `TPIDR_EL0 + TpOff`, where the CLIF semantics
has it.

`exec_of_runGoodT` is `exec_of_runGood` for `stepT`: D1 of the TLS sequence (`RunTlsN`) comes
from the same `RunGoodL` (`runTlsN_of_good`).
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

/-- **The hook-free executable's run from the model-level facts** (`exec_of_runGood` for
`stepT`, the model machine of `leBase I B file`). -/
theorem exec_of_runGoodT {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) {B : BaseEnv}
    (hB : BaseOk (sys I (leBase I B file)))
    (hHc : ∀ d m e, Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e))
    {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {M K : Nat}
    {r : Arm.ArmState} (hX : (imageOf file).Intact r) (hL : TlsLoader I B file r)
    (hent : AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a) {o : Clif.Outcome}
    (hA : ArmRefines (art I f).fb (art I f).base (xreg 30 r)
      ((sys I (leBase I B file)).mach M f) (modelOf I f r) o)
    (hgood : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)) →
      (sys I (leBase I B file)).RunGoodL M f (modelOf I f r) ∧
        (sysS I (leBase I B file) f K r (GotSlot I file)).RunGoodL M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (stepT I B file) r (RelocAt I) o := by
  by_cases hout : (∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)
  · obtain ⟨hG, hgS⟩ := hgood hout
    have hH := hooksSim_le (file := file) hHc
    have hL' := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    refine exec_of_modelT hF (fun g hg => tlsClosed_art hI hg)
      (fun g hg a i hi => siteAt_static hI hcm hF hg hi) hL hfm
      (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside hd
      (runOkSN_of_n hI hcm hF hH hfm (runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg)
        hfm hra hG fun M' g t hR he => ?_))
      (runTlsN_of_good hI hcm hF hfm hra hG) hA
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm hG (raNotSecond_top (hF f hfm) hra)
    have hg := reachN_mem hR hfm
    have hRL' : (sysS I (leBase I B file) f K r (GotSlot I file)).ReachL M f (modelOf I f r)
        M' g c' t :=
      LinkSys.reachL_extImg (Binary.reachL_F (F' := fun _ => False) hRL)
    exact ⟨insn_of_good hI hcm hF hg (hG _ _ _ _ hRL he), got_of_good hI hbin hgot hX hg (hF g hg)
      (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))⟩
  · cases o with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, rfl⟩) hout
    | trapped c => exact absurd (.inr ⟨c, rfl⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

/-- **The binary theorem about the executable's own words, TLS included** (T1;
`docs/contracts/e2e.md`, "`tls_value`"): `binary_correct_exec_proven` for the hook-free machine
`stepT` (the TLS sequence runs on the processor, lld's local-exec words), with the base
environment `leBase I B file` in `BaseOk` (its TLS clause holds, `tlsOk_le`), `HooksSim` only
for the calls of code outside the program, and the loader's thread-pointer contract
`TlsLoader`. -/
theorem binary_correct_exec_proven_tls {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I (leBase I B file)))
    (hHc : ∀ d m e, Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hL : TlsLoader I B file r) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (stepT I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hr' : ClifRun I (leBase I B file) f r args cs := ⟨hr.entry, hr.slots, hr.place⟩
  have htr' : TrapsExplicit (Clif.linkEnvN (prog I) (leBase I B file).env M) (prog I).bare cs :=
    htr
  have hn := (StackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨hA, hd, hG⟩ := binary_correct_of_checksX hI hbin _ hB hn hf M hX ho hr' htr'
  have hfm := (Clif.Program.func?_some hf).1
  have hL0 := okB_sound hI (baseOk_F (F' := worldF I f (StackBound.bud I f) r) hB)
    fun _ h => .inr h
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL0 hfm hro ho hr'
  exact exec_of_runGoodT hI hcm hbin hgot hB hHc hfm hX hL hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS hI hbin hB hn hf M hX ho hav hr' htr' hout⟩

/-- **`binary_correct_exec_depth_proven` without the TLS hook** (any program, recursive ones
included; the stack `frameDrop + D * M`). -/
theorem binary_correct_exec_depth_proven_tls {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I (leBase I B file)))
    (hHc : ∀ d m e, Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hL : TlsLoader I B file r) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (stepT I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hr' : ClifRun I (leBase I B file) f r args cs := ⟨hr.entry, hr.slots, hr.place⟩
  have htr' : TrapsExplicit (Clif.linkEnvN (prog I) (leBase I B file).env M) (prog I).bare cs :=
    htr
  have hfacts := binFacts_of_checks hI hbin
  obtain ⟨hA, hd, hG⟩ := binary_correct_depthX hfacts _ hB hf M hX ho hr' htr'
  have hfm := (Clif.Program.func?_some hf).1
  have hL0 := okB_sound hI (baseOk_F (F' := worldF I f (I.D * M) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL0 hfm hro ho hr'
  exact exec_of_runGoodT hI hcm hbin hgot hB hHc hfm hX hL hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS_depth hI hbin hB hfm M hX ho hav hr' htr' hout⟩

/-- **`binary_correct_exec_peak_proven` without the TLS hook** (the stack `frameDrop + D * d`
for the run's peak call depth `d`). -/
theorem binary_correct_exec_peak_proven_tls {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I (leBase I B file)))
    (hHc : ∀ d m e, Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    (hL : TlsLoader I B file r) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (stepT I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (F + 1) cs) := by
  have hr' : ClifRun I (leBase I B file) f r args cs := ⟨hr.entry, hr.slots, hr.place⟩
  have hd' : Clif.DepthLe (leBase I B file).env (prog I) d cs := hd
  have htr' : TrapsExplicit (Clif.linkEnvD (prog I) (leBase I B file).env F d) (prog I).bare cs :=
    htr
  have hfacts := binFacts_of_checks hI hbin
  obtain ⟨hA, hdiff, hG⟩ := binary_correct_peakX hfacts _ hB hf F d hX ho hr' hd' htr'
  have hfm := (Clif.Program.func?_some hf).1
  have hL0 := okB_sound hI (baseOk_F (F' := worldF I f (I.D * d) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL0 hfm hro ho hr'
  exact exec_of_runGoodT hI hcm hbin hgot hB hHc hfm hX hL hent hdiff hA fun hout =>
    ⟨hG hout, runGood_sysS_peak hI hbin hB hfm F d hX ho hav hr' hd' htr' hout⟩

end E2E.ExecBytes
