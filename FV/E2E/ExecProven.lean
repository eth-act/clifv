import FV.E2E.ExecGot
import FV.E2E.ExecGoodReads

/-! # The binary theorem with D2 and D4 from the M6 proof (L3 (c))

`binary_correct_exec_of_insn` (`ExecGot.lean`, D4 proven) assumes D2 (`RunInsnN`) at every state
of the model's run whose step ends without error; `insn_of_good` (`ExecGoodReads.lean`) proves it
from the register-level per-state facts (`GoodAt`, `RL.GoodX.reads`), `got_of_good` proves D4.
`exec_of_runGood` composes them with the lockstep (`exec_of_modelN`) from the model-level facts of
the run, whatever the callees' stack budget: the model's refinement, its difference from the
machine state, and `RunGoodL` of the linked system and of the one keeping the GOT slots. Two
instances, no per-state hypothesis left — `RunOkD` of `binary_correct_exec_static` is proven from
the M6 proof:

* `binary_correct_exec_proven`: no call cycle reachable from the entry, the stack bound
  `stackFn` (`binary_correct_of_checksX`, `runGood_sysS`);
* `binary_correct_exec_depth_proven`: any program, recursive ones included, the stack
  `frameDrop + (D * M + pbMax)` of the depth-`M` budget (`binary_correct_depthX`,
  `runGood_sysS_depth`; #581: the deepest activation's stack probes write up to `pbMax` bytes below
  its frame);
* `binary_correct_exec_peak_proven`: the same with the stack `frameDrop + (D * d + pbMax)` for the run's
  peak call depth `d` (`Clif.DepthLe`) instead of its fuel (`binary_correct_peakX`,
  `runGood_sysS_peak`).
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

/-- **The executable's run from the model-level facts**: for an entry `hent` of the model state,
the model's refinement `hA` of an outcome `o`, the model state differing from `r` only at the
relocated instruction bytes, and (for a returning or trapping `o`) `RunGoodL` of the linked system
and of the one keeping the GOT slots with some callees' budget `K`, the executable machine run
from `r` refines `o`. -/
theorem exec_of_runGood {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) {B : BaseEnv} (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {M K : Nat}
    {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (hent : AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a) {o : Clif.Outcome}
    (hA : ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o)
    (hgood : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)) →
      (sys I B).RunGoodL M f (modelOf I f r) ∧
        (sysS I B f K r (GotSlot I file)).RunGoodL M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I) o := by
  by_cases hout : (∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)
  · obtain ⟨hG, hgS⟩ := hgood hout
    have hL' := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
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
      LinkSys.reachL_extImg (Binary.reachL_F (F' := fun _ => False) hRL)
    exact ⟨insn_of_good hI hcm hF hg (hG _ _ _ _ hRL he), got_of_good hI hbin hgot hX hg (hF g hg)
      (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))⟩
  · cases o with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, rfl⟩) hout
    | trapped c => exact absurd (.inr ⟨c, rfl⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

/-- **The binary theorem about the executable's own words** (L3; `docs/contracts/e2e.md`): under the premises of `binary_correct_of_checks_acyclic`, the outside-code
contract `HooksSim`, the code map check `codeMapB`, the GOT check (`GotOk`, from `gotB`) and the
outside caller keeping the GOT slots off its stack, arguments and live memory (`OutsideAvoids`),
the executable machine run from `r` refines the whole-program CLIF run. -/
theorem binary_correct_exec_proven {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (StackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨hA, hd, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := okB_sound hI (baseOk_F (F' := worldF I f (StackBound.bud I f) r) hB)
    fun _ h => .inr h
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
  exact exec_of_runGood hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS hI hbin hB hn hf M hX ho hav hr htr hout⟩

/-- **The binary theorem about the executable's own words for any program**, recursive ones
included: `binary_correct_exec_proven` without the call-graph premise (`¬ CycleFrom`), the outside
caller providing the stack `frameDrop + (D * M + pbMax I)` of the depth-`M` budget (#581: with the
stack probes of the deepest activation; every call level at most
`D` bytes, `LinkSys.budget_K`) instead of the stack bound `stackFn` of a non-recursive program.
`M` is the CLIF run's fuel (at most `M + 1` steps of the whole-program run) and the depth of the
proof's linked machine: the stack is proportional to the fuel, not to the run's actual peak call
depth. -/
theorem binary_correct_exec_depth_proven {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * M + pbMax I)) r
      args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * M + pbMax I)) r args
      cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hfacts := binFacts_of_checks hI hbin
  obtain ⟨hA, hd, hG⟩ := binary_correct_depthX hfacts B hB hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := okB_sound hI (baseOk_F (F' := worldF I f (I.D * M + pbMax I) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
  exact exec_of_runGood hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS_depth hI hbin hB hfm M hX ho hav hr htr hout⟩

/-- **The binary theorem about the executable's own words for the run's peak call depth** (L1d):
`binary_correct_exec_depth_proven` with the stack `frameDrop + (D * d + pbMax I)`, where `d` bounds the call
depth of the whole-program CLIF run (`Clif.DepthLe`: every state it reaches has at most `d`
callers), independent of its fuel `F` (at most `F + 1` steps). The run premise `TrapsExplicit` is
under `Clif.linkEnvD` (program callees with fuel `F` and at most `d - 1` callers of their own). -/
theorem binary_correct_exec_peak_proven {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r
      args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (F + 1) cs) := by
  have hfacts := binFacts_of_checks hI hbin
  obtain ⟨hA, hdiff, hG⟩ := binary_correct_peakX hfacts B hB hf F d hX ho hr hd htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := okB_sound hI (baseOk_F (F' := worldF I f (I.D * d + pbMax I) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
  exact exec_of_runGood hI hcm hbin hgot hB hH hfm hX hent hdiff hA fun hout =>
    ⟨hG hout, runGood_sysS_peak hI hbin hB hfm F d hX ho hav hr hd htr hout⟩

end E2E.ExecBytes
