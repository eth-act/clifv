import FV.E2E.ExecGotT
import FV.E2E.ExecGoodReadsT
import FV.E2E.BinCheckT
import FV.E2E.BinaryGoodT
import FV.E2E.BinaryT
import FV.E2E.ExecBytesT
import FV.E2E.ExecGoodRunT
import FV.E2E.ExecRunNT
import FV.E2E.ExecStaticT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.LinkGoodT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.ExecProven` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.ExecProven` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.ExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

/-- **The executable's run from the model-level facts**: for an entry `hent` of the model state,
the model's refinement `hA` of an outcome `o`, the model state differing from `r` only at the
relocated instruction bytes, and (for a returning or trapping `o`) `RunGoodL` of the linked system
and of the one keeping the GOT slots with some callees' budget `K`, the executable machine run
from `r` refines `o`. -/
theorem exec_of_runGoodT {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBT I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) {B : BaseEnv} (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {M K : Nat}
    {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (hent : AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a) {o : Clif.Outcome}
    (hA : ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o)
    (hgood : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)) →
      (sys I B).RunGoodL M f (modelOf I f r) ∧
        (sysS I B f K r (GotSlot I file)).RunGoodL M f (modelOf I f r)) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I) o := by
  by_cases hout : (∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)
  · obtain ⟨hG, hgS⟩ := hgood hout
    have hL' := okB_soundT hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOkT hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    refine exec_of_modelNT hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside hd
      (runOkSN_of_nT hI hcm hF hH hfm (runOkN_of_goodT hI hcm hF (fun g hg => destsInt_of_okT hL' hg)
        hfm hra hG fun M' g t hR he => ?_)) hA
    obtain ⟨c', hRL, -⟩ := reachL_of_reachNT hI hcm hF hR hfm hG (raNotSecond_top (hF f hfm) hra)
    have hg := reachN_mem hR hfm
    have hRL' : (sysS I B f K r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t :=
      LinkSys.reachL_extImg (Binary.reachL_F (F' := fun _ => False) hRL)
    exact ⟨insn_of_goodT hI hcm hF hg (hG _ _ _ _ hRL he), got_of_goodT hI hbin hgot hX hg (hF g hg)
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
theorem binary_correct_exec_provenT {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBT I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (StackBound.goodN_iffT hI).2 ⟨f, hf, hc⟩
  obtain ⟨hA, hd, hG⟩ := binary_correct_of_checksXT hI hbin B hB hn hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := okB_soundT hI (baseOk_F (F' := worldF I f (StackBound.bud I f) r) hB)
    fun _ h => .inr h
  have hfacts := binFacts_of_checksT hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesT hL hfm hro ho hr
  exact exec_of_runGoodT hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysST hI hbin hB hn hf M hX ho hav hr htr hout⟩

/-- **The binary theorem about the executable's own words for any program**, recursive ones
included: `binary_correct_exec_provenT` without the call-graph premise (`¬ CycleFrom`), the outside
caller providing the stack `frameDrop + D * M` of the depth-`M` budget (every call level at most
`D` bytes, `LinkSys.budget_KT`) instead of the stack bound `stackFn` of a non-recursive program.
`M` is the CLIF run's fuel (at most `M + 1` steps of the whole-program run) and the depth of the
proof's linked machine: the stack is proportional to the fuel, not to the run's actual peak call
depth. -/
theorem binary_correct_exec_depth_provenT {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBT I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hfacts := binFacts_of_checksT hI hbin
  obtain ⟨hA, hd, hG⟩ := binary_correct_depthXT hfacts B hB hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := okB_soundT hI (baseOk_F (F' := worldF I f (I.D * M) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesT hL hfm hro ho hr
  exact exec_of_runGoodT hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS_depthT hI hbin hB hfm M hX ho hav hr htr hout⟩

/-- **The binary theorem about the executable's own words for the run's peak call depth** (L1d):
`binary_correct_exec_depth_provenT` with the stack `frameDrop + D * d`, where `d` bounds the call
depth of the whole-program CLIF run (`Clif.DepthLe`: every state it reaches has at most `d`
callers), independent of its fuel `F` (at most `F + 1` steps). The run premise `TrapsExplicit` is
under `Clif.linkEnvD` (program callees with fuel `F` and at most `d - 1` callers of their own). -/
theorem binary_correct_exec_peak_provenT {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBT I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (F + 1) cs) := by
  have hfacts := binFacts_of_checksT hI hbin
  obtain ⟨hA, hdiff, hG⟩ := binary_correct_peakXT hfacts B hB hf F d hX ho hr hd htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := okB_soundT hI (baseOk_F (F' := worldF I f (I.D * d) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesT hL hfm hro ho hr
  exact exec_of_runGoodT hI hcm hbin hgot hB hH hfm hX hent hdiff hA fun hout =>
    ⟨hG hout, runGood_sysS_peakT hI hbin hB hfm F d hX ho hav hr hd htr hout⟩
end E2E.ExecBytes
