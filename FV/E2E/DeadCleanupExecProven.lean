import FV.E2E.DeadCleanupExecGot
import FV.E2E.DeadCleanupExecGoodReads
import FV.E2E.ExecProven
import FV.E2E.DeadCleanupBinary
import FV.E2E.DeadCleanupBinCheck

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-- **The binary theorem about the executable's own words** (L3; `docs/contracts/e2e.md`): under the premises of `binary_correct_of_checks_acyclic`, the outside-code
contract `HooksSim`, the code map check `codeMapB`, the GOT check (`GotOk`, from `gotB`) and the
outside caller keeping the GOT slots off its stack, arguments and live memory (`OutsideAvoids`),
the executable machine run from `r` refines the whole-program CLIF run. -/
theorem binary_correct_exec_proven {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanup I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (E2E.DeadCleanupBinCheck.RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · have hfm := (Clif.Program.func?_some hf).1
    have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) := baseOk_F hB
    have hL := okBCleanup_sound hI hB' fun _ h => .inr h
    have hfacts := binFacts_of_checks hI hbin
    have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
      hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
    obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
    have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    refine binary_correct_exec_of_insn hI hcm hbin hgot B hB hH hf hc M hX ho hav hr htr
      fun M' g t hR he => ?_
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm (hG hout) (raNotSecond_top (hF f hfm) hra)
    exact insn_of_good hI hcm hF (reachN_mem hR hfm) (hG hout _ _ _ _ hRL he)
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

end E2E.DeadCleanupExecBytes
