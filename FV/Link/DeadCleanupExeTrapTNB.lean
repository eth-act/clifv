import FV.Link.DeadCleanupExeTrapT
import FV.Link.DeadCleanupExeTrapNB

/-! # The shipped compiler's callee-trap source theorems (`try_call` callees included) without
# the memory-bound premise (A2/B1)

`Link.DeadCleanup.compileExe_correct_source_trapT{,_peak}` (S9e, `compileExeU`) take the run
premise `∀ s', SReach B.env S.inputCleanup.srcProg cs s' → MemBounded s'.mem`. Their variants
here, `compileExe_correct_source_trapT_nobnd` and `compileExe_correct_source_trapT_peak_nobnd`,
have the same premises without it, as `compileExe_correct_source{,_peak}_nobnd`
(`DeadCleanupExeSourceNB.lean`):

* a program mentioning `i128`: the bound is derived (`srcBounded_acyclic`, `srcBounded_peak`, for
  `compileExe`, which `compileExeU` decides first);
* a program without `i128`: the source run is the compiled program's run from the same state
  (`ident_entry`), so a trap follows from `compileExe_correct_trapT{,_peak}` directly.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- `compileExe_correct_source_trapT` without the premise that the source run's memories lie
below `2^64` (A2/B1). -/
theorem compileExe_correct_source_trapT_nobnd {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ K, (sys S.inputCleanup B).std.TrapsDT K (legalize f) cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have he := (compileExeU_spec h).1
  by_cases hm : ∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true
  · exact compileExe_correct_source_trapT h hsrc B hB hH hBT hlegal hsig hf hc hX ho hr hcs
      hexp hsl hmem (srcBounded_acyclic he hsrc B hB hlegal hsig hm hf hc ho hr hcs hmem) M
  obtain ⟨hpP, hcseq, hf'⟩ := ident_entry hm hf hr hcs hexp hsl hmem
  refine ⟨(compileExe_correct_source_nobnd he hsrc B hB hH hlegal hsig hf hc hX ho hr hcs hexp
    hsl hmem M).1, fun htr _ c hrun => ?_⟩
  cases M with
  | zero => simp at hrun
  | succ K =>
    have hK : Clif.runLoop B.env (prog S.inputCleanup) (K + 1) cs' = .trapped c := by
      rw [hpP, hcseq]; exact hrun
    have H := compileExe_correct_trapT h B hB hH hBT hf' hc K hX ho hr (htr K)
    rw [hK] at H
    exact H

/-- `compileExe_correct_source_trapT_peak` without the premise that the source run's memories lie
below `2^64` (A2/B1). -/
theorem compileExe_correct_source_trapT_peak_nobnd {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (frameDrop (art S.inputCleanup (legalize f)).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hd : Clif.DepthLe B.env S.inputCleanup.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, ((sys S.inputCleanup B).peak F).TrapsDT d (legalize f) cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have he := (compileExeU_spec h).1
  by_cases hm : ∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true
  · exact compileExe_correct_source_trapT_peak h hsrc B hB hH hBT hlegal hsig hf d hX ho hr
      hcs hexp hsl hmem (srcBounded_peak he hsrc B hB hlegal hsig hm hf d ho hr hcs hmem hd) hd M
  obtain ⟨hpP, hcseq, hf'⟩ := ident_entry hm hf hr hcs hexp hsl hmem
  have hdT : Clif.DepthLe B.env (prog S.inputCleanup) d cs' := by rw [hpP, hcseq]; exact hd
  refine ⟨(compileExe_correct_source_peak_nobnd he hsrc B hB hH hlegal hsig hf d hX ho hr hcs hexp
    hsl hmem hd M).1, fun htr _ c hrun => ?_⟩
  cases M with
  | zero => simp at hrun
  | succ K =>
    have hK : Clif.runLoop B.env (prog S.inputCleanup) (K + 1) cs' = .trapped c := by
      rw [hpP, hcseq]; exact hrun
    have H := compileExe_correct_trapT_peak h B hB hH hBT hf' K d hX ho hr hdT (htr K)
    rw [hK] at H
    exact H

end Link.DeadCleanup
