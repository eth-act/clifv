import FVTest.Link.MidSourceWitness
import FVTest.Link.MidSourceTBWitness
import FV.Link.MidSourceRoutesSyms
import FV.Link.MidSourceTBSyms

/-! # Non-vacuity of the `…MidS` route theorems on an executable (#1119, hoisting mode)

**Witness file** (no `native_decide` of its own; it reuses the decided facts of
`FVTest/Link/MidSourceWitness.lean` and `FVTest/Link/MidSourceTBWitness.lean`). On those
executables (the optimised function's code in the region, the theorem about the unoptimised
function's run), the premise of the `…MidS` theorems, `Opt.FunsSimMUAt syms P0.funcs Q.funcs` at the
route input's symbol table, holds (every `ValidatedC` pair simulates at every table:
`ValidatedC.funsSimMU`, `FunsSimMU.at`), so `ReturnPinCompilerWith.attempt_correct_sourceMidS` and
`SemanticCompilerWith.attemptT_correct_sourceTBMidS` apply with every premise `lean-link` decides
discharged. A pair only the hoisting mode accepts (`Link.midPairSymsB`) is shown simulating at the
executable's symbol table in `FVTest/Link/MidSymsWitness.lean`.
-/

namespace Link.MidSourceWitness
set_option autoImplicit false
open Backend E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Opt.Legalize128
open FVTest.Backend.MidValPassWitness (srcF srcG fSrc gOpt)

/-- **`ReturnPinCompilerWith.attempt_correct_sourceMidS` is not vacuous**: on the executable of
`Link.MidSourceWitness`, its premise at the route input's symbol table holds (from `ValidatedC`,
`ValidatedC.funsSimMU`, `FunsSimMU.at`; what `Link.midValidatedSymsB` decides there). -/
theorem correct_sourceMidS_applies : ∃ file, ReturnPinCompilerWith.attempt lower spec file0 true = .ok file ∧
    S0.input0.srcProg.func? name = some fSrc ∧ S1.input0.srcProg.func? name = some gOpt ∧
    fSrc ≠ gOpt ∧
    ∀ (B : BaseEnv), BaseOk (sys input B) → HooksSim input B → Opt.EnvKeepsSymbols B.env →
    ((∃ f ∈ S1.input0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env) →
    ((∃ g ∈ (prog input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none) →
    ∀ {f' : Clif.Function}, (prog input).func? name = some f' →
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls input input.results) f' →
    ∀ {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State},
    (imageOf file).Intact r →
    OutsideCall input (BinCheck.roByte input spec.data) f'
      (SemanticStackBound.stackFn input f') r args' cs'.mem →
    ClifRun input B f' r args' cs' →
    ClifEntry fSrc args cs →
    Opt.Legal.ExpRel ((Opt.Legal.groups fSrc.sig.params).getD []) args args' →
    cs'.frame.slots = cs.frame.slots → cs'.mem = cs.mem →
    (∀ s', Opt.Legal.SReach B.env S1.input0.srcProg (midEntry gOpt cs) s' →
      Opt.Legal.MemBounded s'.mem) →
    ∀ (M : Nat), ∀ vals cm, Clif.runLoop B.env S0.input0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups fSrc.sig.returns).getD []) vals vals' ∧
        ExecRefines (art input f').fb (art input f').base (xreg 30 r) (step input B file) r
          (BinCheck.RelocAtWithResults input input.results) (.returned vals' cm) := by
  obtain ⟨⟨file, hfile⟩, hsrc, hv, hf, hg, hne⟩ := parts
  refine ⟨file, hfile, hf, hg, hne, ?_⟩
  intro B hB hH hkeep hlegal hsig f' hf' hc r args args' cs cs' hX ho hr hcs hexp hsl hmem hbnd M
  exact (ReturnPinCompilerWith.attempt_correct_sourceMidS hfile hcp hsrc (hv.funsSimMU.at _) B hB hH hkeep hlegal hsig
    hf hg hf' hc hX ho hr hcs hexp hsl hmem hbnd M).1

end Link.MidSourceWitness

namespace E2E.MidSourceTBWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Opt.Legalize128
open E2E.I128TryIndTWitness (fStock lower spec file0 input)

/-- **`SemanticCompilerWith.attemptT_correct_sourceTBMidS` is not vacuous**: on the executable of
`E2E.MidSourceTBWitness`, its premise at the route input's symbol table holds (from `ValidatedC`,
`ValidatedC.funsSimMU`, `FunsSimMU.at`). -/
theorem correct_sourceTBMidS_applies : ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file ∧
    P0.func? name = some fNop ∧ input.toLinkInput.srcProg.func? name = some gS ∧ fNop ≠ gS ∧
    ∀ (B : BaseEnv), BaseOk (SemanticBinary.sys input B) → SemanticExecBytes.HooksSim input B →
    Opt.EnvKeepsSymbols B.env →
    ((∃ f ∈ input.toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env) →
    ((∃ g ∈ (SemanticBinary.prog input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none) →
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls input input.results) (legalize gS) →
    ∀ {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State},
    (SemanticBinary.imageOf file).Intact r →
    SemanticBinary.OutsideCall input (BinCheck.roByte input spec.data) (legalize gS)
      (SemanticStackBound.stackFn input (legalize gS)) r args' cs'.mem →
    SemanticBinary.ClifRun input B (legalize gS) r args' cs' →
    ClifEntry fNop args cs →
    Opt.Legal.ExpRel ((Opt.Legal.groups fNop.sig.params).getD []) args args' →
    cs'.frame.slots = cs.frame.slots → cs'.mem = cs.mem →
    (∀ s', Opt.Legal.SReach B.env input.toLinkInput.srcProg (midEntry gS cs) s' →
      Opt.Legal.MemBounded s'.mem) →
    ∀ (M : Nat), ∀ vals cm, Clif.runLoop B.env P0 M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups fNop.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (SemanticBinary.art input (legalize gS)).fb
          (SemanticBinary.art input (legalize gS)).base (xreg 30 r)
          (SemanticExecBytes.step input B file) r
          (BinCheck.RelocAtWithResults input input.results) (.returned vals' cm) := by
  obtain ⟨⟨file, hfile⟩, hsrc, -⟩ := E2E.I128TryIndTWitness.parts
  obtain ⟨hv, hf, hg, hne⟩ := parts
  refine ⟨file, hfile, hf, hg, hne, ?_⟩
  intro B hB hH hkeep hlegal hsig hc r args args' cs cs' hX ho hr hcs hexp hsl hmem hbnd M
  exact (SemanticCompilerWith.attemptT_correct_sourceTBMidS hfile hsrc (hv.funsSimMU.at _) B hB hH hkeep hlegal hsig
    hf hg hc hX ho hr hcs hexp hsl hmem hbnd M).1

end E2E.MidSourceTBWitness
