import FV.Link.SemanticExeSourceTCp
import FV.Link.CpSourceWitness

/-! # Non-vacuity of `attemptT_correct_source{,_peak}Cp` (#1100)

The bundle of `Link.CpSourceWitness` (two functions meeting at an `i128` declaration:
`f(i128, i64) -> i64`, whose `block1(v2)` receives only `v1`, a constant phi, and its caller
`g(i128, i64) -> i64`): constant-phi removal changes `f` and keeps `g` (`S0.cpChanged = ["f"]`);
the bundle's program is in `SrcScopeB`, the source program of the compiled input `S0.cp` is not
(`declSigB` fails in `g`), so `attemptT_correct_source` has no instance there. On the typed Stock
route `lean-link` takes first (`Stock.MemorySinkExt.lowerValidated`, the placement of `S0.cp`)
the typed compiler `SemanticCompilerWith.attemptT` succeeds, `hcp` holds by `rfl` (`lean-link`'s
instance: `I0 = S0.input0`), and `attemptT_correct_sourceCp` applies to `g`, a function that
mentions `i128`. Decided by `native_decide` (witness only).
-/

namespace Link.CpSourceTWitness
set_option autoImplicit false
open Backend E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Opt.Legalize128
open Link.CpSourceWitness (S0 gB)

/-- The typed Stock route's lowering (`lean-link`'s `routes[0]!`). -/
def lower : ProductionLowering := Stock.MemorySinkExt.lowerValidated

/-- The route's placement of the compiled (constant-phi-removed) input. -/
def spec : LinkSpec := S0.cp.placedProductionWith lower true

def file0 : ByteArray :=
  match Link.Ld.assemble (ProductionBoundaryWitness.plan spec) with
  | .ok im => im.write
  | .error _ => ByteArray.empty

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true

def checks : Bool :=
  S0.cpChanged == ["f"] && SrcScopeB S0.input0 && !SrcScopeB input.toLinkInput && gB &&
    (SemanticCompilerWith.attemptT lower spec file0).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide -- witness: native_decide

/-- The route's input is the constant-phi removal of the bundle's (`lean-link`'s `hcp`). -/
theorem hcp : spec.funcs = S0.input0.funcs.map FnInput.cp := rfl

/-- **The typed attempt succeeds; the bundle's program is in `SrcScopeB`, the compiled input's
source program is not**, and constant-phi removal changes `f`. -/
theorem parts : (∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file) ∧
    SrcScopeB S0.input0 = true ∧ SrcScopeB input.toLinkInput = false ∧ S0.cpChanged = ["f"] ∧
    ∃ g, S0.input0.srcProg.func? "g" = some g ∧ mentions128 g = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hc, hs⟩, hi⟩, hg⟩, ha⟩ := h
  refine ⟨?_, hs, hi, hc, ?_⟩
  · cases e : SemanticCompilerWith.attemptT lower spec file0 with
    | error m => rw [e] at ha; cases ha
    | ok file => exact ⟨file, rfl⟩
  · unfold gB at hg
    split at hg
    · rename_i g hgf
      exact ⟨g, hgf, hg⟩
    · cases hg

/-- **`attemptT_correct_sourceCp` is not vacuous**: its compiler premises (the typed attempt
succeeds, `SrcScopeB` of the bundle's input, `hcp`) hold on the witness, where
`attemptT_correct_source`'s premise `SrcScopeB` of the compiled input fails, and its conclusion
is the refinement of the executable for the bundle's `g` (an `i128` function), returned values by
class. -/
theorem correct_sourceCp_applies : ∃ file g,
    SemanticCompilerWith.attemptT lower spec file0 = .ok file ∧
    S0.input0.srcProg.func? "g" = some g ∧ mentions128 g = true ∧
    SrcScopeB input.toLinkInput = false ∧
    ∀ (B : BaseEnv), BaseOk (sys input B) → HooksSim input B → Opt.EnvKeepsSymbols B.env →
    ((∃ f ∈ S0.input0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env) →
    ((∃ g ∈ (prog input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none) →
    ∀ {g' : Clif.Function}, (prog input).func? "g" = some g' →
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls input input.results) g' →
    ∀ {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State},
    (imageOf file).Intact r →
    OutsideCall input (BinCheck.roByte input spec.data) g'
      (SemanticStackBound.stackFn input g') r args' cs'.mem →
    ClifRun input B g' r args' cs' →
    ClifEntry g args cs →
    Opt.Legal.ExpRel ((Opt.Legal.groups g.sig.params).getD []) args args' →
    cs'.frame.slots = cs.frame.slots → cs'.mem = cs.mem →
    (∀ s', Opt.Legal.SReach B.env S0.input0.srcProg cs s' → Opt.Legal.MemBounded s'.mem) →
    ∀ (M : Nat), ∀ vals cm, Clif.runLoop B.env S0.input0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups g.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art input g').fb (art input g').base (xreg 30 r) (step input B file) r
          (BinCheck.RelocAtWithResults input input.results) (.returned vals' cm) := by
  obtain ⟨⟨file, hfile⟩, hsrc, hi, -, g, hg, hm⟩ := parts
  refine ⟨file, g, hfile, hg, hm, hi, ?_⟩
  intro B hB hH hkeep hlegal hsig g' hg' hc r args args' cs cs' hX ho hr hcs hexp hsl hmem hbnd M
  exact (SemanticCompilerWith.attemptT_correct_sourceCp hfile hcp hsrc B hB hH hkeep hlegal hsig hg
    hg' hc hX ho hr hcs hexp hsl hmem hbnd M).1

end Link.CpSourceTWitness
