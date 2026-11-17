import FV.Link.ReturnPinExeSourceCp
import FV.Link.ConstPhiSrcScopeWitness
import FV.E2E.ProductionBoundaryWitness

/-! # Non-vacuity of the `…_sourceCp` theorems (#1052)

Two functions meeting at an `i128` declaration (the shape of `Link.ConstPhiSrcScopeWitness`,
#1042): `f(i128, i64) -> i64`, whose `block1(v2)` receives only `v1` (a constant phi), and its
caller `g(i128, i64) -> i64`, which declares `f` with that signature. Constant-phi removal changes
`f` and keeps `g` (`S0.cpChanged = ["f"]`). The bundle's program is in `SrcScopeB`; the source
program of the compiled input `S0.cp` (`f` printed after the `i128` legalisation, `g` as written)
is not (`declSigB` fails in `g`), so `attempt_correct_source` has no instance there. On the
ABI-aware route (`Stock.VoidCall.NI.lowerValidated`, the placement of `S0.cp`) the attempt
succeeds, `hcp` holds by `rfl` (`lean-link`'s instance: `I0 = S0.input0`), and
`attempt_correct_sourceCp` applies to `g`, a function that mentions `i128`. Decided by
`native_decide` (witness only).
-/

namespace Link.CpSourceWitness
set_option autoImplicit false
open Backend E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Opt.Legalize128

/-- The bundle's input: `f` and its caller `g`. -/
def S0 : LinkSpec :=
  { funcs := [{ clif := ConstPhiSrcScopeWitness.fT, ra := "null" },
      { clif := ConstPhiSrcScopeWitness.gT, ra := "null" }],
    names := [], sizes := [], outside := [], symNames := ["f", "g"], R := 0x200160 }

/-- The ABI-aware route's lowering. -/
def lower : ProductionLowering := Stock.VoidCall.NI.lowerValidated

/-- The route's placement of the compiled (constant-phi-removed) input. -/
def spec : LinkSpec := S0.cp.placedProductionWith lower true

def file0 : ByteArray :=
  match Link.Ld.assemble (ProductionBoundaryWitness.plan spec) with
  | .ok im => im.write
  | .error _ => ByteArray.empty

def input : SemanticStackBound.CompilerInput := ReturnPinCompilerWith.input lower spec true

/-- `g` as the bundle wrote it mentions `i128`. -/
def gB : Bool :=
  match S0.input0.srcProg.func? "g" with
  | some g => mentions128 g
  | none => false

def checks : Bool :=
  S0.cpChanged == ["f"] && SrcScopeB S0.input0 && !SrcScopeB S0.cp.input0 &&
    !SrcScopeB input.toLinkInput && gB && (ReturnPinCompilerWith.attempt lower spec file0 true).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide -- witness: native_decide

/-- The route's input is the constant-phi removal of the bundle's (`lean-link`'s `hcp`). -/
theorem hcp : spec.funcs = S0.input0.funcs.map FnInput.cp := rfl

/-- **The attempt succeeds; the bundle's program is in `SrcScopeB`, the compiled input's source
program is not**, and constant-phi removal changes `f`. -/
theorem parts : (∃ file, ReturnPinCompilerWith.attempt lower spec file0 true = .ok file) ∧
    SrcScopeB S0.input0 = true ∧ SrcScopeB input.toLinkInput = false ∧
    SrcScopeB S0.cp.input0 = false ∧ S0.cpChanged = ["f"] ∧
    ∃ g, S0.input0.srcProg.func? "g" = some g ∧ mentions128 g = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hc, hs⟩, hn⟩, hi⟩, hg⟩, ha⟩ := h
  refine ⟨?_, hs, hi, hn, hc, ?_⟩
  · cases e : ReturnPinCompilerWith.attempt lower spec file0 true with
    | error m => rw [e] at ha; cases ha
    | ok file => exact ⟨file, rfl⟩
  · unfold gB at hg
    split at hg
    · rename_i g hgf
      exact ⟨g, hgf, hg⟩
    · cases hg

/-- **`attempt_correct_sourceCp` is not vacuous**: its compiler premises (the attempt succeeds,
`SrcScopeB` of the bundle's input, `hcp`) hold on the witness, where `attempt_correct_source`'s
premise `SrcScopeB` of the compiled input fails, and its conclusion is the refinement of the
executable for the bundle's `g` (an `i128` function). -/
theorem correct_sourceCp_applies : ∃ file g, ReturnPinCompilerWith.attempt lower spec file0 true = .ok file ∧
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
        ExecRefines (art input g').fb (art input g').base (xreg 30 r) (step input B file) r
          (BinCheck.RelocAtWithResults input input.results) (.returned vals' cm) := by
  obtain ⟨⟨file, hfile⟩, hsrc, hi, -, -, g, hg, hm⟩ := parts
  refine ⟨file, g, hfile, hg, hm, hi, ?_⟩
  intro B hB hH hkeep hlegal hsig g' hg' hc r args args' cs cs' hX ho hr hcs hexp hsl hmem hbnd M
  exact (ReturnPinCompilerWith.attempt_correct_sourceCp hfile hcp hsrc B hB hH hkeep hlegal hsig hg
    hg' hc hX ho hr hcs hexp hsl hmem hbnd M).1

end Link.CpSourceWitness
