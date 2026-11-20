import FV.Link.MidSourceRoutes
import FV.Link.MidPair
import FV.E2E.ProductionBoundaryWitness
import FVTest.Backend.MidValPassWitness

/-! # Non-vacuity of the `…_sourceMid` theorems on an executable (#1119, layer 2)

**Witness file** (`native_decide` allowed; not a compiler theorem). The real pair of
`FVTest/Backend/MidValPassWitness.lean` (sha3 0.12.0's release build, dependency keccak,
`_RNxC6keccak12HbPukoXULhhU`, which calls `_RNxC6keccak12H2JZHOfvwFOl`, outside the program here):
cg_clif's unoptimised function (`srcF`, the bundle's `src_dump`) and Cranelift's optimised one
(`srcG`, the bundle's `dump`; store-to-load forwarding and `nop` removal), which differ. `S0` is
the source input (`I0`), `S1` the compiled one (`I1`), the callee at an outside address.

On the ABI-aware route `lean-link` names (`Stock.VoidCall.NI.lowerValidated`, the placement of
`S1.cp`), `ReturnPinCompilerWith.attempt` writes the executable (`file0`: its placeholder by
`Link.Ld.assemble`), `hcp` holds by `rfl`, `SrcScopeB S1.input0` holds, and `Link.midValidatedB`
holds on the pair (what `lean-link --verified` decides), so `Opt.MidVal.ValidatedC` by
`Link.midValidatedB_sound`: every premise `lean-link` decides for
`ReturnPinCompilerWith.attempt_correct_sourceMid` is discharged, and its conclusion is about a run
of the **unoptimised** program `S0.input0.srcProg` while the executable holds the optimised
function's code. Decided by `native_decide` (witness only).
-/

namespace Link.MidSourceWitness
set_option autoImplicit false
open Backend E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Opt.Legalize128
open FVTest.Backend.MidValPassWitness (srcF srcG fSrc gOpt)

/-- The function's name. -/
def name : String := "_RNxC6keccak12HbPukoXULhhU"

/-- The bundle's source input `I0`: cg_clif's unoptimised function; its callee outside. -/
def S0 : LinkSpec :=
  { funcs := [{ clif := srcF, ra := "null" }], names := [], sizes := [],
    outside := [("_RNxC6keccak12H2JZHOfvwFOl", 0x100000)], symNames := [], R := 0x200160 }

/-- The compiled input `I1`: Cranelift's optimised function. -/
def S1 : LinkSpec := { S0 with funcs := [{ clif := srcG, ra := "null" }] }

/-- The ABI-aware route's lowering. -/
def lower : ProductionLowering := Stock.VoidCall.NI.lowerValidated

/-- The route's placement of the compiled (constant-phi-removed) input. -/
def spec : LinkSpec := S1.cp.placedProductionWith lower true

def file0 : ByteArray :=
  match Link.Ld.assemble (ProductionBoundaryWitness.plan spec) with
  | .ok im => im.write
  | .error _ => ByteArray.empty

def input : SemanticStackBound.CompilerInput := ReturnPinCompilerWith.input lower spec true

def checks : Bool :=
  Link.midValidatedB S0.input0.srcProg.funcs S1.input0.srcProg.funcs && SrcScopeB S1.input0 &&
    decide (S0.input0.srcProg.func? name = some fSrc) &&
    decide (S1.input0.srcProg.func? name = some gOpt) && !decide (fSrc = gOpt) &&
    (ReturnPinCompilerWith.attempt lower spec file0 true).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide -- witness: native_decide

/-- The route's input is the constant-phi removal of the compiled bundle's (`lean-link`'s `hcp`). -/
theorem hcp : spec.funcs = S1.input0.funcs.map FnInput.cp := rfl

/-- **The attempt succeeds, the compiled program is in `SrcScopeB`, the pair is validated**, and
the source and compiled functions differ. -/
theorem parts : (∃ file, ReturnPinCompilerWith.attempt lower spec file0 true = .ok file) ∧
    SrcScopeB S1.input0 = true ∧
    Opt.MidVal.ValidatedC S0.input0.srcProg.funcs S1.input0.srcProg.funcs ∧
    S0.input0.srcProg.func? name = some fSrc ∧ S1.input0.srcProg.func? name = some gOpt ∧
    fSrc ≠ gOpt := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨hv, hs⟩, hf⟩, hg⟩, hne⟩, ha⟩ := h
  refine ⟨?_, hs, Link.midValidatedB_sound hv, hf, hg, hne⟩
  cases e : ReturnPinCompilerWith.attempt lower spec file0 true with
  | error m => rw [e] at ha; cases ha
  | ok file => exact ⟨file, rfl⟩

/-- **`ReturnPinCompilerWith.attempt_correct_sourceMid` is not vacuous**: its compiler premises
(the attempt succeeds, `SrcScopeB` of the compiled bundle's input, `hcp`, `ValidatedC` of the
pair) hold on the witness, where the executable holds the optimised function's code and the
conclusion is the refinement of the executable for a return of the unoptimised function's run. -/
theorem correct_sourceMid_applies : ∃ file, ReturnPinCompilerWith.attempt lower spec file0 true = .ok file ∧
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
  exact (ReturnPinCompilerWith.attempt_correct_sourceMid hfile hcp hsrc hv B hB hH hkeep hlegal hsig
    hf hg hf' hc hX ho hr hcs hexp hsl hmem hbnd M).1

end Link.MidSourceWitness
