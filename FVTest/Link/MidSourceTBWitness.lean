import FV.Link.MidSourceTB
import FV.Link.MidPair
import FVTest.Link.I128TryIndT

/-! # Non-vacuity of `attemptT_correct_source{,_peak}TBMid` (#1119, layer 2)

**Witness file** (`native_decide` allowed; not a compiler theorem). The executable of
`FVTest/Link/I128TryIndT.lean` (`%stock_arithmetic_ni` and `%dc`, in `SrcScopeTB` and not in
`SrcScopeB`; `SemanticCompilerWith.attemptT` writes it), whose route input's source program is
`Q`. `P0` is `Q` with the Stock function `g` replaced by `f`, the same function with a `nop` in
its entry block (the unoptimised form; Cranelift's mid-end removes `nop`s, as in the keccak pair of
`FVTest/Backend/MidValPassWitness.lean`). `Link.midValidatedB P0.funcs Q.funcs` holds, so
`Opt.MidVal.Validated` by `Link.midValidatedB_sound`, `f ≠ g`, and every premise `lean-link
--verified` decides for `attemptT_correct_sourceTBMid` is discharged: its conclusion is about a
run of `P0` from `f`'s entry while the executable holds `g`'s code. Decided by `native_decide`
(witness only).
-/

namespace E2E.MidSourceTBWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Opt.Legalize128
open E2E.I128TryIndTWitness (fStock lower spec file0 input)

/-- The Stock function's name. -/
def name : String := fStock.src.name

/-- The Stock function's text with a `nop` after its entry block's header. -/
def srcNop : String :=
  let ls := fStock.clif.splitOn "\n"
  match ls.findIdx? (·.startsWith "block0") with
  | some i => "\n".intercalate (ls.take (i + 1) ++ ["    nop"] ++ ls.drop (i + 1))
  | none => fStock.clif

/-- `f`: the unoptimised form. -/
def fNop : Clif.Function := ({ clif := srcNop, ra := "null" } : FnInput).src

/-- `Q`: the route input's source program. -/
def Q : Clif.Program := input.toLinkInput.srcProg

/-- `P0`: `Q` with the Stock function in its unoptimised form. -/
def P0 : Clif.Program := { funcs := Q.funcs.map fun g => if g.name = name then fNop else g }

/-- `g`: the Stock function as the route input holds it. -/
def gS : Clif.Function := (Q.func? name).getD default

def checks : Bool :=
  Link.midValidatedB P0.funcs Q.funcs && decide (P0.func? name = some fNop) &&
    decide (Q.func? name = some gS) && !decide (fNop = gS)

theorem checks_true : checks = true := by native_decide -- witness: native_decide

/-- **The pair is validated**, the functions differ, and the programs look them up by `name`. -/
theorem parts : Opt.MidVal.Validated P0.funcs input.toLinkInput.srcProg.funcs ∧
    P0.func? name = some fNop ∧ input.toLinkInput.srcProg.func? name = some gS ∧ fNop ≠ gS := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨hv, hf⟩, hg⟩, hne⟩ := h
  exact ⟨Link.midValidatedB_sound hv, hf, hg, hne⟩

/-- **`attemptT_correct_sourceTBMid` is not vacuous**: its compiler premises (`attemptT`
succeeds, `SrcScopeTB` of the route's input, `Validated` of `P0` against it) hold on the witness,
and its conclusion is the typed refinement of the executable, which holds `g`'s code, for a
return of `P0`'s run from `f`'s entry. -/
theorem correct_sourceTBMid_applies : ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file ∧
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
  exact (SemanticCompilerWith.attemptT_correct_sourceTBMid hfile hsrc hv B hB hH hkeep hlegal hsig
    hf hg hc hX ho hr hcs hexp hsl hmem hbnd M).1

end E2E.MidSourceTBWitness
