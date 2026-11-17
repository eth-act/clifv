import FV.Link.SemanticExeSourceTB
import FV.E2E.StockProductionFixtures
import FV.Backend.Lowering.StockArithmeticNI
import FV.Clif.Print
import FVTest.Link.DeadCleanupWitness

/-! Non-vacuity of `attemptT_correct_source{,_peak}TB` (#1076).

A program of two functions: `%stock_arithmetic_ni` (integer, the Stock route's fixture) and
`%dc`, the shape of Rust's `Box<dyn Any>::downcast` (cg_clif's CLIF of
`alloc::boxed::Box<dyn Any + Send>::downcast::<String>` in crypto-bigint's tests): the vtable's
`type_id` called through a `try_call_indirect` with an `i128`-free signature (`(i64 sret, i64)`)
writing a `TypeId` into a stack slot, a `tag0` handler, then two `TypeId`s loaded with
`load.i128` and compared. `%dc` is outside the old source domain (`legalOkB`: no
`try_call_indirect` in an `i128` function) and inside the new one (`legalOkTB`); the input is in
`SrcScopeTB` and not in `SrcScopeB`. On the Stock route's placement the typed compiler
`SemanticCompilerWith.attemptT` succeeds, so `attemptT_correct_sourceTB` applies to `%dc` in the
written executable (`correct_source_applies`; the function-level run that raises into the
handler: `Clif.Rust.LegalXTWitness`, `FV/E2E/LegalUnwindTWitness.lean`). Decided by
`native_decide` (witness only). `lake build FVTest.Link.I128TryIndT`. -/

namespace E2E.I128TryIndTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
open E2E.DeadCleanupExecutableWitness (placeholder)
open Opt.Legalize128

def srcDc : String := "function %dc(i64 sret, i64, i64, i64) system_v {
    ss0 = explicit_slot 16, align = 8
    sig0 = (i64 sret, i64) system_v
block0(v0: i64, v1: i64, v2: i64, v3: i64):
    v4 = stack_addr.i64 ss0
    try_call_indirect v1(v4, v3), sig0, block1, [ tag0: block2(exn0) ]
block1:
    v5 = load.i128 notrap aligned v4
    v6 = load.i128 notrap aligned v2
    v7 = icmp eq v5, v6
    v8 = uextend.i64 v7
    store notrap v8, v0
    return
block2(v9: i64):
    v10 = iconst.i64 0
    store notrap v10, v0
    return
}
"

def fStock : FnInput :=
  { clif := (StockArithmeticNIWitness.function .defaultI64).print, ra := "null" }

def fDc : FnInput := { clif := srcDc, ra := "{}" }

def fns : List FnInput := [fStock, fDc]

/-- The Stock route of the fixture. -/
def lower : ProductionLowering := Stock.Arithmetic.lowerValidated

def initial : LinkSpec :=
  { funcs := fns, names := [], sizes := [], outside := [], symNames := [], R := 0x1000000 }

/-- The Stock route's placement. -/
def spec : LinkSpec := initial.placedProductionWith lower true

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true

/-- `%dc` as parsed: it mentions `i128`, has a `try_call_indirect` terminator and a `load.i128`,
is outside `legalOkB` and inside `legalOkTB`. -/
def dcB : Bool :=
  match input.toLinkInput.srcProg.func? "dc" with
  | some f =>
    mentions128 f && !legalOkB f && legalOkTB f &&
      f.blocks.any (fun b => match b.term with | .tryCallIndirect .. => true | _ => false) &&
      f.blocks.any (fun b => b.body.any fun s => match s.inst with
        | .load _ .i128 _ _ _ => true
        | _ => false)
  | none => false

def checks : Bool :=
  dcB && (SemanticCompilerWith.attemptT lower spec file0).toBool &&
  SrcScopeTB input.toLinkInput && !SrcScopeB input.toLinkInput

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide -- witness: native_decide

/-- **`attemptT` succeeds; the input is in `SrcScopeTB` and not in `SrcScopeB`.** -/
theorem parts : (∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file) ∧
    SrcScopeTB input.toLinkInput = true ∧ SrcScopeB input.toLinkInput = false ∧
    ∃ f, input.toLinkInput.srcProg.func? "dc" = some f ∧ mentions128 f = true ∧
      legalOkB f = false ∧ ∃ B ∈ f.blocks, ∃ c args et, B.term = .tryCallIndirect c args et := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hd, ha⟩, hs⟩, hn⟩ := h
  refine ⟨?_, hs, hn, ?_⟩
  · cases e : SemanticCompilerWith.attemptT lower spec file0 with
    | error m => rw [e] at ha; cases ha
    | ok file => exact ⟨file, rfl⟩
  · unfold dcB at hd
    split at hd
    · rename_i f hf
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at hd
      obtain ⟨⟨⟨⟨hm, hb⟩, -⟩, B, hB, ht⟩, -⟩ := hd
      refine ⟨f, hf, hm, hb, B, hB, ?_⟩
      cases hbt : B.term
      all_goals first | exact ⟨_, _, _, rfl⟩ | simp [hbt] at ht
    · cases hd

/-- **`attemptT_correct_sourceTB` is not vacuous**: its compiler premises (`attemptT` succeeds,
`SrcScopeTB`) hold on the witness, whose function `%dc` (an `i128` function with a
`try_call_indirect`) is outside `SrcScopeB`, and its conclusion is the typed refinement of the
executable for `%dc`'s source run. -/
theorem correct_source_applies : ∃ file f, SemanticCompilerWith.attemptT lower spec file0 = .ok file ∧
    input.toLinkInput.srcProg.func? "dc" = some f ∧ legalOkB f = false ∧
    ∀ (B : BaseEnv), BaseOk (SemanticBinary.sys input B) → SemanticExecBytes.HooksSim input B →
    ((∃ f ∈ input.toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env) →
    ((∃ g ∈ (SemanticBinary.prog input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none) →
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls input input.results) (legalize f) →
    ∀ {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State},
    (SemanticBinary.imageOf file).Intact r →
    SemanticBinary.OutsideCall input (BinCheck.roByte input spec.data) (legalize f)
      (SemanticStackBound.stackFn input (legalize f)) r args' cs'.mem →
    SemanticBinary.ClifRun input B (legalize f) r args' cs' →
    ClifEntry f args cs →
    Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args' →
    cs'.frame.slots = cs.frame.slots → cs'.mem = cs.mem →
    (∀ s', Opt.Legal.SReach B.env input.toLinkInput.srcProg cs s' → Opt.Legal.MemBounded s'.mem) →
    ∀ (M : Nat), ∀ vals cm, Clif.runLoop B.env input.toLinkInput.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (SemanticBinary.art input (legalize f)).fb
          (SemanticBinary.art input (legalize f)).base (xreg 30 r)
          (SemanticExecBytes.step input B file) r
          (BinCheck.RelocAtWithResults input input.results) (.returned vals' cm) := by
  obtain ⟨⟨file, hfile⟩, hsrc, -, f, hf, -, hb, -⟩ := parts
  refine ⟨file, f, hfile, hf, hb, ?_⟩
  intro B hB hH hlegal hsig hc r args args' cs cs' hX ho hr hcs hexp hsl hmem hbnd M
  exact (SemanticCompilerWith.attemptT_correct_sourceTB hfile hsrc B hB hH hlegal hsig hf hc
    hX ho hr hcs hexp hsl hmem hbnd M).1

end E2E.I128TryIndTWitness
