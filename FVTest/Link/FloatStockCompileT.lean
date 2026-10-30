import FV.Link.SemanticCompileT
import FV.E2E.SrcScopeDefs
import FV.E2E.StockProductionFixtures
import FV.Backend.Lowering.StockArithmeticNI
import FV.Clif.Print
import FVTest.Link.DeadCleanupWitness

/-! Non-vacuity of the typed compiler on a Stock route (#722).

A program of two functions: `%stock_arithmetic_ni` (integer, the Stock route's fixture: its
Stock code is not `lowerFunction`'s and the legacy validator rejects it, `SemanticNI.check`
accepts it) and `%fa` (float arithmetic and an `fcmp`, outside subset E: the Stock lowering
rejects it, so the route takes `lowerFunction`'s code, which `lowerCheckTCF` accepts). On the
Stock route's placement (`placedProductionWith`, the region `lean-backend`'s units reserve), the
integer Stock compiler `SemanticCompilerWith.attempt` fails (the float function is outside its
scope), while `SemanticCompilerWith.attemptT` succeeds: its typed checks `okBTS` hold, so
`attemptT_correct` and its variants apply to an executable whose integer function is Stock code
and whose float function is verified in the same region. Decided by `native_decide` (witness
only). `lake build FVTest.Link.FloatStockCompileT`. -/

namespace E2E.FloatStockCompileTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
open E2E.DeadCleanupExecutableWitness (placeholder)

def srcArith : String := "function %fa(f64, f64) -> f64, i32 {
block0(v0: f64, v1: f64):
    v2 = fadd v0, v1
    v3 = fmul v2, v0
    v4 = fcmp lt v3, v1
    v5 = uextend.i32 v4
    return v3, v5
}
"

def fStock : FnInput :=
  { clif := (StockArithmeticNIWitness.function .defaultI64).print, ra := "null" }

def fFloat : FnInput := { clif := srcArith, ra := "{}" }

def fns : List FnInput := [fStock, fFloat]

/-- The Stock route of the fixture. -/
def lower : ProductionLowering := Stock.Arithmetic.lowerValidated

def initial : LinkSpec :=
  { funcs := fns, names := [], sizes := [], outside := [], symNames := [], R := 0x1000000 }

/-- The Stock route's placement. -/
def spec : LinkSpec := initial.placedProductionWith lower true

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true

/-- Per function: the integer function's artifact is Stock code (not `lowerFunction`'s,
rejected by the legacy validator, accepted by `SemanticNI.check`); the float function's is
`lowerFunction`'s, outside subset E, accepted by `lowerCheckTCF`. -/
def artsB : Bool :=
  input.results.length == 2 &&
  input.results.all fun row => match row.2 with
    | .error _ => false
    | .ok a =>
      if row.1.name == fFloat.func.name then
        !Compile.functionE row.1 && lowersToB row.1 a.vc && Compile.functionETCF row.1 &&
          lowerCheckTCF row.1 a.vc
      else
        Compile.functionE row.1 && !lowerCheck row.1 a.vc && SemanticNI.check row.1 a.vc &&
          !lowersToB row.1 a.vc

def checks : Bool :=
  artsB && SemanticStackBound.okBTS input &&
  !(SemanticCompilerWith.attempt lower spec file0 true).toBool &&
  (SemanticCompilerWith.attemptT lower spec file0).toBool &&
  SrcScopeB input.toLinkInput

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

/-- **`attemptT` succeeds where the integer Stock compiler fails**, with the typed checks, on a
program whose integer function is Stock code and whose float function is `lowerFunction`'s. -/
theorem parts : artsB = true ∧ SemanticStackBound.okBTS input = true ∧
    (SemanticCompilerWith.attempt lower spec file0 true).toBool = false ∧
    ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, -⟩ := h
  refine ⟨ha, hb, hc, ?_⟩
  cases e : SemanticCompilerWith.attemptT lower spec file0 with
  | error m => rw [e] at hd; cases hd
  | ok file => exact ⟨file, rfl⟩

/-- **`attemptT_correct` is not vacuous**: its compiler premise holds on the witness, and its
conclusion is the typed refinement of the executable (`ExecRefinesT`). -/
theorem correct_applies : ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file ∧
    ∀ (B : BaseEnv), BaseOk (SemanticBinary.sys input B) → SemanticExecBytes.HooksSim input B →
    ∀ {n : String} {f : Clif.Function}, (SemanticBinary.prog input).func? n = some f →
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls input input.results) f →
    ∀ (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
    (SemanticBinary.imageOf file).Intact r →
    SemanticBinary.OutsideCall input (BinCheck.roByte input spec.data) f
      (SemanticStackBound.stackFn input f) r args cs.mem →
    SemanticBinary.ClifRun input B f r args cs →
    TrapsExplicit (Clif.linkEnvN (SemanticBinary.prog input) B.env M)
      (SemanticBinary.prog input).bare cs →
    ExecBytes.ExecRefinesT (SemanticBinary.art input f).fb (SemanticBinary.art input f).base
      (xreg 30 r) (SemanticExecBytes.step input B file) r
      (BinCheck.RelocAtWithResults input input.results)
      (Clif.runLoop B.env (SemanticBinary.prog input) (M + 1) cs) := by
  obtain ⟨-, -, -, file, hf⟩ := parts
  exact ⟨file, hf, fun B hB hH _ _ hfn hc M _ _ _ hX ho hr htr =>
    SemanticCompilerWith.attemptT_correct hf B hB hH hfn hc M hX ho hr htr⟩

/-- **The premises of `attemptT_correct_source{,_peak}` on the compiler side hold**: `attemptT`
succeeds and the input is in the source domain `SrcScopeB`. -/
theorem source_applies : (∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file) ∧
    SrcScopeB input.toLinkInput = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact ⟨(parts).2.2.2, h.2⟩

end E2E.FloatStockCompileTWitness
