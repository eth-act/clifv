import FV.Link.SemanticCompileT
import FV.E2E.StockProductionFixtures
import FV.Backend.Lowering.StockArithmeticNI
import FV.Clif.Print
import FVTest.Link.DeadCleanupWitness

/-! Non-vacuity of the typed link layer's `sret` case outside subset E (#722, `LinkSys.OkT.sretE`'s
right disjunct `RetsX`).

A program of two functions: `%stock_arithmetic_ni` (integer, the Stock route's fixture, as in
`FVTest/Link/FloatStockCompileT.lean`) and `%fs` (an `sret` function storing its `f64`
parameter through the struct pointer, as cg_clif writes a float field of a returned struct:
outside subset E, so the integer `sretE` case does not apply). `lowerFunction` appends the struct
pointer to `%fs`'s return, in x8 (#587), so its code meets `RetsX 0` (`retsXB`); the typed checks `okBTS`
hold and `SemanticCompilerWith.attemptT` succeeds on the Stock route's placement. Decided by
`native_decide` (witness only). `lake build FVTest.Link.FloatStockSretT`. -/

namespace E2E.FloatStockSretTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
open E2E.DeadCleanupExecutableWitness (placeholder)

def srcSret : String := "function %fs(i64 sret, f64) {
block0(v0: i64, v1: f64):
    store.f64 notrap v1, v0
    return
}
"

def fStock : FnInput :=
  { clif := (StockArithmeticNIWitness.function .defaultI64).print, ra := "null" }

def fSret : FnInput := { clif := srcSret, ra := "{}" }

def fns : List FnInput := [fStock, fSret]

/-- The Stock route of the fixture. -/
def lower : ProductionLowering := Stock.Arithmetic.lowerValidated

def initial : LinkSpec :=
  { funcs := fns, names := [], sizes := [], outside := [], symNames := [], R := 0x1000000 }

/-- The Stock route's placement. -/
def spec : LinkSpec := initial.placedProductionWith lower true

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true

/-- The `sret` function: outside subset E, with an `sret` parameter, `lowerFunction`'s code,
which `lowerCheckT` accepts and whose returns are in their `retX` registers (`retsXB`). -/
def sretB : Bool :=
  input.results.any fun row => match row.2 with
    | .error _ => false
    | .ok a =>
      row.1.name == fSret.func.name && !Compile.functionE row.1 &&
        row.1.sig.params.any (·.purpose == .sret) && lowersToB row.1 a.vc &&
        lowerCheckT row.1 a.vc && allInsts a.vc (retsXB row.1.sig.returns.length)

def checks : Bool :=
  input.results.length == 2 && sretB && SemanticStackBound.okBTS input &&
  (SemanticCompilerWith.attemptT lower spec file0).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

/-- **`attemptT` admits an `sret` function outside subset E** (the `RetsX` case of
`LinkSys.OkT.sretE`), next to a Stock-lowered integer function. -/
theorem parts : sretB = true ∧ SemanticStackBound.okBTS input = true ∧
    ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, ha⟩, hb⟩, hc⟩ := h
  refine ⟨ha, hb, ?_⟩
  cases e : SemanticCompilerWith.attemptT lower spec file0 with
  | error m => rw [e] at hc; cases hc
  | ok file => exact ⟨file, rfl⟩

end E2E.FloatStockSretTWitness
