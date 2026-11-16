import FV.Backend
import FV.Link.SemanticCompileT
import FV.E2E.StockProductionFixtures
import FV.Backend.Lowering.StockArithmeticNI
import FV.Clif.Print
import FVTest.Link.DeadCleanupWitness

/-! Non-vacuity of plain `call`s with float signatures in the typed scope (S11g, #1015, #35).

A program of four functions passing `f32`s and `f64`s by plain `call` (the call form of
cg_clif without unwinding): `%g (f64) -> f64` and `%g32 (f32) -> f32` (an `fadd` each), `%f`
calling both directly (`colocated`: a `bl`) and the `f64` callee `%ext` outside the program
(through its GOT entry: a `blr`), `%h` calling both through their GOT entries (non-`colocated`:
`blr`); next to the Stock route's integer fixture `%stock_arithmetic_ni`. Before S11g, `%f` and
`%h` were outside the typed scope (`Compile.functionETCF`'s `callsE`: every `call`'s callee had an
integer signature; `opsTypedTCF`: a `call`'s arguments were integer positions). Now they are in
it and the backend reports them verified (`unverifiedReason? = none`), the typed checks
`okBTS` (`okRWithTS`: `lowerCheckTCF` per function, the class-aware link checks) hold,
`SemanticCompilerWith.attemptT` succeeds on the Stock route's placement (so `attemptT_correct`
applies), and the code of `%f` (`%h`) has `bl` (`blr`) sites passing and receiving the float
values in v0. Decided by `native_decide` (witness only). `lake build FVTest.Link.FloatPlainCallsT`.
-/

namespace E2E.FloatPlainCallsTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
open E2E.DeadCleanupExecutableWitness (placeholder)

def srcG : String := "function %g(f64) -> f64 {
block0(v0: f64):
    v1 = fadd v0, v0
    return v1
}
"

def srcG32 : String := "function %g32(f32) -> f32 {
block0(v0: f32):
    v1 = fadd v0, v0
    return v1
}
"

def srcF : String := "function %f(f32, f64) -> f64 {
    fn0 = colocated %g32(f32) -> f32
    fn1 = colocated %g(f64) -> f64
    fn2 = %ext(f64) -> f64
block0(v0: f32, v1: f64):
    v2 = call fn0(v0)
    v3 = fpromote.f64 v2
    v4 = call fn1(v1)
    v5 = fadd v3, v4
    v6 = call fn2(v5)
    return v6
}
"

def srcH : String := "function %h(f32, f64) -> f32 {
    fn0 = %g32(f32) -> f32
    fn1 = %g(f64) -> f64
block0(v0: f32, v1: f64):
    v2 = call fn1(v1)
    v3 = fdemote.f32 v2
    v4 = fadd v0, v3
    v5 = call fn0(v4)
    return v5
}
"

def fStock : FnInput :=
  { clif := (StockArithmeticNIWitness.function .defaultI64).print, ra := "null" }

def fG : FnInput := { clif := srcG, ra := "{}" }
def fG32 : FnInput := { clif := srcG32, ra := "{}" }
def fF : FnInput := { clif := srcF, ra := "{}" }
def fH : FnInput := { clif := srcH, ra := "{}" }

def fns : List FnInput := [fStock, fG, fG32, fF, fH]

/-- The Stock route of the fixture. -/
def lower : ProductionLowering := Stock.Arithmetic.lowerValidated

/-- `%ext` is a symbol outside the linked image. -/
def initial : LinkSpec :=
  { funcs := fns, names := [], sizes := [], outside := [("ext", 0x2000000)],
    symNames := ["ext"], R := 0x1000000 }

/-- The Stock route's placement. -/
def spec : LinkSpec := initial.placedProductionWith lower true

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true

/-- `f` has plain `call`s with float signatures: outside subset E and the scope with typed
`try_call`s (`functionETC`, whose `callsE` stays), in the typed scope with float calls
(`functionETCF`, `storeTypedB`), reported verified. -/
def floatCallsB (f : Clif.Function) : Bool :=
  !Compile.functionE f && !Compile.functionETC f && Compile.functionETCF f &&
    Compile.storeTypedB f && (unverifiedReason? f).isNone

/-- The number of plain `call` sites of `name`'s code passing an argument in v0 and receiving a
result in v0, to a callee by symbol (`bl`, `sym = true`) or through a register (`blr`). -/
def floatSites (name : String) (sym : Bool) : Nat :=
  (input.results.filterMap fun row => match row.2 with
    | .error _ => none
    | .ok a => if row.1.name == name then some a else none).foldl (fun n a =>
      n + (a.vcp.blocks.toList.map fun vb => (vb.insts.toList.filter fun i => match i with
        | .call info =>
          (match info.dest with | .sym _ => sym | .reg _ => !sym) &&
            info.uses.any (·.2 == .v 0) && info.defs.any (·.1 == .v 0)
        | _ => false).length).sum) 0

def checks : Bool :=
  input.results.length == 5 && floatCallsB fF.func && floatCallsB fH.func &&
  floatSites "f" true == 2 && floatSites "f" false == 1 && floatSites "h" false == 2 &&
  SemanticStackBound.okBTS input && (SemanticCompilerWith.attemptT lower spec file0).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

/-- **`attemptT` admits program functions passing and returning `f32`s and `f64`s by plain
`call`** (S11g), by `bl` and by `blr` through the GOT, to program functions and to a callee
outside the program. -/
theorem parts : floatCallsB fF.func = true ∧ floatCallsB fH.func = true ∧
    floatSites "f" true = 2 ∧ floatSites "f" false = 1 ∧ floatSites "h" false = 2 ∧
    SemanticStackBound.okBTS input = true ∧
    ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, ha⟩, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩ := h
  refine ⟨ha, hb, hc, hd, he, hf, ?_⟩
  cases e : SemanticCompilerWith.attemptT lower spec file0 with
  | error m => rw [e] at hg; cases hg
  | ok file => exact ⟨file, rfl⟩

def file : ByteArray := getOk (SemanticCompilerWith.attemptT lower spec file0)

theorem attemptT_eq : SemanticCompilerWith.attemptT lower spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact getOk_eq h.2

/-- **Witness**: `Link.SemanticCompilerWith.attemptT_correct` applies to the program. -/
theorem correct_spec :
    type_of% (@SemanticCompilerWith.attemptT_correct lower spec file0 file attemptT_eq) :=
  @SemanticCompilerWith.attemptT_correct lower spec file0 file attemptT_eq

end E2E.FloatPlainCallsTWitness
