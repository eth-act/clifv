import FV.Link.SemanticCompileT
import FV.E2E.StockProductionFixtures
import FV.Backend.Lowering.StockArithmeticNI
import FV.Clif.Print
import FVTest.Link.DeadCleanupWitness

/-! Non-vacuity of the class-aware program call sites of the typed link layer (#742,
`LinkSys.OkT.callRegs`/`blrRegs` with `sigRetRegs`, `LinkSys.progXT`).

A program of three functions passing `f64`s to each other: `%g (f64) -> f64` (an `fadd`), `%f`
calling `%g` directly (`colocated`: a `bl`, `ProgSite`) and `%h` calling `%g` through its GOT
entry (non-`colocated`: a `blr`, `BlrTo`), both by `try_call` (as cg_clif calls with unwinding,
the typed scope's call form) passing their `f64` parameter in v0 and reading `%g`'s `f64`
result from v0; next to the Stock route's integer fixture `%stock_arithmetic_ni`. Before #742
the typed checks rejected `%f` and `%h` ("calleeInt": `%g` returns an `f64`; "callRegs/blrRegs":
the call's vregs are of class `.float` and its result is not in x0). Now the class-aware checks
`okBTS` (`okRWithTS`) hold, `SemanticCompilerWith.attemptT` succeeds on the Stock route's
placement, and the code of `%f` (`%h`) has a `bl` (`blr`) site passing and receiving in v0.
Decided by `native_decide` (witness only). `lake build FVTest.Link.FloatLinkCallsT`. -/

namespace E2E.FloatLinkCallsTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
open E2E.DeadCleanupExecutableWitness (placeholder)

def srcG : String := "function %g(f64) -> f64 {
block0(v0: f64):
    v1 = fadd v0, v0
    return v1
}
"

def srcF : String := "function %f(f64) -> f64 {
    sig0 = (f64) -> f64
    fn0 = colocated %g(f64) -> f64
block0(v0: f64):
    try_call fn0(v0), sig0, block1(ret0), [ default: block2(exn0) ]
block1(v1: f64):
    return v1
block2(v2: i64):
    return v0
}
"

def srcH : String := "function %h(f64) -> f64 {
    sig0 = (f64) -> f64
    fn0 = %g(f64) -> f64
block0(v0: f64):
    try_call fn0(v0), sig0, block1(ret0), [ default: block2(exn0) ]
block1(v1: f64):
    return v1
block2(v2: i64):
    return v0
}
"

def fStock : FnInput :=
  { clif := (StockArithmeticNIWitness.function .defaultI64).print, ra := "null" }

def fG : FnInput := { clif := srcG, ra := "{}" }
def fF : FnInput := { clif := srcF, ra := "{}" }
def fH : FnInput := { clif := srcH, ra := "{}" }

def fns : List FnInput := [fStock, fG, fF, fH]

/-- The Stock route of the fixture. -/
def lower : ProductionLowering := Stock.Arithmetic.lowerValidated

def initial : LinkSpec :=
  { funcs := fns, names := [], sizes := [], outside := [], symNames := [], R := 0x1000000 }

/-- The Stock route's placement. -/
def spec : LinkSpec := initial.placedProductionWith lower true

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true

/-- A `try_call` site of `name`'s code passing an argument in v0 and receiving a result in v0,
to a callee by symbol (`bl`, `sym = true`) or through a register (`blr`). -/
def floatSiteB (name : String) (sym : Bool) : Bool :=
  input.results.any fun row => match row.2 with
    | .error _ => false
    | .ok a =>
      row.1.name == name && a.vcp.blocks.any fun vb => vb.insts.any fun i => match i with
        | .tryCall info _ =>
          (match info.dest with | .sym _ => sym | .reg _ => !sym) &&
            info.uses.any (·.2 == .v 0) && info.defs.any (·.1 == .v 0)
        | _ => false

def checks : Bool :=
  input.results.length == 4 && floatSiteB "f" true && floatSiteB "h" false &&
  SemanticStackBound.okBTS input && (SemanticCompilerWith.attemptT lower spec file0).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

/-- **`attemptT` admits program calls passing and returning `f64`s** (#742: the class-aware
`LinkSys.OkT.callRegs`/`blrRegs`), by `bl` and by `blr` through the GOT. -/
theorem parts : floatSiteB "f" true = true ∧ floatSiteB "h" false = true ∧
    SemanticStackBound.okBTS input = true ∧
    ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, ha⟩, hb⟩, hc⟩, hd⟩ := h
  refine ⟨ha, hb, hc, ?_⟩
  cases e : SemanticCompilerWith.attemptT lower spec file0 with
  | error m => rw [e] at hd; cases hd
  | ok file => exact ⟨file, rfl⟩

end E2E.FloatLinkCallsTWitness
