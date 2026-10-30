import FV.Link.DeadCleanupCompileT
import FVTest.Link.DeadCleanupWitness

/-! Non-vacuity of `Link.DeadCleanup.compileExeT`'s typed-`try_call` branch (S11e6, #419): on a
program whose single function has a direct `try_call` of an `f64`-taking/`f64`-returning extern
(outside `InScopeP` and `InScopePT`), `compileExeT` succeeds through its third branch: the
widened dead-cleanup checker `okBCleanupT` (via `okBCleanupTFast`) accepts the compiled code and
the Lean linker succeeds, so `compileExeT_correct` applies. Decided by `native_decide` (witness
only). `lake build FVTest.Link.FloatTryCompileExeT`. -/

namespace E2E.FloatTryCompileExeTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend
open E2E.DeadCleanupExecutableWitness (placeholder)

def srcTry : String := "function %t(f64, i64) -> f64 {
    sig0 = (f64, i64) -> f64
    fn0 = %g(f64, i64) -> f64
block0(v0: f64, v1: i64):
    try_call fn0(v0, v1), sig0, block1(ret0), [ default: block2(exn0) ]
block1(v2: f64):
    return v2
block2(v3: i64):
    return v0
}
"

def fTry : FnInput := { clif := srcTry, ra := "{}" }

def fns : List FnInput := [fTry]

/-- The dead-cleanup pipeline's link of the `try_call` program; the callee `%g` is an external
symbol outside the linked image. -/
def spec : LinkSpec :=
  { funcs := fns, names := fns.map (·.func.name),
    sizes := fns.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [("g", 0x2000000)], symNames := ["g"], R := 0x1000000 }

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

/-- `%t` has a direct `try_call` of a callee with `f64` parameters and return: outside subset E
and the typed movement scope, in the scope with typed `try_call`s. -/
def tryFloatsB : Bool :=
  !Compile.functionE fTry.func && !Compile.functionET fTry.func &&
  Compile.functionETC fTry.func

def checks : Bool :=
  tryFloatsB && !InScopeP spec.input0 && !InScopePT spec.input0 &&
  okBCleanupTFast spec.inputCleanup &&
  (Link.DeadCleanup.leanLink spec file0).toBool &&
  (Link.DeadCleanup.compileExeT spec file0).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

theorem parts : tryFloatsB = true ∧ InScopeP spec.input0 = false ∧
    InScopePT spec.input0 = false ∧ okBCleanupTFast spec.inputCleanup = true ∧
    (Link.DeadCleanup.leanLink spec file0).toBool = true ∧
    (Link.DeadCleanup.compileExeT spec file0).toBool = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **Witness**: the checker accepts the `try_call` program (the widened `okBCleanupT`). -/
theorem okBCleanupT_spec : okBCleanupT spec.inputCleanup = true :=
  okBCleanupTFast_eq spec.inputCleanup ▸ parts.2.2.2.1

def file : ByteArray := getOk (Link.DeadCleanup.compileExeT spec file0)

theorem compile_eq : Link.DeadCleanup.compileExeT spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact getOk_eq h.2

/-- **Witness**: `Link.DeadCleanup.compileExeT_correct` applies to the `try_call` program
(through the third branch). -/
theorem correct_spec :
    type_of% (@Link.DeadCleanup.compileExeT_correct spec file0 file compile_eq) :=
  @Link.DeadCleanup.compileExeT_correct spec file0 file compile_eq

end E2E.FloatTryCompileExeTWitness
