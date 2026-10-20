import FV.Link.ExeT
import FV.Link.DeadCleanupExeT
import FVTest.Link.DeadCleanupWitness

/-! Non-vacuity of the typed executable theorems (S11e5 Stage C, slice 8).

A linked program of two float-moving functions: `%w` (integer signature, float loads, constant,
`select`, store and `bitcast` inside) and `%mv` (float parameters and a float return, float block
parameters). Decided by `native_decide` (witness only): the typed input conditions `InScopePT`,
the output checks `OutOkT` and the Lean linker's success, for the legacy pipeline (`spec`) and
the shipped dead-cleanup pipeline (`specC`); so `Link.compileExe_correctT`,
`Link.DeadCleanup.compileExe_correctT` and their depth/peak forms apply (`correctT_*`). The
integer corollary `Link.compileExe_correct_viaT` is instantiated on the existing integer witness
`DeadCleanupExecutableWitness.baselineSpec` (`viaT_baseline`). `lake build FVTest.Link.FloatExeT`. -/

namespace E2E.FloatExeTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend E2E.DeadCleanupExecutableWitness

def fW : FnInput :=
  { clif := "function %w(i64, i8) -> i64 {
block0(v0: i64, v1: i8):
    v2 = load.f64 v0
    v3 = f64const 0x1.0p-2
    v4 = select v1, v2, v3
    store v4, v0+8
    v5 = bitcast.i64 v4
    return v5
}
", ra := "{}" }

def fMv : FnInput :=
  { clif := "function %mv(f64, i64, f32, i8) -> f64 {
block0(v0: f64, v1: i64, v2: f32, v3: i8):
    v4 = load.f64 v1
    store v2, v1+8
    v5 = f32const 0x1.0p0
    store v5, v1+12
    v6 = select v3, v0, v4
    v7 = bitcast.i64 v6
    v8 = bitcast.f64 v7
    v9 = f64const 0x1.0p-2
    brif v3, block1(v8), block1(v9)
block1(v10: f64):
    jump block2(v10)
block2(v11: f64):
    return v11
}
", ra := "{}", k := 1 }

def fns : List FnInput := [fW, fMv]

/-- The legacy pipeline's link. -/
def spec : LinkSpec :=
  { funcs := fns, names := fns.map (·.func.name),
    sizes := fns.map fun fi => (getOk (pipeT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := [], R := 0x1000000 }

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

/-- The dead-cleanup pipeline's link. -/
def specC : LinkSpec :=
  { spec with sizes := fns.map fun fi =>
      (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size }

def file0C : ByteArray :=
  placeholder specC.R specC.size (specC.addrs.map fun p => (BinCheck.symName p.1, p.2))

/-- `%mv` has float parameters and a float return; `%w` moves floats inside. -/
def floatsB : Bool :=
  (fMv.func.sig.params.any (·.ty.isFloat)) && (fMv.func.sig.returns.any (·.ty.isFloat)) &&
  !Compile.functionE fW.func && !Compile.functionE fMv.func

def checks : Bool :=
  floatsB && InScopePT spec.input && OutOkT spec.input && (leanLink spec file0).toBool &&
  InScopePT specC.inputCleanup && OutOkTCleanup specC.inputCleanup && (leanLink specC file0C).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

theorem parts : floatsB = true ∧ InScopePT spec.input = true ∧ OutOkT spec.input = true ∧
    (leanLink spec file0).toBool = true ∧ InScopePT specC.inputCleanup = true ∧
    OutOkTCleanup specC.inputCleanup = true ∧ (leanLink specC file0C).toBool = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

def file : ByteArray := getOk (leanLink spec file0)
def fileC : ByteArray := getOk (leanLink specC file0C)

/-- **Witness**: `InScopePT` of a program with float parameters, returns and data movement. -/
theorem inScopePT_spec : InScopePT spec.input = true := parts.2.1

/-- **Witness**: the output checks hold on the compiler's results. -/
theorem outOkT_spec : OutOkT spec.input = true := parts.2.2.1

theorem link_eq : leanLink spec file0 = .ok file := getOk_eq parts.2.2.2.1

theorem link_eqC : leanLink specC file0C = .ok fileC := getOk_eq parts.2.2.2.2.2.2

/-- **Witness**: `Link.compileExe_correctT` applies to the float program (every premise but the
outside code's contracts and the run is discharged). -/
theorem correctT_spec := @compileExe_correctT spec file0 file inScopePT_spec outOkT_spec link_eq

theorem correct_depthT_spec :=
  @compileExe_correct_depthT spec file0 file inScopePT_spec outOkT_spec link_eq

theorem correct_peakT_spec :=
  @compileExe_correct_peakT spec file0 file inScopePT_spec outOkT_spec link_eq

/-- **Witness**: `Link.DeadCleanup.compileExe_correctT` applies to the float program. -/
theorem correctT_specC :=
  @Link.DeadCleanup.compileExe_correctT specC file0C fileC parts.2.2.2.2.1 parts.2.2.2.2.2.1 link_eqC

/-! ## The integer corollary on the existing integer witness -/

def fileB : ByteArray := getOk (Link.compileExe baselineSpec baselineFile0)

theorem compile_eqB : Link.compileExe baselineSpec baselineFile0 = .ok fileB := by
  have h := checks_true
  simp only [DeadCleanupExecutableWitness.checks, Bool.and_eq_true] at h
  exact getOk_eq h.1.1

/-- **Witness**: the typed premises of the integer witness, from its `compileExe` success. -/
theorem typedPremises_baseline :
    InScopePT baselineSpec.input = true ∧ OutOkT baselineSpec.input = true ∧
      leanLink baselineSpec baselineFile0 = .ok fileB :=
  typedPremises_of_compileExe compile_eqB

/-- **Witness**: `Link.compileExe_correct_viaT` on the integer witness. -/
theorem viaT_baseline := @compileExe_correct_viaT baselineSpec baselineFile0 fileB compile_eqB

end E2E.FloatExeTWitness
