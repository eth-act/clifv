import FV.Link.DeadCleanupCompileT
import FV.E2E.VerifiableT
import FV.E2E.LinkScopeInputDefsT
import FV.E2E.LinkScopeInputDefsTC
import FVTest.Link.DeadCleanupWitness
import FVTest.E2E.FloatFinalT

/-! Non-vacuity of the link-level chain with the proven float operations (S11f, #35).

On a program whose single function `%fa` has float arithmetic (`fadd`, `fmul`) and a scalar
`fcmp` (outside subset E, the typed movement scope and the scope with typed `try_call`s; inside
`Compile.functionETCF`), `Link.DeadCleanup.compileExeT` succeeds through its third branch: the
dead-cleanup checker `okBCleanupT` (via `okBCleanupTFast`, whose lowering check is now
`lowerCheckTCF`) accepts the compiled code and the Lean linker succeeds, so
`compileExeT_correct` applies (`correct_spec`); `lean-link --verified` admits the function
(`fnScopeInTCB`). The per-function premises of the `TCF` link theorems hold for `%fa`
(`InSubsetTCF`, the legacy artifact `CompiledTCF`, the dead-cleanup artifact
`CompiledCleanupTCF`), and the world theorems are instantiated with them (`*_w`). Decided by
`native_decide` (witness only). `lake build FVTest.Link.FloatArithCompileExeT`. -/

namespace E2E.FloatArithCompileExeTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill
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

def fA : FnInput := { clif := srcArith, ra := "{}" }

def fns : List FnInput := [fA]

/-- The dead-cleanup pipeline's link of the float-arithmetic program. -/
def spec : LinkSpec :=
  { funcs := fns, names := fns.map (·.func.name),
    sizes := fns.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := [], R := 0x1000000 }

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

/-- `%fa` has float arithmetic and a scalar `fcmp`: outside subset E, the typed movement scope
and the scope with typed `try_call`s, in the scope with the proven float operations;
`lowerCheckTC` rejects its lowering and `lowerCheckTCF` accepts it. -/
def arithB : Bool :=
  !Compile.functionE fA.func && !Compile.functionET fA.func && !Compile.functionETC fA.func &&
  Compile.functionETCF fA.func &&
  (match lowerFunction fA.func with
    | .ok vc => !lowerCheckTC fA.func vc && lowerCheckTCF fA.func vc
    | .error _ => false)

/-- `lean-link --verified`'s per-function admission: `%fa` fails `fnScopeInTB` and meets
`fnScopeInTCB`. -/
def admitB : Bool := !fnScopeInTB fA.func && fnScopeInTCB fA.func

def checks : Bool :=
  arithB && admitB && !InScopeP spec.input0 && !InScopePT spec.input0 &&
  okBCleanupTFast spec.inputCleanup &&
  (Link.DeadCleanup.leanLink spec file0).toBool &&
  (Link.DeadCleanup.compileExeT spec file0).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

theorem parts : arithB = true ∧ admitB = true ∧ InScopeP spec.input0 = false ∧
    InScopePT spec.input0 = false ∧ okBCleanupTFast spec.inputCleanup = true ∧
    (Link.DeadCleanup.leanLink spec file0).toBool = true ∧
    (Link.DeadCleanup.compileExeT spec file0).toBool = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **Witness**: the checker accepts the float-arithmetic program (`okBCleanupT` with the
lowering check `lowerCheckTCF`). -/
theorem okBCleanupT_spec : okBCleanupT spec.inputCleanup = true :=
  okBCleanupTFast_eq spec.inputCleanup ▸ parts.2.2.2.2.1

def file : ByteArray := getOk (Link.DeadCleanup.compileExeT spec file0)

theorem compile_eq : Link.DeadCleanup.compileExeT spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact getOk_eq h.2

/-- **Witness**: `Link.DeadCleanup.compileExeT_correct` applies to the float-arithmetic program
(through the third branch). -/
theorem correct_spec :
    type_of% (@Link.DeadCleanup.compileExeT_correct spec file0 file compile_eq) :=
  @Link.DeadCleanup.compileExeT_correct spec file0 file compile_eq

/-! ## The per-function premises of the `TCF` link theorems -/

/-- `%fa`. -/
def fF : Clif.Function := fA.func

def vcA : VCode := FloatDriverT.vcOf fF

/-- The dead-cleanup artifact of `%fa` (`prune` before `prepare`, the spill allocation). -/
def vcpC : VCode :=
  match Backend.prepare (Backend.DeadCleanup.prune vcA) with
  | .ok vcp => vcp
  | .error _ => default

def rfC : RFunc := spillAlloc vcpC

def afC : AFunc :=
  match lowerRFunc vcpC rfC with
  | .ok af => af
  | .error _ => default

def faC : FnAsm :=
  match emitFunc 0 afC with
  | .ok fa => fa
  | .error _ => default

def fbC : FnBin :=
  match faC.layout with
  | .ok fb => fb
  | .error _ => default

/-- **Witness**: `%fa` is in the scope with the proven float operations, in a program without
functions. -/
theorem inSubsetTCF_w : InSubsetTCF { funcs := [] } fF :=
  InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl

theorem lower_w : lowerFunction fF = .ok vcA := by
  have hok : (lowerFunction fF).toBool = true := by native_decide
  unfold vcA FloatDriverT.vcOf
  cases h : lowerFunction fF with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

/-- **Witness**: the legacy artifact premise (`CompiledTCF`) holds for `%fa`. -/
theorem compiledTCF_w :
    CompiledTCF fF 0 vcA (FloatFinalT.vcpOf fF) (FloatFinalT.rfOf fF) (FloatFinalT.afOf fF)
      (FloatFinalT.faOf fF) (FloatFinalT.fbOf fF) := by
  refine ⟨lower_w, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (Backend.prepare (FloatDriverT.vcOf fF)).toBool = true := by native_decide
    show Backend.prepare (FloatDriverT.vcOf fF) = .ok (FloatFinalT.vcpOf fF)
    unfold FloatFinalT.vcpOf
    cases h : Backend.prepare (FloatDriverT.vcOf fF) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (FloatFinalT.vcpOf fF) (FloatFinalT.rfOf fF)).isOk = true := by
      native_decide
    cases h : checkAlloc (FloatFinalT.vcpOf fF) (FloatFinalT.rfOf fF) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (FloatFinalT.vcpOf fF) (FloatFinalT.rfOf fF)).toBool = true := by
      native_decide
    unfold FloatFinalT.afOf
    cases h : lowerRFunc (FloatFinalT.vcpOf fF) (FloatFinalT.rfOf fF) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (FloatFinalT.afOf fF)).toBool = true := by native_decide
    unfold FloatFinalT.faOf
    cases h : emitFunc 0 (FloatFinalT.afOf fF) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (FloatFinalT.faOf fF).layout.toBool = true := by native_decide
    unfold FloatFinalT.fbOf
    cases h : (FloatFinalT.faOf fF).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness**: the dead-cleanup artifact premise (`CompiledCleanupTCF`) holds for `%fa`. -/
theorem compiledCleanupTCF_w : CompiledCleanupTCF fF 0 vcA vcpC rfC afC faC fbC := by
  refine ⟨lower_w, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (Backend.prepare (Backend.DeadCleanup.prune vcA)).toBool = true := by
      native_decide
    unfold vcpC
    cases h : Backend.prepare (Backend.DeadCleanup.prune vcA) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc vcpC rfC).isOk = true := by native_decide
    cases h : checkAlloc vcpC rfC with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc vcpC rfC).toBool = true := by native_decide
    unfold afC
    cases h : lowerRFunc vcpC rfC with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 afC).toBool = true := by native_decide
    unfold faC
    cases h : emitFunc 0 afC with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : faC.layout.toBool = true := by native_decide
    unfold fbC
    cases h : faC.layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness**: `%fa`'s dead-cleanup artifact is an artifact of either typed scope (the right
disjunct, `CompiledEitherTCF.cleanup`). -/
theorem compiledAnyT_w : CompiledAnyT { funcs := [] } fF 0 vcA vcpC rfC afC faC fbC :=
  .inr (.cleanup compiledCleanupTCF_w)

/-! ## The `TCF` world theorems on `%fa` -/

section
variable (X : ExtSem) (syms : String → Option Nat) (slotOff : Nat) (env : Clif.Env)
  (F : BitVec 64 → Prop) (c : BitVec 64) (K : Nat)

/-- **Witness**: `backend_correct_worldTCF` (and `backend_correct_world_niTCF`,
`backend_correct_worldXTCF`, `backend_correct_world_niXTCF`) on `%fa`'s legacy artifact. -/
theorem worldTCF_w :
    type_of% (backend_correct_worldTCF (X := X) (syms := syms) (slotOff := slotOff) (env := env)
      (F := F) (c := c) (K := K) inSubsetTCF_w compiledTCF_w typedRules_program) :=
  backend_correct_worldTCF inSubsetTCF_w compiledTCF_w typedRules_program

theorem world_niTCF_w :
    type_of% (backend_correct_world_niTCF (X := X) (syms := syms) (slotOff := slotOff) (env := env)
      (F := F) (c := c) (K := K) inSubsetTCF_w compiledTCF_w typedRules_program) :=
  backend_correct_world_niTCF inSubsetTCF_w compiledTCF_w typedRules_program

theorem worldXTCF_w :
    type_of% (backend_correct_worldXTCF (X := X) (syms := syms) (slotOff := slotOff) (env := env)
      (F := F) (c := c) (K := K) inSubsetTCF_w compiledTCF_w typedRules_program) :=
  backend_correct_worldXTCF inSubsetTCF_w compiledTCF_w typedRules_program

theorem world_niXTCF_w :
    type_of% (backend_correct_world_niXTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledTCF_w typedRules_program) :=
  backend_correct_world_niXTCF inSubsetTCF_w compiledTCF_w typedRules_program

/-- **Witness**: the dead-cleanup `TCF` world theorems on `%fa`'s dead-cleanup artifact. -/
theorem world_cleanupTCF_w :
    type_of% (backend_correct_world_cleanupTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledCleanupTCF_w
      typedRules_program) :=
  backend_correct_world_cleanupTCF inSubsetTCF_w compiledCleanupTCF_w typedRules_program

theorem world_ni_valueTCF_w :
    type_of% (backend_correct_world_ni_valueTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledCleanupTCF_w
      typedRules_program) :=
  backend_correct_world_ni_valueTCF inSubsetTCF_w compiledCleanupTCF_w typedRules_program

theorem worldX_cleanupTCF_w :
    type_of% (backend_correct_worldX_cleanupTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledCleanupTCF_w
      typedRules_program) :=
  backend_correct_worldX_cleanupTCF inSubsetTCF_w compiledCleanupTCF_w typedRules_program

theorem world_niX_cleanupTCF_w :
    type_of% (backend_correct_world_niX_cleanupTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledCleanupTCF_w
      typedRules_program) :=
  backend_correct_world_niX_cleanupTCF inSubsetTCF_w compiledCleanupTCF_w typedRules_program

/-- **Witness**: the `CompiledEitherTCF` dispatch on both artifacts of `%fa`. -/
theorem world_pipelineTCF_w :
    type_of% (backend_correct_world_pipelineTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w (.legacy compiledTCF_w)
      typedRules_program) :=
  backend_correct_world_pipelineTCF inSubsetTCF_w (.legacy compiledTCF_w) typedRules_program

theorem world_ni_pipelineTCF_w :
    type_of% (backend_correct_world_ni_pipelineTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w (.cleanup compiledCleanupTCF_w)
      typedRules_program) :=
  backend_correct_world_ni_pipelineTCF inSubsetTCF_w (.cleanup compiledCleanupTCF_w)
    typedRules_program

theorem worldX_pipelineTCF_w :
    type_of% (backend_correct_worldX_pipelineTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w (.cleanup compiledCleanupTCF_w)
      typedRules_program) :=
  backend_correct_worldX_pipelineTCF inSubsetTCF_w (.cleanup compiledCleanupTCF_w)
    typedRules_program

theorem world_niX_pipelineTCF_w :
    type_of% (backend_correct_world_niX_pipelineTCF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w (.legacy compiledTCF_w)
      typedRules_program) :=
  backend_correct_world_niX_pipelineTCF inSubsetTCF_w (.legacy compiledTCF_w) typedRules_program

/-- **Witness**: the `CompiledAnyT` dispatch with the scope `InSubsetTCF` on `%fa` (the
consumers of `LinkSys.OkT`). -/
theorem world_pipelineAnyTF_w :
    type_of% (backend_correct_world_pipelineAnyTF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledAnyT_w typedRules_program) :=
  backend_correct_world_pipelineAnyTF inSubsetTCF_w compiledAnyT_w typedRules_program

theorem world_ni_pipelineAnyTF_w :
    type_of% (backend_correct_world_ni_pipelineAnyTF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledAnyT_w typedRules_program) :=
  backend_correct_world_ni_pipelineAnyTF inSubsetTCF_w compiledAnyT_w typedRules_program

theorem worldX_pipelineAnyTF_w :
    type_of% (backend_correct_worldX_pipelineAnyTF (X := X) (syms := syms) (slotOff := slotOff)
      (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledAnyT_w typedRules_program) :=
  backend_correct_worldX_pipelineAnyTF inSubsetTCF_w compiledAnyT_w typedRules_program

theorem world_niX_pipelineAnyTF_w :
    type_of% (backend_correct_world_niX_pipelineAnyTF (X := X) (syms := syms)
      (slotOff := slotOff) (env := env) (F := F) (c := c) (K := K) inSubsetTCF_w compiledAnyT_w
      typedRules_program) :=
  backend_correct_world_niX_pipelineAnyTF inSubsetTCF_w compiledAnyT_w typedRules_program

end

end E2E.FloatArithCompileExeTWitness
