import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.SpillInstCheck
import FV.Backend.Proof.SpillLocalPipeT
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.SpillArity
import FVTest.Backend.FloatDriverT

/-!
Non-vacuity of the typed spill-allocation chain (S11e5 Stage C, slice 6): on the float-movement
function `fMv` (outside subset E: float parameters, loads/stores, constants, `select`, `bitcast`,
float block parameters and edge arguments, a float return), the premises of `classesHypT`,
`edgesHyp_ofT`, `spillLocalOk_of_pipelineT` and `spillAcceptedT` hold — the input checks
`Compile.tryArgClassOk`, `resClassOkB`, `arityOkB`, `dominatedB`, and on the prepared code the
decided premises `ctlSpillB`, `formsCoveredB`, `killFreeB` — so the typed theorems give
`ClassesOk`, `EdgesOk`, `SpillLocalOk` and `AllocChecked` of the spill allocation (which keeps
the 128-bit FP spill slots). `checkAlloc` also accepts the spill allocation directly. Checks by
`native_decide` (witness only). `lake build FVTest.Backend.FloatSpillT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

namespace FloatSpillT

open FloatDriverT

/-- `prepare`'s output on `fMv`'s lowering (`default` if it fails). -/
def vcpOf (f : Clif.Function) : VCode :=
  match Backend.prepare (vcOf f) with
  | .ok vcp => vcp
  | .error _ => default

-- the prepared code has float vregs (block parameters, edge arguments, operands)
#guard (vcpOf fMv).classes.contains .float
#guard (vcpOf fMv).blocks.any fun vb => vb.params.any (·.homeCls == .float)
-- the decided premises
#guard Compile.tryArgClassOk fMv && resClassOkB fMv && Spill.arityOkB fMv && dominatedB fMv
#guard ctlSpillB (vcOf fMv) && formsCoveredB default (vcpOf fMv) && killFreeB (vcpOf fMv)
#guard (checkAlloc (vcpOf fMv) (spillAlloc (vcpOf fMv))).isOk

theorem prepare_mv : Backend.prepare (vcOf fMv) = .ok (vcpOf fMv) := by
  have hok : (Backend.prepare (vcOf fMv)).toBool = true := by native_decide
  unfold vcpOf
  cases h : Backend.prepare (vcOf fMv) with
  | error e => rw [h] at hok; cases hok
  | ok vcp => rfl

theorem dominated_mv : Dominated fMv := dominated_of (by native_decide)
theorem arityOk_mv : ArityOk fMv := arityOk_of (by native_decide)
theorem tryArgClassOk_mv : Compile.tryArgClassOk fMv = true := by native_decide
theorem resClassOk_mv : ResClassOk fMv := resClassOk_of_resClassOkB (by native_decide)
theorem ctlSpill_mv : ∀ vb ∈ (vcOf fMv).blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true →
    SpillInstOk i := ctlSpill_of_ctlSpillB (by native_decide)
theorem formsCovered_mv : FormsCovered default (vcpOf fMv) :=
  (formsCoveredB_iff _ _).mp (by native_decide)
theorem killFree_mv : killFreeB (vcpOf fMv) = true := by native_decide

/-- **Non-vacuity of `classesHypT`**. -/
theorem classesHypT_mv : ClassesOk (vcpOf fMv) :=
  classesHypT fMv (vcOf fMv) (vcpOf fMv) dominated_mv scopeT_mv resClassOk_mv lowerFunction_mv
    prepare_mv

/-- **Non-vacuity of `edgesHyp_ofT`** (with `lowOk_ofT`, `prepDomain_ofT`). -/
theorem edgesHyp_ofT_mv : ∃ succs preds, (vcpOf fMv).cfg = .ok (succs, preds) ∧
    EdgesOk (vcpOf fMv) succs preds := by
  obtain ⟨ss, ps, h⟩ := cfg_ok_of_prepare prepare_mv (prepDomain_ofT dominated_mv scopeT_mv lowerFunction_mv)
  exact ⟨ss, ps, h, edgesHyp_ofT dominated_mv scopeT_mv arityOk_mv tryArgClassOk_mv lowerFunction_mv
    prepare_mv ss ps h⟩

/-- **Non-vacuity of `spillLocalOk_of_pipelineT`**. -/
theorem spillLocalOk_mv : SpillLocalOk (vcpOf fMv) :=
  spillLocalOk_of_pipelineT dominated_mv scopeT_mv arityOk_mv tryArgClassOk_mv resClassOk_mv
    lowerFunction_mv prepare_mv ctlSpill_mv formsCovered_mv

/-- **Non-vacuity of `spillAcceptedT`**: the spill allocation of `fMv`'s prepared code is
`AllocChecked`. -/
theorem spillAcceptedT_mv : AllocChecked (vcpOf fMv) (spillAlloc (vcpOf fMv)) :=
  spillAcceptedT dominated_mv scopeT_mv arityOk_mv tryArgClassOk_mv resClassOk_mv lowerFunction_mv
    prepare_mv ctlSpill_mv formsCovered_mv killFree_mv

/-- **Non-vacuity of `allocChecked_allocResultT`** (regalloc2 absent: the spill allocation). -/
theorem allocChecked_allocResultT_mv :
    AllocChecked (vcpOf fMv) (allocResult (vcpOf fMv) (.error "regalloc2 absent")) :=
  allocChecked_allocResultT dominated_mv scopeT_mv arityOk_mv tryArgClassOk_mv resClassOk_mv
    lowerFunction_mv prepare_mv ctlSpill_mv formsCovered_mv killFree_mv _

/-- `checkAlloc` accepts the spill allocation of `fMv`'s prepared code. -/
theorem checkAlloc_mv : checkAlloc (vcpOf fMv) (spillAlloc (vcpOf fMv)) = .ok () := by
  have h : (checkAlloc (vcpOf fMv) (spillAlloc (vcpOf fMv))).isOk = true := by native_decide
  cases hc : checkAlloc (vcpOf fMv) (spillAlloc (vcpOf fMv)) with
  | ok u => rfl
  | error e => rw [hc] at h; cases h

/-- **Non-vacuity of `classesOkB`**: it accepts `fMv`'s prepared code. -/
theorem classesOkB_mv : ClassesOk (vcpOf fMv) := classesOk_of_classesOkB (by native_decide)

-- the input checks are not trivially true: `classesOkB` rejects a missing class, `tryArgClassOk`
-- a `try_call` return passed to an `f64` parameter
#guard !classesOkB { vcpOf fMv with classes := #[] }
#guard !Compile.tryArgClassOk (fnOfText
  "function %t(i64) -> f64 tail {\n  sig0 = (i64) -> i64 tail\n  fn0 = %g(i64) -> i64 tail\n\nblock0(v0: i64):\n  try_call fn0(v0), sig0, block1(ret0), [ default: block2(exn0) ]\n\nblock1(v1: f64):\n  return v1\n\nblock2(v2: i64):\n  v3 = f64const 0x0.0p0\n  return v3\n}\n")

/-! ## The integer specializations -/

/-- An integer loop with block parameters (subset E; `E.lowerWitness`'s source). -/
def fInt : Clif.Function := fnOfText
  "function %sum(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 0
    jump block1(v0, v1)
block1(v2: i64, v3: i64):
    v4 = iadd v3, v2
    v5 = iconst.i64 1
    v6 = isub v2, v5
    brif v6, block1(v6, v4), block2
block2:
    return v4
}"

theorem prepare_int : Backend.prepare (vcOf fInt) = .ok (vcpOf fInt) := by
  have hok : (Backend.prepare (vcOf fInt)).toBool = true := by native_decide
  unfold vcpOf
  cases h : Backend.prepare (vcOf fInt) with
  | error e => rw [h] at hok; cases hok
  | ok vcp => rfl

theorem lowerFunction_int : lowerFunction fInt = .ok (vcOf fInt) := by
  have hok : (lowerFunction fInt).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fInt with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

/-- **Non-vacuity of the integer specializations** (`classesHyp_of_T`, `edgesHyp_of_toT`,
`resClassOk_of_lowerScope`, `spillLocalOk_of_pipelineT_int`) on a function of subset E. -/
theorem spillLocalOk_int : ClassesOk (vcpOf fInt) ∧ SpillLocalOk (vcpOf fInt) := by
  have hd : Dominated fInt := dominated_of (by native_decide)
  have hs : LowerScope fInt := lowerScope_of (by native_decide)
  have ha : ArityOk fInt := arityOk_of (by native_decide)
  exact ⟨classesHyp_of_T fInt _ _ hd hs lowerFunction_int prepare_int,
    spillLocalOk_of_pipelineT_int hd hs ha lowerFunction_int prepare_int
      (ctlSpill_of_ctlSpillB (by native_decide))⟩

theorem edgesHyp_int : ∀ succs preds, (vcpOf fInt).cfg = .ok (succs, preds) →
    EdgesOk (vcpOf fInt) succs preds :=
  edgesHyp_of_toT (dominated_of (by native_decide)) (lowerScope_of (by native_decide))
    (arityOk_of (by native_decide)) lowerFunction_int prepare_int

end FloatSpillT
