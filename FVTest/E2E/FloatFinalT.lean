import FV.E2E.FinalT
import FVTest.Backend.FloatDriverT

/-!
Non-vacuity of the typed final theorem's structural premises (S11e5 Stage C, slice 7): the
function `fW` moves `f64` values (a float `load`, an `f64const`, a float `select`, a float
`store`, a `bitcast` to an integer) between integer parameters and an integer return. It is
outside subset E and inside the typed scope (`InSubsetT`), and the whole pipeline — typed
lowering validator `lowerCheckT`, `prepare` + `prepCheck`, the spill allocation accepted by
`checkAlloc`, `lowerRFunc` (with its control-form check), emission and layout — succeeds
(`CompiledT`, hence `CompiledAT`); the prepared code's forms are covered (`FormsCovered`). These
are the premises of `backend_correct_finalT`/`_exT` besides the typed M4 families
(`TypedRules`) and the run/link contracts.

`fMv` (float parameters and a float return) is in `InSubsetT` and passes the validators and
`checkAlloc`, but `lowerRFunc`'s control-form check (`ctlCheck`: integer `Args`/`Rets` vregs)
rejects it until slice 5 widens `ctlInstOk`. Checks by `native_decide` (witness only).
`lake build FVTest.E2E.FloatFinalT`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E

namespace FloatFinalT

open FloatDriverT

/-- Float data movement between integer parameters and an integer return. -/
def fW : Clif.Function := fnOfText
  "function %w(i64, i8) -> i64 {
block0(v0: i64, v1: i8):
    v2 = load.f64 v0
    v3 = f64const 0x1.0p-2
    v4 = select v1, v2, v3
    store v4, v0+8
    v5 = bitcast.i64 v4
    return v5
}
"

/-- `prepare`'s output on the lowering (`default` if it fails). -/
def vcpOf (f : Clif.Function) : VCode :=
  match Backend.prepare (vcOf f) with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation of the prepared code. -/
def rfOf (f : Clif.Function) : RFunc := spillAlloc (vcpOf f)

def afOf (f : Clif.Function) : AFunc :=
  match lowerRFunc (vcpOf f) (rfOf f) with
  | .ok af => af
  | .error _ => default

def faOf (f : Clif.Function) : FnAsm :=
  match emitFunc 0 (afOf f) with
  | .ok fa => fa
  | .error _ => default

def fbOf (f : Clif.Function) : FnBin :=
  match (faOf f).layout with
  | .ok fb => fb
  | .error _ => default

-- `fW` is outside subset E, inside the typed scope; its pipeline succeeds
#guard !Compile.functionE fW && Compile.functionET fW
#guard (lowerFunction fW).toBool && !lowerCheck fW (vcOf fW) && lowerCheckT fW (vcOf fW)
#guard (vcOf fW).blocks.any fun vb => vb.insts.any (· matches .fpuLoad ..)
#guard (lowerRFunc (vcpOf fW) (rfOf fW)).toBool && (emitFunc 0 (afOf fW)).toBool &&
  (faOf fW).layout.toBool
-- `fMv` passes the validators and `checkAlloc`, not yet `lowerRFunc`'s `ctlCheck` (slice 5)
#guard lowerCheckT fMv (vcOf fMv) && (checkAlloc (vcpOf fMv) (rfOf fMv)).isOk &&
  !(lowerRFunc (vcpOf fMv) (rfOf fMv)).toBool && !ctlCheck (vcpOf fMv) (rfOf fMv)

theorem lowerFunction_w : lowerFunction fW = .ok (vcOf fW) := by
  have hok : (lowerFunction fW).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fW with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

theorem prepare_w : Backend.prepare (vcOf fW) = .ok (vcpOf fW) := by
  have hok : (Backend.prepare (vcOf fW)).toBool = true := by native_decide
  unfold vcpOf
  cases h : Backend.prepare (vcOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok vcp => rfl

theorem alloc_w : lowerRFunc (vcpOf fW) (rfOf fW) = .ok (afOf fW) := by
  have hok : (lowerRFunc (vcpOf fW) (rfOf fW)).toBool = true := by native_decide
  unfold afOf
  cases h : lowerRFunc (vcpOf fW) (rfOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok af => rfl

theorem emit_w : emitFunc 0 (afOf fW) = .ok (faOf fW) := by
  have hok : (emitFunc 0 (afOf fW)).toBool = true := by native_decide
  unfold faOf
  cases h : emitFunc 0 (afOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok fa => rfl

theorem layout_w : (faOf fW).layout = .ok (fbOf fW) := by
  have hok : (faOf fW).layout.toBool = true := by native_decide
  unfold fbOf
  cases h : (faOf fW).layout with
  | error e => rw [h] at hok; cases hok
  | ok fb => rfl

theorem checkAlloc_w : checkAlloc (vcpOf fW) (rfOf fW) = .ok () := by
  have hok : (checkAlloc (vcpOf fW) (rfOf fW)).isOk = true := by native_decide
  cases h : checkAlloc (vcpOf fW) (rfOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok u => rfl

/-- **Witness**: `fW` is in the typed theorem's subset (outside subset E). -/
theorem inSubsetT_w (p : Clif.Program) : InSubsetT p fW := by
  have hnc : fW.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..)) = true := by
    native_decide
  have hnt : fW.blocks.all (fun B => !B.term.isTry) = true := by native_decide
  have habi : (sigAbiOk fW.sig && fW.externs.all (sigAbiOk ·.2.sig)) = true := by native_decide
  have hind : _root_.Backend.indSigs fW = [] := by native_decide
  simp only [Bool.and_eq_true, List.all_eq_true] at habi
  refine ⟨by native_decide, fun B hB st hst fn args hi _ _ => ?_, fun B hB fn args et ht _ _ => ?_,
    ⟨habi.1, fun e he => habi.2 e he⟩, by rw [hind]; simp⟩
  · have := List.all_eq_true.mp (List.all_eq_true.mp hnc B hB) st hst
    rw [hi] at this; cases this
  · have := List.all_eq_true.mp hnt B hB
    rw [ht] at this; cases this

/-- **Witness**: the typed compiled-code premise holds for `fW` (the spill allocation, accepted
by `checkAlloc`). -/
theorem compiledT_w :
    CompiledT fW 0 (vcOf fW) (vcpOf fW) (rfOf fW) (afOf fW) (faOf fW) (fbOf fW) :=
  ⟨lowerFunction_w, by native_decide, prepare_w, by native_decide, checkAlloc_w, alloc_w, emit_w,
    layout_w⟩

/-- **Witness**: … and so the `AllocChecked` form. -/
theorem compiledAT_w :
    CompiledAT fW 0 (vcOf fW) (vcpOf fW) (rfOf fW) (afOf fW) (faOf fW) (fbOf fW) :=
  compiledT_w.toA

/-- **Witness**: the prepared code's straight-line forms are covered (`hcov`). -/
theorem formsCovered_w : FormsCovered ⟨(faOf fW).k, (afOf fW).slotBase⟩ (vcpOf fW) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: the typed lowering obligations of `fW` (from `lowerCheckT`). -/
theorem loweringObligationsT_w : LoweringObligationsT fW (vcOf fW) :=
  loweringObligationsT_of_check compiledT_w.lowerOk

/-- **Witness**: `fMv` (float parameters, a float return) is in the typed subset too. -/
theorem inSubsetT_mv (p : Clif.Program) : InSubsetT p fMv := by
  have hnc : fMv.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..)) = true := by
    native_decide
  have hnt : fMv.blocks.all (fun B => !B.term.isTry) = true := by native_decide
  have habi : (sigAbiOk fMv.sig && fMv.externs.all (sigAbiOk ·.2.sig)) = true := by native_decide
  have hind : _root_.Backend.indSigs fMv = [] := by native_decide
  simp only [Bool.and_eq_true, List.all_eq_true] at habi
  refine ⟨functionET_mv, fun B hB st hst fn args hi _ _ => ?_, fun B hB fn args et ht _ _ => ?_,
    ⟨habi.1, fun e he => habi.2 e he⟩, by rw [hind]; simp⟩
  · have := List.all_eq_true.mp (List.all_eq_true.mp hnc B hB) st hst
    rw [hi] at this; cases this
  · have := List.all_eq_true.mp hnt B hB
    rw [ht] at this; cases this

end FloatFinalT
