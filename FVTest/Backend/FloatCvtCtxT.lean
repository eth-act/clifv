import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselFloatCvt

/-!
Non-vacuity of the S11f-cvt roots (#410): the context `buildCtx` makes for a function with
every float <-> integer conversion root of the closure (`fcvt_from_{u,s}int` to `f32`/`f64` from
`i8`/`i16`/`i32` and `i64`, `fcvt_to_{u,s}int_sat` to `i32`/`i64` from `f32`/`f64`) passes
`ctxOkT` (by `native_decide`, witness only), so `ctxOkT_sound` gives `CtxInvT` for it, and the
ISLE `lower` term fires each of the sixteen roots (`fcvt_from_uint_f32_le32_okT` …
`fcvt_to_sint_sat_i64_f64_okT`, `IselFloatCvt`) on its instructions.

The value witnesses check the shared IEEE core at the boundary inputs (NaN, ±∞, values beyond
the range, -0.0, a halfway tie): CLIF's `FSem.toIntSat`/`FSem.fromInt` and the Arm side
(`fpuToIntVal`/`intToFpuVal`, the `ispecFP` meaning of `fcvtz{s,u}`/`{s,u}cvtf`) give the same
bits (`native_decide`, witnesses only). `lake build FVTest.Backend.FloatCvtCtxT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

/-- The first function of a CLIF text. -/
def fnOfTextC (src : String) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => f
    | .error _ => default
  | [] => default

/-- `buildCtx`'s context and initial lowering state of a function (an empty context if it fails). -/
def ctxStOfC (f : Clif.Function) : Ctx × LState :=
  match buildCtx f with
  | .ok (ctx, _, st) => (ctx, st)
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] },
      default)

def fCvt : Clif.Function := fnOfTextC
  "function %c(i8, i16, i32, i64, f32, f64) -> i64 {\nblock0(v0: i8, v1: i16, v2: i32, v3: i64, v4: f32, v5: f64):\n    v6 = fcvt_from_uint.f32 v0\n    v7 = fcvt_from_uint.f64 v1\n    v8 = fcvt_from_uint.f32 v3\n    v9 = fcvt_from_uint.f64 v3\n    v10 = fcvt_from_sint.f32 v2\n    v11 = fcvt_from_sint.f64 v0\n    v12 = fcvt_from_sint.f32 v3\n    v13 = fcvt_from_sint.f64 v3\n    v14 = fcvt_to_uint_sat.i32 v4\n    v15 = fcvt_to_uint_sat.i64 v4\n    v16 = fcvt_to_uint_sat.i32 v5\n    v17 = fcvt_to_uint_sat.i64 v5\n    v18 = fcvt_to_sint_sat.i32 v4\n    v19 = fcvt_to_sint_sat.i64 v4\n    v20 = fcvt_to_sint_sat.i32 v5\n    v21 = fcvt_to_sint_sat.i64 v5\n    return v21\n}\n"

/-- The lowering trace of instruction `ii` (the ids of the rules that fired), or `[]`. -/
def lowerTraceC (f : Clif.Function) (ii : Nat) : List Isle.RuleId :=
  let (ctx, st) := ctxStOfC f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some (.regsVec _), _, tr) => tr
  | _ => []

-- `buildCtx` succeeds and the instructions are the conversions
#guard (buildCtx fCvt).toBool
#guard (ctxStOfC fCvt).1.insts[0]?.bind (·.clif) == some (.float .fcvtFromUint .f32 [0])
#guard (ctxStOfC fCvt).1.insts[15]?.bind (·.clif) == some (.float .fcvtToSintSat .i64 [5])
-- `lower` fires the sixteen conversion roots, in order, on them
#guard [rule_lower_724, rule_lower_727, rule_lower_730, rule_lower_733, rule_lower_744,
    rule_lower_747, rule_lower_750, rule_lower_753, rule_lower_764, rule_lower_767,
    rule_lower_770, rule_lower_773, rule_lower_784, rule_lower_787, rule_lower_790,
    rule_lower_793].zipIdx.all fun (r, ii) => (lowerTraceC fCvt ii).contains r.id

/-- **`CtxInvT` holds for the conversion context.** -/
theorem ctxInvT_float_cvt : CtxInvT fCvt (ctxStOfC fCvt).1 :=
  ctxOkT_sound (by native_decide)

/-- **The conversion roots apply to this context**: its `fcvt_from_uint.f32` of an `i8`
(instruction 0) lies in a `CtxInvT` context and `rule_lower_724` is a root of `lower`, so
`fcvt_from_uint_f32_le32_okT` gives `LowerRuleOkT` for the rule on it. -/
theorem float_cvt_root_applies :
    CtxInvT fCvt (ctxStOfC fCvt).1 ∧
      ((ctxStOfC fCvt).1.insts[0]?.bind (·.clif)) = some (.float .fcvtFromUint .f32 [0]) ∧
      rule_lower_724 ∈ program.rulesOf TId.lower ∧
      (∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) env cp, Refines F isem →
        MRStable F MR → LowerRuleOkT isem MR env cp program rule_lower_724) :=
  ⟨ctxInvT_float_cvt, by native_decide,
    by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel,
    fun _ _ MR env cp hR hMR => fcvt_from_uint_f32_le32_okT data_program MR env cp hR hMR⟩

/-! ## Boundary values: CLIF and the emitted instruction agree -/

/-- `fcvtz{s,u}` at `op` on the float bits `x` (`fpuToIntVal`), the low `w` bits. -/
def armToInt (op : FpuToIntOp) (w : Nat) {n : Nat} (x : BitVec n) : BitVec w :=
  (fpuToIntVal op (x.setWidth 128)).setWidth w

/-- `{s,u}cvtf` at `op` on the X-register value `x` (`intToFpuVal`), the low `w` bits. -/
def armFromInt (op : IntToFpuOp) (w : Nat) (x : BitVec 64) : BitVec w :=
  (intToFpuVal op (x.setWidth 128)).setWidth w

/-- `fcvt_to_uint_sat.i32` of an `f32`: NaN, +∞, -∞, -0.0, 2^32 (beyond the range), -1.5. -/
theorem cvt_u32_f32_boundary :
    [0x7fc00000#32, 0x7f800000#32, 0xff800000#32, 0x80000000#32, 0x4f800000#32,
      0xbfc00000#32].map (fun x => Clif.FSem.toIntSat true 32 .f32 x) =
      [some 0#32, some 0xffffffff#32, some 0#32, some 0#32, some 0xffffffff#32, some 0#32] ∧
    [0x7fc00000#32, 0x7f800000#32, 0xff800000#32, 0x80000000#32, 0x4f800000#32,
      0xbfc00000#32].map (fun x => some (armToInt .f32ToU32 32 x)) =
      [some 0#32, some 0xffffffff#32, some 0#32, some 0#32, some 0xffffffff#32, some 0#32] := by
  native_decide

/-- `fcvt_to_sint_sat.i32` of an `f32`: NaN, +∞, -∞, -0.0, 2^31, below -2^31. -/
theorem cvt_s32_f32_boundary :
    [0x7fc00000#32, 0x7f800000#32, 0xff800000#32, 0x80000000#32, 0x4f000000#32,
      0xcf000001#32].map (fun x => (Clif.FSem.toIntSat false 32 .f32 x, some (armToInt .f32ToI32 32 x))) =
      [(some 0#32, some 0#32), (some 0x7fffffff#32, some 0x7fffffff#32),
        (some 0x80000000#32, some 0x80000000#32), (some 0#32, some 0#32),
        (some 0x7fffffff#32, some 0x7fffffff#32), (some 0x80000000#32, some 0x80000000#32)] := by
  native_decide

/-- `fcvt_to_uint_sat.i64` of an `f32`: NaN, +∞, -∞, -0.0, 2^64. -/
theorem cvt_u64_f32_boundary :
    [0x7fc00000#32, 0x7f800000#32, 0xff800000#32, 0x80000000#32, 0x5f800000#32].map
      (fun x => (Clif.FSem.toIntSat true 64 .f32 x, some (armToInt .f32ToU64 64 x))) =
      [(some 0#64, some 0#64), (some 0xffffffffffffffff#64, some 0xffffffffffffffff#64),
        (some 0#64, some 0#64),
        (some 0#64, some 0#64), (some 0xffffffffffffffff#64, some 0xffffffffffffffff#64)] := by
  native_decide

/-- `fcvt_to_sint_sat.i64` of an `f32`: NaN, +∞, -∞, -0.0, 2^63, below -2^63. -/
theorem cvt_s64_f32_boundary :
    [0x7fc00000#32, 0x7f800000#32, 0xff800000#32, 0x80000000#32, 0x5f000000#32,
      0xdf000001#32].map (fun x => (Clif.FSem.toIntSat false 64 .f32 x, some (armToInt .f32ToI64 64 x))) =
      [(some 0#64, some 0#64), (some 0x7fffffffffffffff#64, some 0x7fffffffffffffff#64),
        (some 0x8000000000000000#64, some 0x8000000000000000#64), (some 0#64, some 0#64),
        (some 0x7fffffffffffffff#64, some 0x7fffffffffffffff#64),
        (some 0x8000000000000000#64, some 0x8000000000000000#64)] := by
  native_decide

/-- `fcvt_to_uint_sat.i32` of an `f64`: NaN, +∞, -∞, -0.0, 2^32, 2^32 - 0.5 (truncated). -/
theorem cvt_u32_f64_boundary :
    [0x7ff8000000000000#64, 0x7ff0000000000000#64, 0xfff0000000000000#64, 0x8000000000000000#64,
      0x41f0000000000000#64, 0x41efffffffff0000#64].map
      (fun x => (Clif.FSem.toIntSat true 32 .f64 x, some (armToInt .f64ToU32 32 x))) =
      [(some 0#32, some 0#32), (some 0xffffffff#32, some 0xffffffff#32), (some 0#32, some 0#32),
        (some 0#32, some 0#32), (some 0xffffffff#32, some 0xffffffff#32),
        (some 0xffffffff#32, some 0xffffffff#32)] := by
  native_decide

/-- `fcvt_to_sint_sat.i32` of an `f64`: NaN, +∞, -∞, -0.0, 2^31, -2^31 - 1. -/
theorem cvt_s32_f64_boundary :
    [0x7ff8000000000000#64, 0x7ff0000000000000#64, 0xfff0000000000000#64, 0x8000000000000000#64,
      0x41e0000000000000#64, 0xc1e0000000200000#64].map
      (fun x => (Clif.FSem.toIntSat false 32 .f64 x, some (armToInt .f64ToI32 32 x))) =
      [(some 0#32, some 0#32), (some 0x7fffffff#32, some 0x7fffffff#32),
        (some 0x80000000#32, some 0x80000000#32), (some 0#32, some 0#32),
        (some 0x7fffffff#32, some 0x7fffffff#32), (some 0x80000000#32, some 0x80000000#32)] := by
  native_decide

/-- `fcvt_to_uint_sat.i64` of an `f64`: NaN, +∞, -∞, -0.0, 2^64, the largest double below. -/
theorem cvt_u64_f64_boundary :
    [0x7ff8000000000000#64, 0x7ff0000000000000#64, 0xfff0000000000000#64, 0x8000000000000000#64,
      0x43f0000000000000#64, 0x43efffffffffffff#64].map
      (fun x => (Clif.FSem.toIntSat true 64 .f64 x, some (armToInt .f64ToU64 64 x))) =
      [(some 0#64, some 0#64), (some 0xffffffffffffffff#64, some 0xffffffffffffffff#64),
        (some 0#64, some 0#64),
        (some 0#64, some 0#64), (some 0xffffffffffffffff#64, some 0xffffffffffffffff#64),
        (some 0xfffffffffffff800#64, some 0xfffffffffffff800#64)] := by
  native_decide

/-- `fcvt_to_sint_sat.i64` of an `f64`: NaN, +∞, -∞, -0.0, 2^63, -2^63, -2.5. -/
theorem cvt_s64_f64_boundary :
    [0x7ff8000000000000#64, 0x7ff0000000000000#64, 0xfff0000000000000#64, 0x8000000000000000#64,
      0x43e0000000000000#64, 0xc3e0000000000000#64, 0xc004000000000000#64].map
      (fun x => (Clif.FSem.toIntSat false 64 .f64 x, some (armToInt .f64ToI64 64 x))) =
      [(some 0#64, some 0#64), (some 0x7fffffffffffffff#64, some 0x7fffffffffffffff#64),
        (some 0x8000000000000000#64, some 0x8000000000000000#64), (some 0#64, some 0#64),
        (some 0x7fffffffffffffff#64, some 0x7fffffffffffffff#64),
        (some 0x8000000000000000#64, some 0x8000000000000000#64),
        (some 0xfffffffffffffffe#64, some 0xfffffffffffffffe#64)] := by
  native_decide

/-- `fcvt_from_{u,s}int` (zero is `+0.0`, `u32::MAX`/`u64::MAX` round up to 2^32/2^64, the
halfway tie 2^24 + 1 rounds to even, `i32::MIN`/`i64::MIN` are exact): CLIF's `FSem.fromInt`
and `{s,u}cvtf` on the (extended) X register agree. -/
theorem cvt_from_boundary :
    Clif.FSem.fromInt true (0#32) .f32 = some (armFromInt .u32ToF32 Clif.Ty.f32.width 0) ∧
    Clif.FSem.fromInt true (0xffffffff#32) .f32 =
      some (armFromInt .u32ToF32 Clif.Ty.f32.width 0xffffffff) ∧
    Clif.FSem.fromInt true (0x01000001#32) .f32 =
      some (armFromInt .u32ToF32 Clif.Ty.f32.width 0x01000001) ∧
    Clif.FSem.fromInt false (0x80000000#32) .f32 =
      some (armFromInt .i32ToF32 Clif.Ty.f32.width 0x80000000) ∧
    Clif.FSem.fromInt true (0xffffffffffffffff#64) .f64 =
      some (armFromInt .u64ToF64 Clif.Ty.f64.width (-1)) ∧
    Clif.FSem.fromInt false (0x8000000000000000#64) .f64 =
      some (armFromInt .i64ToF64 Clif.Ty.f64.width 0x8000000000000000) ∧
    Clif.FSem.fromInt false (0xff#8) .f32 =
      some (armFromInt .i32ToF32 Clif.Ty.f32.width ((0xff#8).signExtend 64)) ∧
    Clif.FSem.fromInt true (0xffff#16) .f64 =
      some (armFromInt .u32ToF64 Clif.Ty.f64.width ((0xffff#16).setWidth 64)) ∧
    (armFromInt .u32ToF32 32 0, armFromInt .u32ToF32 32 0xffffffff,
      armFromInt .u32ToF32 32 0x01000001, armFromInt .i32ToF32 32 0x80000000,
      armFromInt .u64ToF64 64 (-1), armFromInt .i64ToF64 64 0x8000000000000000,
      armFromInt .i32ToF32 32 ((0xff#8).signExtend 64)) =
    (0#32, 0x4f800000#32, 0x4b800000#32, 0xcf000000#32, 0x43f0000000000000#64,
      0xc3e0000000000000#64, 0xbf800000#32) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide
