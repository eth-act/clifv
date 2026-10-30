import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselExclT

/-!
Non-vacuity of S11f's rounding roots (#239): the context `buildCtx` makes for a function with
every scalar float rounding operation (`ceil floor trunc nearest` at `f32` and `f64`) passes the
Boolean check `ctxOkT` (by `native_decide`, witness only), so `ctxOkT_sound` gives `CtxInvT` for
it, and the ISLE `lower` term fires each of the eight rounding roots of `floatArithRootRule`
(`lowerRulesCorrectFT_program`) on its instructions — and not the generic-size rounding rules
(`lower.isle:564/575/586/597`, priority -1), whose `fpu_round` over a dynamic `scalar_size ty`
is unproven. Its instructions are in the arithmetic scope `InstScopeTA` (not in `InstScopeT`),
so `lower_nonroot_nomatchTA` excludes the roots outside the closure on them, e.g.
`rule_lower_58`.
`lake build FVTest.Backend.FloatRoundCtxT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

-- `decide +kernel` on `evalFloat` results (witness only; `Clif.Res` itself stays without it)
deriving instance DecidableEq for Clif.Res

/-- The `n`-th function of a CLIF text. -/
def fnOfTextR (src : String) (n : Nat := 0) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | fs => match fs[n]? with
    | some p => match p.func with
      | .ok f => f
      | .error _ => default
    | none => default

/-- `buildCtx`'s context and initial lowering state of a function (an empty context if it fails). -/
def ctxStOfR (f : Clif.Function) : Ctx × LState :=
  match buildCtx f with
  | .ok (ctx, _, st) => (ctx, st)
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] },
      default)

def fRound : Clif.Function := fnOfTextR
  "function %r32(i32, i64) -> i64 {\nblock0(v0: i32, v1: i64):\n    v2 = bitcast.f32 v0\n    v3 = ceil v2\n    v4 = floor v3\n    v5 = trunc v4\n    v6 = nearest v5\n    v7 = fpromote.f64 v6\n    v8 = ceil v7\n    v9 = floor v8\n    v10 = trunc v9\n    v11 = nearest v10\n    v12 = bitcast.i64 v11\n    v13 = bitcast.i32 v6\n    v14 = uextend.i64 v13\n    v15 = iadd v12, v14\n    return v15\n}\n"

/-- The lowering trace of instruction `ii` (the ids of the rules that fired), or `[]`. -/
def lowerTraceR (f : Clif.Function) (ii : Nat) : List Isle.RuleId :=
  let (ctx, st) := ctxStOfR f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some (.regsVec _), _, tr) => tr
  | _ => []

-- `buildCtx` succeeds and the instructions are the rounding operations
#guard (buildCtx fRound).toBool
#guard (ctxStOfR fRound).1.insts[1]?.bind (·.clif) == some (.float .ceil .f32 [2])
#guard (ctxStOfR fRound).1.insts[6]?.bind (·.clif) == some (.float .ceil .f64 [7])
#guard (ctxStOfR fRound).1.insts[9]?.bind (·.clif) == some (.float .nearest .f64 [10])
-- the float values have float vregs
#guard (ctxStOfR fRound).1.valueReg? 3 == some (.vreg 3 .float)
#guard (ctxStOfR fRound).1.valueReg? 11 == some (.vreg 11 .float)
-- `lower` fires the eight rounding roots (`floatArithRootRule`) on them, not the generic-size
-- rules 564/575/586/597 (ids 681/684/687/690, priority -1, dynamic `scalar_size`)
#guard [rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589,
  rule_lower_592, rule_lower_600, rule_lower_603].all floatArithRootRule
#guard (lowerTraceR fRound 1).contains 682 && (lowerTraceR fRound 2).contains 685 &&
  (lowerTraceR fRound 3).contains 688 && (lowerTraceR fRound 4).contains 691 &&
  (lowerTraceR fRound 6).contains 683 && (lowerTraceR fRound 7).contains 686 &&
  (lowerTraceR fRound 8).contains 689 && (lowerTraceR fRound 9).contains 692
#guard !((lowerTraceR fRound 1).contains 681 || (lowerTraceR fRound 3).contains 684 ||
  (lowerTraceR fRound 6).contains 687 || (lowerTraceR fRound 8).contains 690)

/-- **`CtxInvT` holds for the float rounding context.** -/
theorem ctxInvT_float_round : CtxInvT fRound (ctxStOfR fRound).1 :=
  ctxOkT_sound (by native_decide)

/-- **The roots of `LowerRulesCorrectFT` apply to this context**: its `ceil.f32` (instruction 1)
lies in a `CtxInvT` context and rule 682 (`rule_lower_567`) is a `floatArithRootRule` of
`lower`, so `lowerRulesCorrectFT_program` gives `LowerRuleOkT` for the rule on it. -/
theorem float_round_root_applies :
    CtxInvT fRound (ctxStOfR fRound).1 ∧
      ((ctxStOfR fRound).1.insts[1]?.bind (·.clif)) = some (.float .ceil .f32 [2]) ∧
      rule_lower_567 ∈ program.rulesOf TId.lower ∧ floatArithRootRule rule_lower_567 = true :=
  ⟨ctxInvT_float_round, by native_decide,
    by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel, rfl⟩

-- the check rejects the context with an `f32` value re-typed as an integer
#guard !ctxOkT fRound { (ctxStOfR fRound).1 with valTy := (ctxStOfR fRound).1.valTy.set! 3 (some (.int 32)) }

/-- **The float rounding context is in the arithmetic scope `InstScopeTA`.** -/
theorem instScopeTA_float_round : InstScopeTA (ctxStOfR fRound).1 := by
  have h : ((ctxStOfR fRound).1.insts.toList.all fun info =>
      match info.clif with
      | some c => Compile.instETA c
      | none => true) = true := by native_decide
  intro ii info inst hi hc
  have hm := List.all_eq_true.mp h info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
  rw [hc] at hm
  exact hm

/-- **`lower_nonroot_nomatchTA` applies to this context**: a root outside the closure
(`rule_lower_58`; the `fcmp` root `rule_lower_2176` is a closure root since S11f's `fcmp`)
matches none of its instructions, e.g. the `ceil.f32` (instruction 1). -/
theorem float_round_excluded_nomatch (cfg m s0 env s1) :
    (Isle.Interp.matchRule program (Backend.sem (ctxStOfR fRound).1) cfg m rule_lower_58
      [V.inst 1]).run s0 ≠ .ok (some env, s1) := by
  obtain ⟨info, hi⟩ : ∃ info, (ctxStOfR fRound).1.insts[1]? = some info :=
    Option.isSome_iff_exists.mp (by native_decide)
  obtain ⟨inst, hc⟩ : ∃ inst, info.clif = some inst := by
    refine Option.isSome_iff_exists.mp ?_
    have : ((ctxStOfR fRound).1.insts[1]?.bind (·.clif)).isSome = true := by native_decide
    rw [hi] at this
    exact this
  exact lower_nonroot_nomatchTA ctxInvT_float_round instScopeTA_float_round (by native_decide) hi
    hc (r := rule_lower_58)
    (by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel) (by decide)
    cfg m s0 env s1

/-! ## Edge values: the CLIF semantics and the emitted `fpu_round` agree (kernel-checked)

`Clif.evalFloat` of `ceil`/`floor`/`trunc`/`nearest` is `IEEE.roundInt` at `rpi`/`rmi`/`rz`/
`rne` (`FV/Clif/FSem.lean`), the same function `fpuRoundOut` (the Arm model's `FPRoundInt` with
`FPCR = 0`) applies; these witnesses check the edge behaviour of that shared function: signed
zeros, half-integer ties (rounding away for `ceil`/`floor`, to even for `nearest`, toward zero
for `trunc`), the largest f64 half-integer `2^52 - 0.5` (a tie for `nearest`), integral and huge
values unchanged, infinities, and quiet NaNs. -/

def ceilF32 (b : BitVec 32) : Clif.Res Clif.Val := Clif.evalFloat .ceil .f32 [⟨.f32, b⟩]
def floorF32 (b : BitVec 32) : Clif.Res Clif.Val := Clif.evalFloat .floor .f32 [⟨.f32, b⟩]
def truncF32 (b : BitVec 32) : Clif.Res Clif.Val := Clif.evalFloat .trunc .f32 [⟨.f32, b⟩]
def nearestF32 (b : BitVec 32) : Clif.Res Clif.Val := Clif.evalFloat .nearest .f32 [⟨.f32, b⟩]
def ceilF64 (b : BitVec 64) : Clif.Res Clif.Val := Clif.evalFloat .ceil .f64 [⟨.f64, b⟩]
def floorF64 (b : BitVec 64) : Clif.Res Clif.Val := Clif.evalFloat .floor .f64 [⟨.f64, b⟩]
def truncF64 (b : BitVec 64) : Clif.Res Clif.Val := Clif.evalFloat .trunc .f64 [⟨.f64, b⟩]
def nearestF64 (b : BitVec 64) : Clif.Res Clif.Val := Clif.evalFloat .nearest .f64 [⟨.f64, b⟩]

theorem ceil32_half : ceilF32 0x3F000000#32 = .ok ⟨.f32, 0x3F800000#32⟩ := by decide +kernel
theorem ceil32_nhalf : ceilF32 0xBF000000#32 = .ok ⟨.f32, 0x80000000#32⟩ := by decide +kernel
theorem ceil32_onehalf : ceilF32 0x3FC00000#32 = .ok ⟨.f32, 0x40000000#32⟩ := by decide +kernel
theorem ceil32_nonehalf : ceilF32 0xBFC00000#32 = .ok ⟨.f32, 0xBF800000#32⟩ := by decide +kernel
theorem ceil32_zero : ceilF32 0x00000000#32 = .ok ⟨.f32, 0x00000000#32⟩ := by decide +kernel
theorem ceil32_nzero : ceilF32 0x80000000#32 = .ok ⟨.f32, 0x80000000#32⟩ := by decide +kernel
theorem ceil32_pinf : ceilF32 0x7F800000#32 = .ok ⟨.f32, 0x7F800000#32⟩ := by decide +kernel
theorem ceil32_ninf : ceilF32 0xFF800000#32 = .ok ⟨.f32, 0xFF800000#32⟩ := by decide +kernel
theorem ceil32_nan : ceilF32 0x7FC00000#32 = .ok ⟨.f32, 0x7FC00000#32⟩ := by decide +kernel
theorem ceil32_huge : ceilF32 0x5F000000#32 = .ok ⟨.f32, 0x5F000000#32⟩ := by decide +kernel

theorem floor32_half : floorF32 0x3F000000#32 = .ok ⟨.f32, 0x00000000#32⟩ := by decide +kernel
theorem floor32_nhalf : floorF32 0xBF000000#32 = .ok ⟨.f32, 0xBF800000#32⟩ := by decide +kernel
theorem floor32_onehalf : floorF32 0x3FC00000#32 = .ok ⟨.f32, 0x3F800000#32⟩ := by decide +kernel
theorem floor32_nonehalf : floorF32 0xBFC00000#32 = .ok ⟨.f32, 0xC0000000#32⟩ := by decide +kernel
theorem floor32_nzero : floorF32 0x80000000#32 = .ok ⟨.f32, 0x80000000#32⟩ := by decide +kernel
theorem floor32_ninf : floorF32 0xFF800000#32 = .ok ⟨.f32, 0xFF800000#32⟩ := by decide +kernel
theorem floor32_nan : floorF32 0x7FC00000#32 = .ok ⟨.f32, 0x7FC00000#32⟩ := by decide +kernel

theorem trunc32_half : truncF32 0x3F000000#32 = .ok ⟨.f32, 0x00000000#32⟩ := by decide +kernel
theorem trunc32_nhalf : truncF32 0xBF000000#32 = .ok ⟨.f32, 0x80000000#32⟩ := by decide +kernel
theorem trunc32_onehalf : truncF32 0x3FC00000#32 = .ok ⟨.f32, 0x3F800000#32⟩ := by decide +kernel
theorem trunc32_nonehalf : truncF32 0xBFC00000#32 = .ok ⟨.f32, 0xBF800000#32⟩ := by decide +kernel
theorem trunc32_pinf : truncF32 0x7F800000#32 = .ok ⟨.f32, 0x7F800000#32⟩ := by decide +kernel
theorem trunc32_nan : truncF32 0x7FC00000#32 = .ok ⟨.f32, 0x7FC00000#32⟩ := by decide +kernel

theorem nearest32_half : nearestF32 0x3F000000#32 = .ok ⟨.f32, 0x00000000#32⟩ := by decide +kernel
theorem nearest32_nhalf : nearestF32 0xBF000000#32 = .ok ⟨.f32, 0x80000000#32⟩ := by decide +kernel
theorem nearest32_onehalf : nearestF32 0x3FC00000#32 = .ok ⟨.f32, 0x40000000#32⟩ := by
  decide +kernel
theorem nearest32_nonehalf : nearestF32 0xBFC00000#32 = .ok ⟨.f32, 0xC0000000#32⟩ := by
  decide +kernel
theorem nearest32_nan : nearestF32 0x7FC00000#32 = .ok ⟨.f32, 0x7FC00000#32⟩ := by decide +kernel

theorem ceil64_half : ceilF64 0x3FE0000000000000#64 = .ok ⟨.f64, 0x3FF0000000000000#64⟩ := by
  decide +kernel
theorem ceil64_nhalf : ceilF64 0xBFE0000000000000#64 = .ok ⟨.f64, 0x8000000000000000#64⟩ := by
  decide +kernel
theorem ceil64_onehalf : ceilF64 0x3FF8000000000000#64 = .ok ⟨.f64, 0x4000000000000000#64⟩ := by
  decide +kernel
theorem ceil64_nonehalf : ceilF64 0xBFF8000000000000#64 = .ok ⟨.f64, 0xBFF0000000000000#64⟩ := by
  decide +kernel
theorem ceil64_zero : ceilF64 0x0000000000000000#64 = .ok ⟨.f64, 0x0000000000000000#64⟩ := by
  decide +kernel
theorem ceil64_nzero : ceilF64 0x8000000000000000#64 = .ok ⟨.f64, 0x8000000000000000#64⟩ := by
  decide +kernel
theorem ceil64_pinf : ceilF64 0x7FF0000000000000#64 = .ok ⟨.f64, 0x7FF0000000000000#64⟩ := by
  decide +kernel
theorem ceil64_ninf : ceilF64 0xFFF0000000000000#64 = .ok ⟨.f64, 0xFFF0000000000000#64⟩ := by
  decide +kernel
theorem ceil64_nan : ceilF64 0x7FF8000000000000#64 = .ok ⟨.f64, 0x7FF8000000000000#64⟩ := by
  decide +kernel
theorem ceil64_half52 : ceilF64 0x432FFFFFFFFFFFFF#64 = .ok ⟨.f64, 0x4330000000000000#64⟩ := by
  decide +kernel
theorem ceil64_int52 : ceilF64 0x4330000000000001#64 = .ok ⟨.f64, 0x4330000000000001#64⟩ := by
  decide +kernel

theorem floor64_half : floorF64 0x3FE0000000000000#64 = .ok ⟨.f64, 0x0000000000000000#64⟩ := by
  decide +kernel
theorem floor64_nhalf : floorF64 0xBFE0000000000000#64 = .ok ⟨.f64, 0xBFF0000000000000#64⟩ := by
  decide +kernel
theorem floor64_onehalf : floorF64 0x3FF8000000000000#64 = .ok ⟨.f64, 0x3FF0000000000000#64⟩ := by
  decide +kernel
theorem floor64_nonehalf : floorF64 0xBFF8000000000000#64 = .ok ⟨.f64, 0xC000000000000000#64⟩ := by
  decide +kernel
theorem floor64_half52 : floorF64 0x432FFFFFFFFFFFFF#64 =
    .ok ⟨.f64, 0x432FFFFFFFFFFFFE#64⟩ := by decide +kernel
theorem floor64_ninf : floorF64 0xFFF0000000000000#64 = .ok ⟨.f64, 0xFFF0000000000000#64⟩ := by
  decide +kernel
theorem floor64_nan : floorF64 0x7FF8000000000000#64 = .ok ⟨.f64, 0x7FF8000000000000#64⟩ := by
  decide +kernel

theorem trunc64_half : truncF64 0x3FE0000000000000#64 = .ok ⟨.f64, 0x0000000000000000#64⟩ := by
  decide +kernel
theorem trunc64_nhalf : truncF64 0xBFE0000000000000#64 = .ok ⟨.f64, 0x8000000000000000#64⟩ := by
  decide +kernel
theorem trunc64_onehalf : truncF64 0x3FF8000000000000#64 = .ok ⟨.f64, 0x3FF0000000000000#64⟩ := by
  decide +kernel
theorem trunc64_nonehalf : truncF64 0xBFF8000000000000#64 = .ok ⟨.f64, 0xBFF0000000000000#64⟩ := by
  decide +kernel
theorem trunc64_half52 : truncF64 0x432FFFFFFFFFFFFF#64 =
    .ok ⟨.f64, 0x432FFFFFFFFFFFFE#64⟩ := by decide +kernel
theorem trunc64_pinf : truncF64 0x7FF0000000000000#64 = .ok ⟨.f64, 0x7FF0000000000000#64⟩ := by
  decide +kernel
theorem trunc64_nan : truncF64 0x7FF8000000000000#64 = .ok ⟨.f64, 0x7FF8000000000000#64⟩ := by
  decide +kernel

theorem nearest64_half : nearestF64 0x3FE0000000000000#64 = .ok ⟨.f64, 0x0000000000000000#64⟩ := by
  decide +kernel
theorem nearest64_nhalf : nearestF64 0xBFE0000000000000#64 =
    .ok ⟨.f64, 0x8000000000000000#64⟩ := by decide +kernel
theorem nearest64_onehalf : nearestF64 0x3FF8000000000000#64 =
    .ok ⟨.f64, 0x4000000000000000#64⟩ := by decide +kernel
theorem nearest64_nonehalf : nearestF64 0xBFF8000000000000#64 =
    .ok ⟨.f64, 0xC000000000000000#64⟩ := by decide +kernel
theorem nearest64_half52 : nearestF64 0x432FFFFFFFFFFFFF#64 =
    .ok ⟨.f64, 0x4330000000000000#64⟩ := by decide +kernel
theorem nearest64_nan : nearestF64 0x7FF8000000000000#64 = .ok ⟨.f64, 0x7FF8000000000000#64⟩ := by
  decide +kernel
