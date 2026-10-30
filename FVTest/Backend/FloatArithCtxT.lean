import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselExclT
import FV.Backend.Proof.IselFloatCmp

/-!
Non-vacuity of S11f's target `LowerRulesCorrectFT` (#239): the context `buildCtx` makes for a
function with every scalar float arithmetic operation of the closure (`fadd fsub fmul fdiv fmin
fmax sqrt fneg fabs` at `f32`, `fpromote.f64`, `fadd` at `f64`, `fdemote.f32`) passes the Boolean
check `ctxOkT` (by `native_decide`, witness only), so `ctxOkT_sound` gives `CtxInvT` for it, and
the ISLE `lower` term fires each of the eleven roots of `floatArithRootRule`
(`lowerRulesCorrectFT_program`) on its instructions. Its instructions are in the arithmetic
scope `InstScopeTA` (not in `InstScopeT`), so `lower_nonroot_nomatchTA` excludes the roots
outside the closure on them; the `fcmp` root `rule_lower_2176` is S11f's
(`LowerRulesCorrectFC`, witness `FloatCmpCtxT.lean`).
`lake build FVTest.Backend.FloatArithCtxT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

/-- The first function of a CLIF text. -/
def fnOfTextA (src : String) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => f
    | .error _ => default
  | [] => default

/-- `buildCtx`'s context and initial lowering state of a function (an empty context if it fails). -/
def ctxStOfA (f : Clif.Function) : Ctx × LState :=
  match buildCtx f with
  | .ok (ctx, _, st) => (ctx, st)
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] },
      default)

def fArith : Clif.Function := fnOfTextA
  "function %a(f32, f32, f64) -> f32 {\nblock0(v0: f32, v1: f32, v2: f64):\n    v3 = fadd v0, v1\n    v4 = fsub v3, v1\n    v5 = fmul v4, v0\n    v6 = fdiv v5, v1\n    v7 = fmin v6, v0\n    v8 = fmax v7, v1\n    v9 = sqrt v8\n    v10 = fneg v9\n    v11 = fabs v10\n    v12 = fpromote.f64 v11\n    v13 = fadd v12, v2\n    v14 = fdemote.f32 v13\n    return v14\n}\n"

/-- The lowering trace of instruction `ii` (the ids of the rules that fired), or `[]`. -/
def lowerTraceA (f : Clif.Function) (ii : Nat) : List Isle.RuleId :=
  let (ctx, st) := ctxStOfA f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some (.regsVec _), _, tr) => tr
  | _ => []

-- `buildCtx` succeeds and the instructions are the float operations
#guard (buildCtx fArith).toBool
#guard (ctxStOfA fArith).1.insts[0]?.bind (·.clif) == some (.float .fadd .f32 [0, 1])
#guard (ctxStOfA fArith).1.insts[9]?.bind (·.clif) == some (.float .fpromote .f64 [11])
#guard (ctxStOfA fArith).1.insts[11]?.bind (·.clif) == some (.float .fdemote .f32 [13])
-- the float values have float vregs
#guard (ctxStOfA fArith).1.valueReg? 3 == some (.vreg 3 .float)
#guard (ctxStOfA fArith).1.valueReg? 12 == some (.vreg 12 .float)
-- `lower` fires the eleven arithmetic roots (`floatArithRootRule`) on them
#guard [rule_lower_485, rule_lower_493, rule_lower_501, rule_lower_509, rule_lower_517,
  rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554,
  rule_lower_559].all floatArithRootRule
#guard (lowerTraceA fArith 0).contains 662 && (lowerTraceA fArith 1).contains 664 &&
  (lowerTraceA fArith 2).contains 666 && (lowerTraceA fArith 3).contains 668 &&
  (lowerTraceA fArith 4).contains 670 && (lowerTraceA fArith 5).contains 672 &&
  (lowerTraceA fArith 6).contains 674 && (lowerTraceA fArith 7).contains 676 &&
  (lowerTraceA fArith 8).contains 678 && (lowerTraceA fArith 9).contains 679 &&
  (lowerTraceA fArith 10).contains 662 && (lowerTraceA fArith 11).contains 680

/-- **`CtxInvT` holds for the float arithmetic context.** -/
theorem ctxInvT_float_arith : CtxInvT fArith (ctxStOfA fArith).1 :=
  ctxOkT_sound (by native_decide)

/-- **The roots of `LowerRulesCorrectFT` apply to this context**: its `fadd.f32` (instruction 0)
lies in a `CtxInvT` context and rule 662 (`rule_lower_485`) is a `floatArithRootRule` of `lower`,
so `lowerRulesCorrectFT_program` gives `LowerRuleOkT` for the rule on it. -/
theorem float_arith_root_applies :
    CtxInvT fArith (ctxStOfA fArith).1 ∧
      ((ctxStOfA fArith).1.insts[0]?.bind (·.clif)) = some (.float .fadd .f32 [0, 1]) ∧
      rule_lower_485 ∈ program.rulesOf TId.lower ∧ floatArithRootRule rule_lower_485 = true :=
  ⟨ctxInvT_float_arith, by native_decide,
    by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel, rfl⟩

-- the check rejects the context with an `f32` value re-typed as an integer
#guard !ctxOkT fArith { (ctxStOfA fArith).1 with valTy := (ctxStOfA fArith).1.valTy.set! 3 (some (.int 32)) }

/-- **The float arithmetic context is in the arithmetic scope `InstScopeTA`.** -/
theorem instScopeTA_float_arith : InstScopeTA (ctxStOfA fArith).1 := by
  have h : ((ctxStOfA fArith).1.insts.toList.all fun info =>
      match info.clif with
      | some c => Compile.instETA c
      | none => true) = true := by native_decide
  intro ii info inst hi hc
  have hm := List.all_eq_true.mp h info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
  rw [hc] at hm
  exact hm

-- the typed scope without the arithmetic does not admit it
#guard !Compile.instET (.float .fadd .f32 [0, 1]) && Compile.instETA (.float .fadd .f32 [0, 1])
#guard !Compile.instETA (.float (.fcmp .eq) .f32 [0, 1])

/-- **The deferred `fcmp` root is now a proven closure root (S11f)**: `rule_lower_2176` is in
`closureRootIds`, is a `floatCmpRootRule` (proven over float-capable contexts by
`lowerRulesCorrectFC_program`, see `FloatCmpCtxT.lean`), and is not a `floatArithRootRule`, so
the arithmetic dispatch excludes it via `hfa`. -/
theorem float_cmp_root_closure :
    closureRootIds.contains rule_lower_2176.id = true ∧ floatCmpRootRule rule_lower_2176 = true ∧
      floatArithRootRule rule_lower_2176 = false :=
  ⟨by native_decide, by native_decide, by native_decide⟩
