import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselExclT
import FV.Backend.Proof.IselFloatCmp

/-!
Non-vacuity of S11f's target `LowerRulesCorrectFC` (#35): the context `buildCtx` makes for a
function with all twelve `fcmp` conditions at `f32` (and `eq`/`ult` at `f64`), one under
`uextend.i32`, passes the Boolean check `ctxOkT` (by `native_decide`, witness only), so
`ctxOkT_sound` gives `CtxInvT` for it, and the ISLE `lower` term fires the two roots of
`floatCmpRootRule` (`lowerRulesCorrectFC_program`) on its instructions. The `; run:` oracle is
`FVTest/Backend/float_cmp.clif`.
`lake build FVTest.Backend.FloatCmpCtxT`.
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

def fCmp : Clif.Function := fnOfTextC
  "function %c(f32, f32, f64, f64) -> i32 {\nblock0(v0: f32, v1: f32, v2: f64, v3: f64):\n    v4 = fcmp eq v0, v1\n    v5 = fcmp ne v0, v1\n    v6 = fcmp lt v0, v1\n    v7 = fcmp le v0, v1\n    v8 = fcmp gt v0, v1\n    v9 = fcmp ge v0, v1\n    v10 = fcmp ord v0, v1\n    v11 = fcmp uno v0, v1\n    v12 = fcmp ugt v0, v1\n    v13 = fcmp uge v0, v1\n    v14 = fcmp ult v0, v1\n    v15 = fcmp ule v0, v1\n    v16 = uextend.i32 v4\n    v17 = fcmp eq v2, v3\n    v18 = uextend.i32 v17\n    return v16\n}\n"

/-- The lowering trace of instruction `ii` (the ids of the rules that fired), or `[]`. -/
def lowerTraceC (f : Clif.Function) (ii : Nat) : List Isle.RuleId :=
  let (ctx, st) := ctxStOfC f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some (.regsVec _), _, tr) => tr
  | _ => []

-- `buildCtx` succeeds and the instructions are the comparisons
#guard (buildCtx fCmp).toBool
#guard (ctxStOfC fCmp).1.insts[0]?.bind (·.clif) == some (.float (.fcmp .eq) .f32 [0, 1])
#guard (ctxStOfC fCmp).1.insts[11]?.bind (·.clif) == some (.float (.fcmp .ule) .f32 [0, 1])
#guard (ctxStOfC fCmp).1.insts[12]?.bind (·.clif) == some (.extend .uextend .i32 4)
#guard (ctxStOfC fCmp).1.insts[13]?.bind (·.clif) == some (.float (.fcmp .eq) .f64 [2, 3])
-- the comparison results have integer vregs
#guard (ctxStOfC fCmp).1.valueReg? 4 == some (.vreg 4 .int)
-- `lower` fires the two fcmp roots (`floatCmpRootRule`): 951 (`rule_lower_2176`) on the plain
-- `fcmp`s, 812 (`rule_lower_1283`) on the `uextend`s
#guard [rule_lower_2176, rule_lower_1283].all floatCmpRootRule
#guard (lowerTraceC fCmp 0).contains 951 && (lowerTraceC fCmp 11).contains 951 &&
  (lowerTraceC fCmp 12).contains 812 && (lowerTraceC fCmp 14).contains 812

/-- **`CtxInvT` holds for the float comparison context.** -/
theorem ctxInvT_float_cmp : CtxInvT fCmp (ctxStOfC fCmp).1 :=
  ctxOkT_sound (by native_decide)

/-- **The roots of `LowerRulesCorrectFC` apply to this context**: its `fcmp.eq.f32`
(instruction 0) lies in a `CtxInvT` context and rule 951 (`rule_lower_2176`) is a
`floatCmpRootRule` of `lower`, so `lowerRulesCorrectFC_program` gives `LowerRuleOkT` for the
rule on it. -/
theorem float_cmp_root_applies :
    CtxInvT fCmp (ctxStOfC fCmp).1 ∧
      ((ctxStOfC fCmp).1.insts[0]?.bind (·.clif)) = some (.float (.fcmp .eq) .f32 [0, 1]) ∧
      rule_lower_2176 ∈ program.rulesOf TId.lower ∧ floatCmpRootRule rule_lower_2176 = true :=
  ⟨ctxInvT_float_cmp, by native_decide,
    by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel, rfl⟩

/-- **NaN witnesses for the twelve `fcmp` conditions** (`Clif.FSem.fcmp` of a quiet NaN against
`1.0`, compare class `un`; the `; run:` lines of `float_cmp.clif` exercise the same table
through the backend). -/
theorem fcmp_nan_witnesses :
    [Clif.FloatCC.eq, .lt, .le, .gt, .ge, .ord].all
        (fun cc => Clif.FSem.fcmp cc .f32 0x7fc00000#32 0x3f800000#32 = some false) ∧
      [Clif.FloatCC.ne, .uno, .ugt, .uge, .ult, .ule].all
        (fun cc => Clif.FSem.fcmp cc .f32 0x7fc00000#32 0x3f800000#32 = some true) := by
  refine ⟨by native_decide, by native_decide⟩
