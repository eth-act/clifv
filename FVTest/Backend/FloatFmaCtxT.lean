import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselFloatFma
import FV.Backend.Proof.FmaNegYFreeCtx

/-!
Non-vacuity of the #35 `fma` roots (`IselFloatFma`): the context `buildCtx` makes for a function
with `fma` at `f32` and `f64`, an `fneg` folded into the first operand (`fmadd` rule 2 →
`fmsub`), one into the addend (`rule_lower_609` → `fnmsub`) and both (`fnmsub` rule 2 →
`fnmadd`), passes the Boolean check `ctxOkT` (by `native_decide`, witness only), so
`ctxOkT_sound` gives `CtxInvT` for it; `Compile.fmaNegYFree` holds for it, so
`fmaNegYFree_of_buildCtx` gives `FmaNegYFree`. The ISLE `lower` term fires the roots (ids
693/694, `fmaRootRule`) through the helpers' scalar rules (`fmadd` 699, `fmsub` 701, `fnmsub`
702, `fnmadd` 700), never the vector rules (703, 704), and appends exactly the `FpuRRRR`
`lowerInstOk_fpu3` is about; `lowerRulesCorrectFM_program` then applies to each instruction.
A function whose `fma` has an `fneg` second operand fails `Compile.fmaNegYFree` (the folds of
`fmadd`/`fnmsub` rule 3 are not NaN-sign exact, `FloatFmaWitness`).
`lake build FVTest.Backend.FloatFmaCtxT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

namespace Backend.Proof.FloatFmaCtxT

/-- The `n`-th function of a CLIF text. -/
def fnOfTextF (src : String) (n : Nat := 0) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | fs => match fs[n]? with
    | some p => match p.func with
      | .ok f => f
      | .error _ => default
    | none => default

/-- `buildCtx`'s context and initial lowering state of a function (an empty context if it
fails). -/
def ctxStOfF (f : Clif.Function) : Ctx × LState :=
  match buildCtx f with
  | .ok (ctx, _, st) => (ctx, st)
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] },
      default)

/-- `fma` at `f32` (instruction 3), `fma (fneg x) y z` (5), `fma x y (fneg z)` at `f64` (10),
`fma (fneg x) y (fneg z)` at `f64` (12). -/
def fFma : Clif.Function := fnOfTextF
  "function %fm(i32, i32, i32, i64, i64, i64) -> i64 {\nblock0(v0: i32, v1: i32, v2: i32, v3: i64, v4: i64, v5: i64):\n    v6 = bitcast.f32 v0\n    v7 = bitcast.f32 v1\n    v8 = bitcast.f32 v2\n    v9 = fma v6, v7, v8\n    v10 = fneg v9\n    v11 = fma v10, v7, v8\n    v12 = bitcast.f64 v3\n    v13 = bitcast.f64 v4\n    v14 = bitcast.f64 v5\n    v15 = fneg v14\n    v16 = fma v12, v13, v15\n    v17 = fneg v16\n    v18 = fma v17, v13, v15\n    v19 = bitcast.i64 v18\n    v20 = bitcast.i32 v11\n    v21 = uextend.i64 v20\n    v22 = iadd v19, v21\n    return v22\n}\n"

/-- The lowering of instruction `ii`: the rules that fired and the instructions appended, or
`([], [])`. -/
def lowerRunF (f : Clif.Function) (ii : Nat) : List Isle.RuleId × List MInst :=
  let (ctx, st) := ctxStOfF f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some (.regsVec _), st', tr) => (tr, (st'.emitted.extract st.emitted.size).toList)
  | _ => ([], [])

-- `buildCtx` succeeds and the instructions are the four `fma`s
#guard (buildCtx fFma).toBool
#guard (ctxStOfF fFma).1.insts[3]?.bind (·.clif) == some (.float .fma .f32 [6, 7, 8])
#guard (ctxStOfF fFma).1.insts[5]?.bind (·.clif) == some (.float .fma .f32 [10, 7, 8])
#guard (ctxStOfF fFma).1.insts[10]?.bind (·.clif) == some (.float .fma .f64 [12, 13, 15])
#guard (ctxStOfF fFma).1.insts[12]?.bind (·.clif) == some (.float .fma .f64 [17, 13, 15])
-- the scope check passes (no `fneg` second operand)
#guard Compile.fmaNegYFree fFma
-- `lower` fires the roots through the scalar helper rules: `fmadd` rule 0 (MAdd), rule 2 →
-- `fmsub` rule 0 (MSub), `rule_lower_609` → `fnmsub` rule 0 (NMSub), and `fnmsub` rule 2 →
-- `fnmadd` (NMAdd); never the vector rules 703/704
#guard fmaRootRule rule_lower_608 && fmaRootRule rule_lower_609
#guard (lowerRunF fFma 3).1.contains 693 && (lowerRunF fFma 3).1.contains 699
#guard (lowerRunF fFma 5).1.contains 693 && (lowerRunF fFma 5).1.contains 695 &&
  (lowerRunF fFma 5).1.contains 701
#guard (lowerRunF fFma 10).1.contains 694 && (lowerRunF fFma 10).1.contains 702
#guard (lowerRunF fFma 12).1.contains 694 && (lowerRunF fFma 12).1.contains 697 &&
  (lowerRunF fFma 12).1.contains 700
#guard [3, 5, 10, 12].all fun ii =>
  !((lowerRunF fFma ii).1.contains 703 || (lowerRunF fFma ii).1.contains 704)
-- the appended code is one `FpuRRRR` into the first fresh vreg, the `fneg`s' operands in
-- place of the negated CLIF operands
#guard (lowerRunF fFma 3).2 == let n := (ctxStOfF fFma).2.nextVreg
  [.fpuRRRR .mAdd .size32 (.vreg n .float) (.vreg 6 .float) (.vreg 7 .float) (.vreg 8 .float)]
#guard (lowerRunF fFma 5).2 == let n := (ctxStOfF fFma).2.nextVreg
  [.fpuRRRR .mSub .size32 (.vreg n .float) (.vreg 9 .float) (.vreg 7 .float) (.vreg 8 .float)]
#guard (lowerRunF fFma 10).2 == let n := (ctxStOfF fFma).2.nextVreg
  [.fpuRRRR .nMSub .size64 (.vreg n .float) (.vreg 12 .float) (.vreg 13 .float)
    (.vreg 14 .float)]
#guard (lowerRunF fFma 12).2 == let n := (ctxStOfF fFma).2.nextVreg
  [.fpuRRRR .nMAdd .size64 (.vreg n .float) (.vreg 16 .float) (.vreg 13 .float)
    (.vreg 14 .float)]

/-- **`CtxInvT` holds for the `fma` context.** -/
theorem ctxInvT_float_fma : CtxInvT fFma (ctxStOfF fFma).1 :=
  ctxOkT_sound (by native_decide)

/-- **`FmaNegYFree` holds for it** (`Compile.fmaNegYFree`, `fmaNegYFree_of_buildCtx`). -/
theorem fmaNegYFree_float_fma : FmaNegYFree (ctxStOfF fFma).1 := by
  have hinv := ctxInvT_float_fma
  have hok : (buildCtx fFma).toBool = true := by native_decide
  revert hinv
  unfold ctxStOfF
  split
  next ctx _ _ hb =>
    intro hinv
    exact fmaNegYFree_of_buildCtx (by native_decide) hb hinv
  next _ hb =>
    intro _
    rw [hb] at hok
    cases hok

/-- **The roots of `LowerRulesCorrectFM` apply to this context**: its `fma`s lie in a `CtxInvT`
context with `FmaNegYFree`, and `rule_lower_608`/`rule_lower_609` are the `fmaRootRule`s of
`lower`, so `lowerRulesCorrectFM_program` gives `LowerRuleOkTC FmaNegYFree` for both. -/
theorem float_fma_roots_apply {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR) :
    CtxInvT fFma (ctxStOfF fFma).1 ∧ FmaNegYFree (ctxStOfF fFma).1 ∧
      ((ctxStOfF fFma).1.insts[3]?.bind (·.clif)) = some (.float .fma .f32 [6, 7, 8]) ∧
      LowerRuleOkTC FmaNegYFree isem MR env cp program rule_lower_608 ∧
      LowerRuleOkTC FmaNegYFree isem MR env cp program rule_lower_609 :=
  ⟨ctxInvT_float_fma, fmaNegYFree_float_fma, by native_decide,
    lowerRulesCorrectFM_program F isem MR env cp hR hMR rule_lower_608
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel) rfl,
    lowerRulesCorrectFM_program F isem MR env cp hR hMR rule_lower_609
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel) rfl⟩

/-- An `fma` whose second operand is an `fneg` is rejected by the scope check. -/
def fFmaNegY : Clif.Function := fnOfTextF
  "function %fy(f32, f32, f32) -> f32 {\nblock0(v0: f32, v1: f32, v2: f32):\n    v3 = fneg v1\n    v4 = fma v0, v3, v2\n    return v4\n}\n"

#guard (buildCtx fFmaNegY).toBool
#guard !Compile.fmaNegYFree fFmaNegY

theorem fmaNegY_rejected : Compile.fmaNegYFree fFmaNegY = false := by native_decide

/-! ## The semantics lemma on concrete values -/

/-- `fma_holds32` on `fmsub` (an `fneg` folded into the first operand) with a quiet NaN: the
emitted `fmsub` of the `fneg`'s operand `qNaN` holds CLIF's `fma (fneg qNaN) 1.0 +0`. -/
theorem fma_holds_fmsub_nan :
    ∃ w, fpu3Out .mSub .size32 (0xDEADBEEFCAFEF00D12345678#96 ++ 0x7FC00001#32)
      (0#96 ++ 0x3F800000#32) (0xFFFFFFFFFFFFFFFFFFFFFFFF#96 ++ 0x00000000#32) = some w ∧
      VHolds ⟨.f32, IEEE.mulAdd .b32 .rne 0x00000000#32 (IEEE.neg .b32 0x7FC00001#32)
        0x3F800000#32⟩ w :=
  fma_holds32 (o := .mSub) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Backend.Proof.FloatFmaCtxT
