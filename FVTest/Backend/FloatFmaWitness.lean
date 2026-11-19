import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselCmpCond
import FV.Backend.Proof.IselFmaFamily

/-!
# #35 `fma`: witnesses

1. **Statements restated** because `instData` (and its name mirror `fFmt`/`fOpc`) now builds
   `Ternary`/`Fma` for an `fma.f32/f64`: their old forms (main's text) are false.
2. **The `fneg` fold on `fma`'s second operand is not exact** (why `Compile.fmaNegYFree` keeps
   such functions out of the verified scope): Cranelift's `fmadd` rule 3
   (`lower.isle:633`, `fma x (fneg y0) z` → `fmsub x y0 z`) computes `FPMulAdd(z, −x, y0)` where
   CLIF computes `FPMulAdd(z, x, −y0)`; with a quiet NaN `x` (and no other NaN), both return that
   NaN quietened, but the Arm instruction negated it first. Same for `fnmsub` rule 3
   (`lower.isle:635`, → `fnmadd`).
-/

namespace Backend.Proof.FloatFmaWitness

open Backend Backend.Proof Backend.Proof.Driver

/-! ## 1. Old forms false -/

/-- The old `fFmt_mem` (without `"Ternary"`) is false: `fFmt .fma = "Ternary"`. -/
theorem fFmt_mem_old_false :
    ¬ ∀ op : Clif.FOp, fFmt op ∈ ["Binary", "Unary", "FloatCompare", ""] := fun h => by
  have := h .fma
  simp [fFmt] at this

/-- The old `fFmt_eq_false` is false at `op = .fma`, `s = "Ternary"`. -/
theorem fFmt_eq_false_old_false :
    ¬ ∀ {op : Clif.FOp} {s : String}, s ∉ ["Binary", "Unary", "FloatCompare", ""] →
      (fFmt op = s ↔ False) := fun h =>
  (@h .fma "Ternary" (by decide)).mp rfl

/-- The old `eq_fFmt_false` is false at `op = .fma`, `s = "Ternary"`. -/
theorem eq_fFmt_false_old_false :
    ¬ ∀ {op : Clif.FOp} {s : String}, s ∉ ["Binary", "Unary", "FloatCompare", ""] →
      (s = fFmt op ↔ False) := fun h =>
  (@h .fma "Ternary" (by decide)).mp rfl

/-- The old `instNames_snd_memT` (with `fOpNames`) is false: an `fma` is named `"Fma"`. -/
theorem instNames_snd_memT_old_false :
    ¬ ∀ cl : Clif.Inst, (instNames cl).2 ∈ eOpNames ++ ["Bitcast"] ++ fOpNames := fun h => by
  have := h (.float .fma .f32 [0, 1, 2])
  revert this
  decide

/-- The first function of a CLIF text. -/
def fnOfText (src : String) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => f
    | .error _ => default
  | [] => default

/-- `buildCtx`'s context of a function (an empty context if it fails). -/
def ctxOf (f : Clif.Function) : Ctx :=
  match buildCtx f with
  | .ok (ctx, _, _) => ctx
  | .error _ => { func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] }

/-- A function whose `v4` is an `fma` and is used by an `fadd`. -/
def fFmaUse : Clif.Function := fnOfText
  "function %u(f32, f32, f32) -> f32 {\nblock0(v0: f32, v1: f32, v2: f32):\n    v3 = fma v0, v1, v2\n    v4 = fadd v3, v0\n    return v4\n}\n"

#guard (buildCtx fFmaUse).toBool
#guard (ctxOf fFmaUse).insts[0]?.bind (·.clif) == some (.float .fma .f32 [0, 1, 2])
#guard (ctxOf fFmaUse).defInst? 3 == some 0

theorem ctxInvT_fmaUse : CtxInvT fFmaUse (ctxOf fFmaUse) :=
  ctxOkT_sound (by native_decide)

set_option maxRecDepth 20000 in
/-- The old `opcode_absurdT` (`hns` over `fOpNames`) is false: `v3` of `fFmaUse` is defined by an
`fma` (`Ternary`/`Fma`, a name outside `eOpNames ++ ["Bitcast"] ++ fOpNames`). -/
theorem opcode_absurdT_old_false :
    ¬ ∀ {f : Clif.Function} {ctx : Ctx} (_hctx : CtxInvT f ctx) {x j : Nat} {info : IInfo}
      (_hd : ctx.defInst? x = some j) (_hi : ctx.insts[j]? = some info) {kf ko : Nat}
      {fs : List V} (_he : V.data 152 kf (V.data 151 ko [] :: fs) = info.data) {s : String}
      (_hs : (variantNames 151)[ko]? = some s) (_hns : s ∉ eOpNames ++ ["Bitcast"] ++ fOpNames)
      (_hk : (kf ≠ 33 ∧ kf ≠ 34) ∨ (ko ≠ 59 ∧ ko ≠ 60)), False := fun h => by
  obtain ⟨info, hi⟩ : ∃ info, (ctxOf fFmaUse).insts[0]? = some info :=
    Option.isSome_iff_exists.mp (by native_decide)
  have hcl : info.clif = some (.float .fma .f32 [0, 1, 2]) := by
    have : ((ctxOf fFmaUse).insts[0]?.bind (·.clif)) = some (.float .fma .f32 [0, 1, 2]) := by
      native_decide
    rw [hi] at this
    exact this
  have hd := ctxInvT_fmaUse.data 0 info _ hi hcl
  have e : instData fFmaUse (.float .fma .f32 [0, 1, 2]) =
      .ok (.data 152 24 [.data 151 118 [], .values [0, 1, 2]]) := rfl
  rw [e] at hd
  exact h ctxInvT_fmaUse (x := 3) (j := 0) (by native_decide) hi (Except.ok.inj hd) (s := "Fma")
    rfl (by decide) (.inl (by decide))

/-! ## 2. The `fneg` fold on the second operand: the NaN sign differs -/

/-- A positive quiet NaN, `1.0`, `+0.0` (`f32`). -/
def qnan32 : BitVec 32 := 0x7FC00000#32
def one32 : BitVec 32 := 0x3F800000#32
def zero32 : BitVec 32 := 0x00000000#32

/-- CLIF: `fma qNaN (fneg 1.0) +0` is the positive quiet NaN (`FPProcessNaNs`: the first NaN
operand of `addend, op1, op2` is `x`). -/
theorem clif_fma_negY_nan :
    Clif.FSem.fma .b32 qnan32 (IEEE.neg .b32 one32) zero32 = 0x7FC00000#32 := by
  decide +kernel

/-- Arm: `fmsub` of `qNaN, 1.0, +0` (what `fmadd` rule 3 emits for that `fma`) negates `x`
first: the negative quiet NaN. -/
theorem arm_fmsub_nan : fpu3Val .mSub .b32 qnan32 one32 zero32 = 0xFFC00000#32 := by
  decide +kernel

/-- **`fmadd` rule 3 is not exact**: on these operands the emitted `fmsub` and CLIF's `fma`
differ (in the NaN's sign). -/
theorem fmsub_negY_nan_differs :
    fpu3Val .mSub .b32 qnan32 one32 zero32 ≠
      Clif.FSem.fma .b32 qnan32 (IEEE.neg .b32 one32) zero32 := by
  rw [arm_fmsub_nan, clif_fma_negY_nan]; decide

/-- **`fnmsub` rule 3 is not exact either**: `fma qNaN (fneg 1.0) (fneg +0)` lowers to
`fnmadd qNaN, 1.0, +0` = `FPMulAdd(−0, −qNaN, 1.0)`, CLIF computes `FPMulAdd(−0, qNaN, −1.0)`. -/
theorem fnmadd_negY_nan_differs :
    fpu3Val .nMAdd .b32 qnan32 one32 zero32 ≠
      Clif.FSem.fma .b32 qnan32 (IEEE.neg .b32 one32) (IEEE.neg .b32 zero32) := by
  decide +kernel

/-- The exact folds keep the NaN's sign: `fmadd` rule 2 (`fneg` on `x`: `fmsub x0 y z`). -/
theorem fmsub_negX_nan_same :
    fpu3Val .mSub .b32 qnan32 one32 zero32 =
      Clif.FSem.fma .b32 (IEEE.neg .b32 qnan32) one32 zero32 := by
  decide +kernel

end Backend.Proof.FloatFmaWitness
