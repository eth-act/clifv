import FVTest.Opt.MidValFwdWitness
import FV.Opt.Proof.MidValNormFam8

/-! # Family 8, comparisons with an offset, saturating differences, products of constants,
differences of sums: witnesses (#1119, agent MidendNext8)

Family 8 of the mid-end validator's normaliser (`fam8Step`, the first step of `Norm.stdD`,
`FV/Opt/MidVal.lean`; proofs `FV/Opt/Proof/MidValNormFam8.lean`). Each pair below is decided:
accepted by `checkC` now, and rejected with main's normaliser before this change (`normPrev`:
`Norm.stdT`, then family 7; `*_prev_rejects`); look-alikes are rejected (`neg_*`).

* Hand-made: `(x + 1) == 5` against `x == 4` (`cmpOff`, `pos_off`); `(x - 3) >u x` against
  `x <u 3` (`cmpOff`, `pos_ovf`); `(x - y) >u x` against `y >u x` (`cmpSub`, `pos_sat`);
  `(x * 7) * 8` against `x * 56` (`mulMul`, `pos_mul`); `(x + 1) - (y + 1)` against `x - y`
  (`subAdds`, `pos_subs`); a branch on `(x - 1) != 0` against a branch on `x - 1` (`pos_cond`:
  `f`'s condition is now `x != 1`, and `condChain` finds the wrapper `icmp ne _, 0`, which family 8
  normalises to it in `condPrep`'s copy; accepted before this change too).
* Real pairs of the shared #1119 corpus (`FVTest/Opt/midval/real_fam8_*.clif`), rejected by
  `checkCPrev` (main's `checkC` with main's normaliser in its checks) and accepted by
  `checkCertC` with the hints and fold requests `emitC` gives, with the simulation and the
  program refinement (`*_sim`):
  - `sub`: crypto-bigint's test build, core's `Step::backward_overflowing` for a range: `(a - b)
    >u a` against `b >u a` (`cmpSub`);
  - `ovf`: crypto-bigint's test build, itertools' `_RNxC9itertools11HrqDb3h6XjC`: a saturating
    `n - 1`, `(n - 1) >u n` against `n == 0` (`cmpOff`);
  - `off`: crypto-bigint's test build, proptest's `_RNxC8proptest12HbbXoFW9VsCB`: a branch on
    `(a - b) + 1 == c` against `a - b == c - 1` (`cmpOff`);
  - `mul`: crypto-bigint's test build, criterion's `_RNxC9criterion12H7Zzm8JhpBTg`: `((n >> 3) *
    7) * 4` against `(n >> 3) * 28` (`mulMul`).
-/

namespace Opt.MidVal.Fam8Witness
open Clif Pairs NormWitness CondWitness FoldWitness

/-! ## Main's checker (before this change) -/

/-- Main's default normaliser (`Norm.stdT`, then family 7). -/
def normPrev (f : Function) : Norm :=
  Norm.orElse (Norm.stdT f) (Norm.guard (dropStep (atomTy f)))

/-- Main's `checkC` with main's normaliser in its checks: hints, then the prep copies `foldPre`
and `foldPreK` for `foldCands`, then the same two on `fwdPre f` when `check` accepts it against
`f`. -/
def checkCPrev (f g : Function) : Except Reject (List (BlockId × List Wrap)) :=
  match checkC0 f g (normPrev f) with
  | .ok h => .ok h
  | .error e =>
    let bs := match foldCands f g with
      | [] => (f.blocks.head?.map (·.id)).toList
      | bs => bs
    let prep (f' : Function) : Except Reject (List (BlockId × List Wrap)) :=
      if f'.blocks == f.blocks then .error e
      else if f'.blocks.map (·.id) != g.blocks.map (·.id) then .error e
      else match checkC0 f' g (normPrev f') with
        | .ok h => .ok (h ++ bs.map fun b => (b, []))
        | .error e' => .error e'
    if bs.isEmpty then .error e
    else match prep (foldPre f bs) with
      | .ok h => .ok h
      | .error _ =>
        match prep (foldPreK f bs) with
        | .ok h => .ok h
        | .error e' =>
          let f1 := fwdPre f
          if f1.blocks == f.blocks || !(check f f1 (normPrev f)).isOk then .error e'
          else match prep (foldPre f1 bs) with
            | .ok h => .ok h
            | .error _ => match prep (foldPreK f1 bs) with
              | .ok h => .ok h
              | .error _ => .error e'

/-- The verdict of `checkCPrev` on a hand-made pair. -/
def acceptsPrev (f g : String) : Option Bool := do
  pure (checkCPrev (ConstPhi.run (← fn? f)) (← fn? g)).isOk

/-- The verdict of `checkCPrev` on a decoded dump pair. -/
def realPrev (fT gT : String) : Option Bool := do
  let f := ConstPhi.run (← RealWitness.decode fT)
  let g ← RealWitness.decode gT
  pure (checkCPrev f g).isOk

/-! ## Hand-made pairs -/

def offF : String := "function %f(i64) -> i8 {\nblock0(v0: i64):\n    v1 = iconst.i64 1\n    v2 = iadd v0, v1\n    v3 = iconst.i64 5\n    v4 = icmp eq v2, v3\n    return v4\n}"
def offG : String := "function %f(i64) -> i8 {\nblock0(v0: i64):\n    v1 = iconst.i64 4\n    v4 = icmp eq v0, v1\n    return v4\n}"
def offWrongG : String := "function %f(i64) -> i8 {\nblock0(v0: i64):\n    v1 = iconst.i64 5\n    v4 = icmp eq v0, v1\n    return v4\n}"

theorem pos_off : acceptsC offF offG = some true := by native_decide
theorem pos_off_prev_rejects : acceptsPrev offF offG = some false := by native_decide
theorem neg_off : acceptsC offF offWrongG = some false := by native_decide

def ovfF : String := "function %f(i64) -> i8 {\nblock0(v0: i64):\n    v1 = iconst.i64 -3\n    v2 = iadd v0, v1\n    v3 = icmp ugt v2, v0\n    return v3\n}"
def ovfG : String := "function %f(i64) -> i8 {\nblock0(v0: i64):\n    v1 = iconst.i64 3\n    v3 = icmp ult v0, v1\n    return v3\n}"
def ovfWrongG : String := "function %f(i64) -> i8 {\nblock0(v0: i64):\n    v1 = iconst.i64 2\n    v3 = icmp ult v0, v1\n    return v3\n}"

theorem pos_ovf : acceptsC ovfF ovfG = some true := by native_decide
theorem pos_ovf_prev_rejects : acceptsPrev ovfF ovfG = some false := by native_decide
theorem neg_ovf : acceptsC ovfF ovfWrongG = some false := by native_decide

def satF : String := "function %f(i64, i64) -> i8 {\nblock0(v0: i64, v1: i64):\n    v2 = isub v0, v1\n    v3 = icmp ugt v2, v0\n    return v3\n}"
def satG : String := "function %f(i64, i64) -> i8 {\nblock0(v0: i64, v1: i64):\n    v3 = icmp ugt v1, v0\n    return v3\n}"
def satWrongG : String := "function %f(i64, i64) -> i8 {\nblock0(v0: i64, v1: i64):\n    v3 = icmp ugt v0, v1\n    return v3\n}"

theorem pos_sat : acceptsC satF satG = some true := by native_decide
theorem pos_sat_prev_rejects : acceptsPrev satF satG = some false := by native_decide
theorem neg_sat : acceptsC satF satWrongG = some false := by native_decide

def mulF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 7\n    v2 = imul v0, v1\n    v3 = iconst.i64 8\n    v4 = imul v2, v3\n    return v4\n}"
def mulG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 56\n    v4 = imul v0, v1\n    return v4\n}"
def mulWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 48\n    v4 = imul v0, v1\n    return v4\n}"

theorem pos_mul : acceptsC mulF mulG = some true := by native_decide
theorem pos_mul_prev_rejects : acceptsPrev mulF mulG = some false := by native_decide
theorem neg_mul : acceptsC mulF mulWrongG = some false := by native_decide

def subsF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = iconst.i64 1\n    v3 = iadd v0, v2\n    v4 = iadd v1, v2\n    v5 = isub v3, v4\n    return v5\n}"
def subsG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v5 = isub v0, v1\n    return v5\n}"
def subsWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v5 = isub v1, v0\n    return v5\n}"

theorem pos_subs : acceptsC subsF subsG = some true := by native_decide
theorem pos_subs_prev_rejects : acceptsPrev subsF subsG = some false := by native_decide
theorem neg_subs : acceptsC subsF subsWrongG = some false := by native_decide

def condF : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i64 -1\n    v2 = iadd v0, v1\n    v3 = iconst.i64 0\n    v4 = icmp ne v2, v3\n    brif v4, block1, block2\n\nblock1:\n    v5 = iconst.i32 1\n    return v5\n\nblock2:\n    v6 = iconst.i32 0\n    return v6\n}"
def condG : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i64 -1\n    v2 = iadd v0, v1\n    brif v2, block1, block2\n\nblock1:\n    v5 = iconst.i32 1\n    return v5\n\nblock2:\n    v6 = iconst.i32 0\n    return v6\n}"
def condWrongG : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i64 -1\n    v2 = iadd v0, v1\n    brif v2, block2, block1\n\nblock1:\n    v5 = iconst.i32 1\n    return v5\n\nblock2:\n    v6 = iconst.i32 0\n    return v6\n}"

theorem pos_cond : acceptsC condF condG = some true := by native_decide
theorem pos_cond_prev : acceptsPrev condF condG = some true := by native_decide
theorem neg_cond : acceptsC condF condWrongG = some false := by native_decide

/-! ## Real pairs -/

def subF : String := include_str "midval/real_fam8_sub.unopt.clif"
def subG : String := include_str "midval/real_fam8_sub.opt.clif"
def ovfF' : String := include_str "midval/real_fam8_ovf.unopt.clif"
def ovfG' : String := include_str "midval/real_fam8_ovf.opt.clif"
def offF' : String := include_str "midval/real_fam8_off.unopt.clif"
def offG' : String := include_str "midval/real_fam8_off.opt.clif"
def mulF' : String := include_str "midval/real_fam8_mul.unopt.clif"
def mulG' : String := include_str "midval/real_fam8_mul.opt.clif"

/-- An accepted re-check gives the simulation and the program refinement, with or without
hints. -/
theorem simC_of_checked1 {fT gT : String} (h : (checkedC fT gT).map (·.1) = some true) :
    SimRefinesC fT gT := by
  cases hc : checkedC fT gT with
  | none =>
    rw [hc] at h
    cases h
  | some p =>
    obtain ⟨b1, b2⟩ := p
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact simC_of_checked hc

theorem real_sub_prev_rejects : realPrev subF subG = some false := by native_decide
theorem real_sub_checked : (checkedC subF subG).map (·.1) = some true := by native_decide
theorem real_sub_sim : SimRefinesC subF subG := simC_of_checked1 real_sub_checked

theorem real_ovf_prev_rejects : realPrev ovfF' ovfG' = some false := by native_decide
theorem real_ovf_checked : (checkedC ovfF' ovfG').map (·.1) = some true := by native_decide
theorem real_ovf_sim : SimRefinesC ovfF' ovfG' := simC_of_checked1 real_ovf_checked

theorem real_off_prev_rejects : realPrev offF' offG' = some false := by native_decide
theorem real_off_checked : (checkedC offF' offG').map (·.1) = some true := by native_decide
theorem real_off_sim : SimRefinesC offF' offG' := simC_of_checked1 real_off_checked

theorem real_mul_prev_rejects : realPrev mulF' mulG' = some false := by native_decide
theorem real_mul_checked : (checkedC mulF' mulG').map (·.1) = some true := by native_decide
theorem real_mul_sim : SimRefinesC mulF' mulG' := simC_of_checked1 real_mul_checked

end Opt.MidVal.Fam8Witness
