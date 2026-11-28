import FVTest.Opt.MidValFam9Witness
import FV.Opt.Proof.MidValNormFam10

/-! # Family 10, pairs of constants, doubled sums, zero offsets: witnesses (#1119, agent
MidendNext12)

Family 10 of the mid-end validator's normaliser (`fam10Step`, the third step of `Norm.stdD`,
`FV/Opt/MidVal.lean`; proofs `FV/Opt/Proof/MidValNormFam10.lean`). Each pair below is decided:
accepted by `checkC` now, and rejected with main's normaliser before this change (`normPrev`:
families 8 and 9, then `Norm.stdT`, then family 7; `*_prev_rejects`); look-alikes are rejected
(`neg_*`).

* Hand-made: `(x & 1) & (y & 1)` against `(x & y) & 1` (`pairRe`, `pos_band`; look-alike: the
  mask `3`); `(x + 16) + (y + 16)` against `(x + y) + 32` (`pairRe`, `pos_add`; look-alike: `31`);
  `(x + 5) + (y + -5)` against `x + y` (`pairRe`, the neutral sum of the constants, `pos_addZero`);
  `(x + 16) * 2` against `(x + x) + 32` (`dblRe`, `pos_dbl`; look-alike: `16`); `(x + 8) - 8`
  against `x` (`affZero`, `pos_aff`; look-alike: `(x + 8) - 7`).
* Real pairs of the shared #1119 corpus (`FVTest/Opt/midval/real_fam10_*.clif`), rejected by
  `checkCPrev` (main's `checkC` with main's normaliser in its checks) and accepted by
  `checkCertC` with the hints and fold requests `emitC` gives, with the simulation and the
  program refinement (`*_sim`); all from crypto-bigint's test build:
  - `pair`: clap_builder's `_RNxC12clap_builder12HcZ8SGvwWGJa`: a chain of `(a & 1) & (b & 1)`
    against `((a & b) & …) & 1` (`pairRe`);
  - `dbl`: regex_syntax's `_RNxC12regex_syntax12HgorpCe7HbSY`: `(x + -1) * 2` against
    `(x + x) + -2` (`dblRe`);
  - `aff`: proptest's `_RNxC8proptest12HethdGkKfETy`: `(x + k) - k` against `x` (`affZero`);
  - `sym`: crypto_bigint's `_RNxC13crypto_bigint12H4bFv6PVKeWU`: `symbol_value + 0 * 8` against
    the `symbol_value` (`idNode`).
-/

namespace Opt.MidVal.Fam10Witness
open Clif Pairs NormWitness CondWitness FoldWitness

/-! ## Main's checker (before this change) -/

/-- Main's default normaliser (families 8 and 9, `Norm.stdT`, then family 7). -/
def normPrev (f : Function) : Norm :=
  Norm.orElse (Norm.guard fam8Step)
    (Norm.orElse (Norm.guard (fam9Step (atomTy f)))
      (Norm.orElse (Norm.stdT f) (Norm.guard (dropStep (atomTy f)))))

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

def bandF : String := "function %f(i8, i8) -> i8 {\nblock0(v0: i8, v1: i8):\n    v2 = iconst.i8 1\n    v3 = band v0, v2\n    v4 = band v1, v2\n    v5 = band v3, v4\n    return v5\n}"
def bandG : String := "function %f(i8, i8) -> i8 {\nblock0(v0: i8, v1: i8):\n    v2 = iconst.i8 1\n    v3 = band v0, v1\n    v5 = band v3, v2\n    return v5\n}"
def bandWrongG : String := "function %f(i8, i8) -> i8 {\nblock0(v0: i8, v1: i8):\n    v2 = iconst.i8 3\n    v3 = band v0, v1\n    v5 = band v3, v2\n    return v5\n}"

theorem pos_band : acceptsC bandF bandG = some true := by native_decide
theorem pos_band_prev_rejects : acceptsPrev bandF bandG = some false := by native_decide
theorem neg_band : acceptsC bandF bandWrongG = some false := by native_decide

def addF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = iconst.i64 16\n    v3 = iadd v0, v2\n    v4 = iadd v1, v2\n    v5 = iadd v3, v4\n    return v5\n}"
def addG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = iconst.i64 32\n    v3 = iadd v0, v1\n    v5 = iadd v3, v2\n    return v5\n}"
def addWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = iconst.i64 31\n    v3 = iadd v0, v1\n    v5 = iadd v3, v2\n    return v5\n}"

theorem pos_add : acceptsC addF addG = some true := by native_decide
theorem pos_add_prev_rejects : acceptsPrev addF addG = some false := by native_decide
theorem neg_add : acceptsC addF addWrongG = some false := by native_decide

def addZeroF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = iconst.i64 5\n    v3 = iadd v0, v2\n    v4 = iconst.i64 -5\n    v5 = iadd v1, v4\n    v6 = iadd v3, v5\n    return v6\n}"
def addZeroG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v6 = iadd v0, v1\n    return v6\n}"

theorem pos_addZero : acceptsC addZeroF addZeroG = some true := by native_decide
theorem pos_addZero_prev_rejects : acceptsPrev addZeroF addZeroG = some false := by native_decide

def dblF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 16\n    v2 = iadd v0, v1\n    v3 = iconst.i64 2\n    v4 = imul v3, v2\n    return v4\n}"
def dblG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iadd v0, v0\n    v2 = iconst.i64 32\n    v4 = iadd v1, v2\n    return v4\n}"
def dblWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iadd v0, v0\n    v2 = iconst.i64 16\n    v4 = iadd v1, v2\n    return v4\n}"

theorem pos_dbl : acceptsC dblF dblG = some true := by native_decide
theorem pos_dbl_prev_rejects : acceptsPrev dblF dblG = some false := by native_decide
theorem neg_dbl : acceptsC dblF dblWrongG = some false := by native_decide

def affF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 8\n    v2 = iadd v0, v1\n    v3 = isub v2, v1\n    return v3\n}"
def affG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}"
def affWrongF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 8\n    v2 = iadd v0, v1\n    v4 = iconst.i64 7\n    v3 = isub v2, v4\n    return v3\n}"

theorem pos_aff : acceptsC affF affG = some true := by native_decide
theorem pos_aff_prev_rejects : acceptsPrev affF affG = some false := by native_decide
theorem neg_aff : acceptsC affWrongF affG = some false := by native_decide

/-! ## Real pairs -/

def pairF : String := include_str "midval/real_fam10_pair.unopt.clif"
def pairG : String := include_str "midval/real_fam10_pair.opt.clif"
def dblF' : String := include_str "midval/real_fam10_dbl.unopt.clif"
def dblG' : String := include_str "midval/real_fam10_dbl.opt.clif"
def affF' : String := include_str "midval/real_fam10_aff.unopt.clif"
def affG' : String := include_str "midval/real_fam10_aff.opt.clif"
def symF : String := include_str "midval/real_fam10_sym.unopt.clif"
def symG : String := include_str "midval/real_fam10_sym.opt.clif"

theorem real_pair_prev_rejects : realPrev pairF pairG = some false := by native_decide
theorem real_pair_checked : (checkedC pairF pairG).map (·.1) = some true := by native_decide
theorem real_pair_sim : SimRefinesC pairF pairG := Fam8Witness.simC_of_checked1 real_pair_checked

theorem real_dbl_prev_rejects : realPrev dblF' dblG' = some false := by native_decide
theorem real_dbl_checked : (checkedC dblF' dblG').map (·.1) = some true := by native_decide
theorem real_dbl_sim : SimRefinesC dblF' dblG' := Fam8Witness.simC_of_checked1 real_dbl_checked

theorem real_sym_prev_rejects : realPrev symF symG = some false := by native_decide
theorem real_sym_checked : (checkedC symF symG).map (·.1) = some true := by native_decide
theorem real_sym_sim : SimRefinesC symF symG := Fam8Witness.simC_of_checked1 real_sym_checked

theorem real_aff_prev_rejects : realPrev affF' affG' = some false := by native_decide
theorem real_aff_checked : (checkedC affF' affG').map (·.1) = some true := by native_decide
theorem real_aff_sim : SimRefinesC affF' affG' := Fam8Witness.simC_of_checked1 real_aff_checked

end Opt.MidVal.Fam10Witness
