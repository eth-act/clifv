import FVTest.Opt.MidValFam8Witness
import FV.Opt.Proof.MidValNormFam9

/-! # Family 9, masks, narrowed shifts, complements, extensions, comparisons of extensions and
of `<=>`, `select` as min/max, multiply-high: witnesses (#1119, agents MidendNext10/11)

Family 9 of the mid-end validator's normaliser (`fam9Step`, the second step of `Norm.stdD`,
`FV/Opt/MidVal.lean`; proofs `FV/Opt/Proof/MidValNormFam9.lean`). Each pair below is decided:
accepted by `checkC` now, and rejected with main's normaliser before this change (`normPrev`:
family 8, then `Norm.stdT`, then family 7; `*_prev_rejects`); look-alikes are rejected (`neg_*`).
`Norm.stdT` here already has `borMask` on the node `narrowStep` builds; no pair below narrows.

* Hand-made: `(x & 63) | -64` against `x | -64` (`borMask`, `pos_mask`; look-alike: the mask
  `62`); `((x & -16) | 3) | 12` against `x | 15` (`borMaskRe`, `pos_maskRe`); `~(x + -1)`
  against `-x` and `~(~x + y)` against `x - y` (`notDec`, `pos_dec`, `pos_notAdd`); `ireduce.i32
  ((uextend.i64 x) << 7)` against `x << 7` (`redShl`, `pos_shl`; look-alike: the amount `33`);
  `ireduce.i32 (-(sextend.i64 x))` against `-x` (`redUn`, `pos_un`); `uextend.i64 (uextend.i32
  x)` against `uextend.i64 x` (`extExt`, `pos_ext`; look-alike: `uextend` of `sextend`);
  `(uextend.i64 x) <s 0` against `0` and `(sextend.i64 x) >s 0` against `x >s 0` (`extCmp`,
  `pos_cmpU`, `pos_cmpS`); `((x >u y) - (x <u y)) == -1` against `x <u y` (`shipCmp`,
  `pos_ship`); `select (x >u y) x y` against `umax x y` (`selMinMax`, `pos_mm`); `ireduce.i64
  (((uextend.i128 x) * (uextend.i128 y)) >> 64)` against `umulhi x y` (`mulHi`, `pos_hi`).
* Real pairs of the shared #1119 corpus (`FVTest/Opt/midval/real_fam9_*.clif`), rejected by
  `checkCPrev` (main's `checkC` with main's normaliser in its checks) and accepted by
  `checkCertC` with the hints and fold requests `emitC` gives, with the simulation and the
  program refinement (`*_sim`); all from crypto-bigint's test build:
  - `notdec`: num-bigint's `_RNxC10num_bigint12H4M9jjHFxQlC`: `~(ireduce x + ~y)` against
    `y - ireduce x` (`notDec`);
  - `mulhi`: fastrand's `_RNxC8fastrand12H2lPqad2exxP`: the high half of a 64×64 product
    written with `i128` against `umulhi` (`mulHi`);
  - `ship`: num-bigint's `_RNxC10num_bigint12HcLFswXcneZg`: a branch on `(a <=> b) == -1`
    against `a <u b` (`shipCmp`);
  - `minmax`: num-integer's `_RNxC11num_integer12H3MSDDmzWzax`: `select (s >u 255) 255 s`
    against `umin s 255` (`selMinMax`);
  - `extext`: clap_builder's `_RNxC12clap_builder12H40CxCaocfsO`: `uextend.i64 (uextend.i32
    (ctz.i16 x))` against `uextend.i64 (ctz.i16 x)` (`extExt`).
-/

namespace Opt.MidVal.Fam9Witness
open Clif Pairs NormWitness CondWitness FoldWitness

/-! ## Main's checker (before this change) -/

/-- Main's default normaliser (family 8, `Norm.stdT`, then family 7). -/
def normPrev (f : Function) : Norm :=
  Norm.orElse (Norm.guard fam8Step) (Norm.orElse (Norm.stdT f) (Norm.guard (dropStep (atomTy f))))

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

def maskF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 63\n    v2 = band v0, v1\n    v3 = iconst.i64 -64\n    v4 = bor v2, v3\n    return v4\n}"
def maskG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v3 = iconst.i64 -64\n    v4 = bor v0, v3\n    return v4\n}"
def maskWrongF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 62\n    v2 = band v0, v1\n    v3 = iconst.i64 -64\n    v4 = bor v2, v3\n    return v4\n}"

theorem pos_mask : acceptsC maskF maskG = some true := by native_decide
theorem pos_mask_prev_rejects : acceptsPrev maskF maskG = some false := by native_decide
theorem neg_mask : acceptsC maskWrongF maskG = some false := by native_decide

def maskReF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 -16\n    v2 = band v0, v1\n    v3 = iconst.i64 3\n    v4 = bor v2, v3\n    v5 = iconst.i64 12\n    v6 = bor v4, v5\n    return v6\n}"
def maskReG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 15\n    v6 = bor v0, v1\n    return v6\n}"
def maskReWrongF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 -16\n    v2 = band v0, v1\n    v3 = iconst.i64 3\n    v4 = bor v2, v3\n    v5 = iconst.i64 8\n    v6 = bor v4, v5\n    return v6\n}"
def maskReWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 11\n    v6 = bor v0, v1\n    return v6\n}"

theorem pos_maskRe : acceptsC maskReF maskReG = some true := by native_decide
theorem pos_maskRe_prev_rejects : acceptsPrev maskReF maskReG = some false := by native_decide
theorem neg_maskRe : acceptsC maskReWrongF maskReWrongG = some false := by native_decide

def decF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 -1\n    v2 = iadd v0, v1\n    v3 = bnot v2\n    return v3\n}"
def decG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v3 = ineg v0\n    return v3\n}"
def decWrongF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 1\n    v2 = iadd v0, v1\n    v3 = bnot v2\n    return v3\n}"

theorem pos_dec : acceptsC decF decG = some true := by native_decide
theorem pos_dec_prev_rejects : acceptsPrev decF decG = some false := by native_decide
theorem neg_dec : acceptsC decWrongF decG = some false := by native_decide

def notAddF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = bnot v0\n    v3 = iadd v2, v1\n    v4 = bnot v3\n    return v4\n}"
def notAddG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v4 = isub v0, v1\n    return v4\n}"
def notAddWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v4 = isub v1, v0\n    return v4\n}"

theorem pos_notAdd : acceptsC notAddF notAddG = some true := by native_decide
theorem pos_notAdd_prev_rejects : acceptsPrev notAddF notAddG = some false := by native_decide
theorem neg_notAdd : acceptsC notAddF notAddWrongG = some false := by native_decide

def shlF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = uextend.i64 v0\n    v2 = iconst.i64 7\n    v3 = ishl v1, v2\n    v4 = ireduce.i32 v3\n    return v4\n}"
def shlG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v2 = iconst.i32 7\n    v4 = ishl v0, v2\n    return v4\n}"
def shlWrongF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = uextend.i64 v0\n    v2 = iconst.i64 33\n    v3 = ishl v1, v2\n    v4 = ireduce.i32 v3\n    return v4\n}"
def shlWrongG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v2 = iconst.i32 33\n    v4 = ishl v0, v2\n    return v4\n}"

theorem pos_shl : acceptsC shlF shlG = some true := by native_decide
theorem pos_shl_prev_rejects : acceptsPrev shlF shlG = some false := by native_decide
theorem neg_shl : acceptsC shlWrongF shlWrongG = some false := by native_decide

def unF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = sextend.i64 v0\n    v2 = ineg v1\n    v3 = ireduce.i32 v2\n    return v3\n}"
def unG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v3 = ineg v0\n    return v3\n}"
def unWrongG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v3 = bnot v0\n    return v3\n}"

theorem pos_un : acceptsC unF unG = some true := by native_decide
theorem pos_un_prev_rejects : acceptsPrev unF unG = some false := by native_decide
theorem neg_un : acceptsC unF unWrongG = some false := by native_decide

def extF : String := "function %f(i8) -> i64 {\nblock0(v0: i8):\n    v1 = uextend.i32 v0\n    v2 = uextend.i64 v1\n    return v2\n}"
def extG : String := "function %f(i8) -> i64 {\nblock0(v0: i8):\n    v2 = uextend.i64 v0\n    return v2\n}"
def extWrongF : String := "function %f(i8) -> i64 {\nblock0(v0: i8):\n    v1 = sextend.i32 v0\n    v2 = uextend.i64 v1\n    return v2\n}"

theorem pos_ext : acceptsC extF extG = some true := by native_decide
theorem pos_ext_prev_rejects : acceptsPrev extF extG = some false := by native_decide
theorem neg_ext : acceptsC extWrongF extG = some false := by native_decide

def cmpUF : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v1 = uextend.i64 v0\n    v2 = iconst.i64 0\n    v3 = icmp slt v1, v2\n    return v3\n}"
def cmpUG : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v3 = iconst.i8 0\n    return v3\n}"
def cmpUWrongF : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v1 = sextend.i64 v0\n    v2 = iconst.i64 0\n    v3 = icmp slt v1, v2\n    return v3\n}"

theorem pos_cmpU : acceptsC cmpUF cmpUG = some true := by native_decide
theorem pos_cmpU_prev_rejects : acceptsPrev cmpUF cmpUG = some false := by native_decide
theorem neg_cmpU : acceptsC cmpUWrongF cmpUG = some false := by native_decide

def cmpSF : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v1 = sextend.i64 v0\n    v2 = iconst.i64 0\n    v3 = icmp sgt v1, v2\n    return v3\n}"
def cmpSG : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v2 = iconst.i32 0\n    v3 = icmp sgt v0, v2\n    return v3\n}"
def cmpSWrongG : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v2 = iconst.i32 0\n    v3 = icmp slt v0, v2\n    return v3\n}"

theorem pos_cmpS : acceptsC cmpSF cmpSG = some true := by native_decide
theorem pos_cmpS_prev_rejects : acceptsPrev cmpSF cmpSG = some false := by native_decide
theorem neg_cmpS : acceptsC cmpSF cmpSWrongG = some false := by native_decide

def shipF : String := "function %f(i64, i64) -> i8 {\nblock0(v0: i64, v1: i64):\n    v2 = icmp ugt v0, v1\n    v3 = icmp ult v0, v1\n    v4 = isub v2, v3\n    v5 = iconst.i8 -1\n    v6 = icmp eq v4, v5\n    return v6\n}"
def shipG : String := "function %f(i64, i64) -> i8 {\nblock0(v0: i64, v1: i64):\n    v6 = icmp ult v0, v1\n    return v6\n}"
def shipWrongG : String := "function %f(i64, i64) -> i8 {\nblock0(v0: i64, v1: i64):\n    v6 = icmp ugt v0, v1\n    return v6\n}"

theorem pos_ship : acceptsC shipF shipG = some true := by native_decide
theorem pos_ship_prev_rejects : acceptsPrev shipF shipG = some false := by native_decide
theorem neg_ship : acceptsC shipF shipWrongG = some false := by native_decide

def mmF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = icmp ugt v0, v1\n    v3 = select v2, v0, v1\n    return v3\n}"
def mmG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v3 = umax v0, v1\n    return v3\n}"
def mmWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v3 = umin v0, v1\n    return v3\n}"

theorem pos_mm : acceptsC mmF mmG = some true := by native_decide
theorem pos_mm_prev_rejects : acceptsPrev mmF mmG = some false := by native_decide
theorem neg_mm : acceptsC mmF mmWrongG = some false := by native_decide

def hiF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = uextend.i128 v0\n    v3 = uextend.i128 v1\n    v4 = imul v2, v3\n    v5 = iconst.i32 64\n    v6 = ushr v4, v5\n    v7 = ireduce.i64 v6\n    return v7\n}"
def hiG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v7 = umulhi v0, v1\n    return v7\n}"
def hiWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v7 = smulhi v0, v1\n    return v7\n}"

theorem pos_hi : acceptsC hiF hiG = some true := by native_decide
theorem pos_hi_prev_rejects : acceptsPrev hiF hiG = some false := by native_decide
theorem neg_hi : acceptsC hiF hiWrongG = some false := by native_decide

/-! ## Real pairs -/

def notdecF : String := include_str "midval/real_fam9_notdec.unopt.clif"
def notdecG : String := include_str "midval/real_fam9_notdec.opt.clif"
def mulhiF : String := include_str "midval/real_fam9_mulhi.unopt.clif"
def mulhiG : String := include_str "midval/real_fam9_mulhi.opt.clif"
def shipF' : String := include_str "midval/real_fam9_ship.unopt.clif"
def shipG' : String := include_str "midval/real_fam9_ship.opt.clif"
def minmaxF : String := include_str "midval/real_fam9_minmax.unopt.clif"
def minmaxG : String := include_str "midval/real_fam9_minmax.opt.clif"
def extextF : String := include_str "midval/real_fam9_extext.unopt.clif"
def extextG : String := include_str "midval/real_fam9_extext.opt.clif"

theorem real_notdec_prev_rejects : realPrev notdecF notdecG = some false := by native_decide
theorem real_notdec_checked : (checkedC notdecF notdecG).map (·.1) = some true := by native_decide
theorem real_notdec_sim : SimRefinesC notdecF notdecG :=
  Fam8Witness.simC_of_checked1 real_notdec_checked

theorem real_mulhi_prev_rejects : realPrev mulhiF mulhiG = some false := by native_decide
theorem real_mulhi_checked : (checkedC mulhiF mulhiG).map (·.1) = some true := by native_decide
theorem real_mulhi_sim : SimRefinesC mulhiF mulhiG :=
  Fam8Witness.simC_of_checked1 real_mulhi_checked

theorem real_ship_prev_rejects : realPrev shipF' shipG' = some false := by native_decide
theorem real_ship_checked : (checkedC shipF' shipG').map (·.1) = some true := by native_decide
theorem real_ship_sim : SimRefinesC shipF' shipG' := Fam8Witness.simC_of_checked1 real_ship_checked

theorem real_minmax_prev_rejects : realPrev minmaxF minmaxG = some false := by native_decide
theorem real_minmax_checked : (checkedC minmaxF minmaxG).map (·.1) = some true := by native_decide
theorem real_minmax_sim : SimRefinesC minmaxF minmaxG :=
  Fam8Witness.simC_of_checked1 real_minmax_checked

theorem real_extext_prev_rejects : realPrev extextF extextG = some false := by native_decide
theorem real_extext_checked : (checkedC extextF extextG).map (·.1) = some true := by native_decide
theorem real_extext_sim : SimRefinesC extextF extextG :=
  Fam8Witness.simC_of_checked1 real_extext_checked

end Opt.MidVal.Fam9Witness
