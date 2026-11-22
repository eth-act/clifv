import FVTest.Opt.MidValPhiWitness

/-! # Unsigned comparisons with 0 in the fold's constants: witnesses (#1119, `rewrite:domtree`/`rewrite:blocks`)

`constEval` (`FV/Opt/MidValFold.lean`) gives the constant of `icmp ult x, 0` and `icmp ugt 0, x`
(0) and of `icmp uge x, 0` and `icmp ule 0, x` (1) whatever `x` holds (`zeroCmp`), so branch
folding (`foldBr`) folds the branches on them as Cranelift's mid-end does; `check_soundC`
composes the check with `foldPre_simU`, through `foldBr_simU` and `zeroCmp_sound`
(`FV/Opt/Proof/MidValFold.lean`).

* Hand-made: `brif (icmp ult v0, 0)` and `brif (icmp ugt 0, v0)` against a `jump` to the `else`
  block, `brif (icmp uge v0, 0)` and `brif (icmp ule 0, v0)` against a `jump` to the `then`
  block, are accepted (`pos_*`) and rejected without the rule (`*_check_rejects`, `*_c0_rejects`).
* Negative: `icmp ugt v0, 0` (`v0 ≠ 0`), `icmp ult 0, v0` (the zero on the other side) and
  `icmp ult v0, 1` (not zero) are not folded (`*_not_folded`) and their pairs against a `jump`
  rejected (`neg_*`); for `icmp ugt v0, 0` there is no simulation (`ugt_not_sim`), so every
  certificate with every hint list is rejected (`ugt_rejected`).
* Real pairs (crypto-bigint 0.7.11 and serde_json 1.0.154 test builds,
  `FVTest/Opt/midval/real_zero_*.clif`), each rejected before (`checkC0`) and accepted by
  `checkCertC` with the requests `emitC` gives (decided), with the simulation and the program
  refinement: `toml` (`icmp ule 0, v3`, a `rewrite:domtree` rejection), `ws` (`char::is_whitespace`:
  `icmp ule 0, v5`, `rewrite:domtree`), `serde` (serde_core: `icmp ult v6, 0` and the block it
  guards removed, `rewrite:blocks`).
-/

namespace Opt.MidVal.ZeroWitness

open Clif Pairs NormWitness CondWitness FoldWitness

/-! ## Hand-made pairs -/

/-- `f`: `v1 = iconst.i32 0`, `v2 = icmp cc a, b` (operands `v0`/`v1` as given), branch on `v2`
to `block1` (returns 1) or `block2` (returns 0). -/
def cmpText (cc a b : String) (k : String := "0") : String :=
  s!"function %f(i32) -> i32 \{\nblock0(v0: i32):\n    v1 = iconst.i32 {k}\n    v2 = icmp {cc} {a}, {b}\n    brif v2, block1, block2\n\nblock1:\n    v4 = iconst.i32 1\n    return v4\n\nblock2:\n    v5 = iconst.i32 0\n    return v5\n}"

/-- `ultG`: `jump block2` (returns 0); `keepWrongG`: `jump block1` (returns 1). -/
theorem pos_ult : acceptsC (cmpText "ult" "v0" "v1") ultG = some true := by native_decide
theorem pos_ult_check_rejects : accepts (cmpText "ult" "v0" "v1") ultG = some false := by
  native_decide
theorem pos_ult_c0_rejects : acceptsC0 (cmpText "ult" "v0" "v1") ultG = some false := by
  native_decide

theorem pos_ugt : acceptsC (cmpText "ugt" "v1" "v0") ultG = some true := by native_decide
theorem pos_ugt_check_rejects : accepts (cmpText "ugt" "v1" "v0") ultG = some false := by
  native_decide
theorem pos_ugt_c0_rejects : acceptsC0 (cmpText "ugt" "v1" "v0") ultG = some false := by
  native_decide

theorem pos_uge : acceptsC (cmpText "uge" "v0" "v1") keepWrongG = some true := by native_decide
theorem pos_uge_check_rejects : accepts (cmpText "uge" "v0" "v1") keepWrongG = some false := by
  native_decide
theorem pos_uge_c0_rejects : acceptsC0 (cmpText "uge" "v0" "v1") keepWrongG = some false := by
  native_decide

theorem pos_ule : acceptsC (cmpText "ule" "v1" "v0") keepWrongG = some true := by native_decide
theorem pos_ule_check_rejects : accepts (cmpText "ule" "v1" "v0") keepWrongG = some false := by
  native_decide
theorem pos_ule_c0_rejects : acceptsC0 (cmpText "ule" "v1" "v0") keepWrongG = some false := by
  native_decide

/-! ## Negative pairs -/

/-- `f` of `cmpText cc a b k` as a function. -/
def cmpFn (cc : IntCC) (a b : ValueId) (k : BitVec 32) : Function :=
  fnBr2 [{ results := [1], inst := .iconst .i32 k }, { results := [2], inst := .icmp cc .i32 a b }] 2

theorem ugtF_text : fn? (cmpText "ugt" "v0" "v1") = some (cmpFn .ugt 0 1 0) := by native_decide

/-- `x >u 0` depends on `x`: not folded, the pair against `jump block1` rejected. -/
theorem ugt_not_folded : foldBr (cmpFn .ugt 0 1 0) [0] = cmpFn .ugt 0 1 0 := by native_decide
theorem neg_ugt : acceptsC (cmpText "ugt" "v0" "v1") keepWrongG = some false := by native_decide

/-- For `v0 = 0`, `f` returns 0 and `g` 1. -/
theorem ugt_not_sim : ¬ FunSimMU (cmpFn .ugt 0 1 0) jump1Fn :=
  not_funSimMU_ret_ne (b := (cmpFn .ugt 0 1 0).blocks.head!) (b' := jump1Fn.blocks.head!)
    (args := [⟨.i32, 0⟩]) (regs := Regs.empty.set 0 ⟨.i32, 0⟩) (m := Mem.empty)
    (vals := [⟨.i32, 0⟩]) (vals' := [⟨.i32, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate and every hint list (prep requests included). -/
theorem ugt_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run (cmpFn .ugt 0 1 0)) jump1Fn cert hints = false := by
  cases h : checkCertC (ConstPhi.run (cmpFn .ugt 0 1 0)) jump1Fn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) ugt_not_sim

/-- `0 <u x` (the zero on the other side) depends on `x`. -/
theorem ult0_not_folded : foldBr (cmpFn .ult 1 0 0) [0] = cmpFn .ult 1 0 0 := by native_decide
theorem neg_ult0 : acceptsC (cmpText "ult" "v1" "v0") ultG = some false := by native_decide

/-- `x <u 1` depends on `x`. -/
theorem ult1_not_folded : foldBr (cmpFn .ult 0 1 1) [0] = cmpFn .ult 0 1 1 := by native_decide
theorem neg_ult1 : acceptsC (cmpText "ult" "v0" "v1" "1") ultG = some false := by native_decide

/-! ## Real pairs -/

def tomlF : String := include_str "midval/real_zero_toml.unopt.clif"
def tomlG : String := include_str "midval/real_zero_toml.opt.clif"
def wsF : String := include_str "midval/real_zero_ws.unopt.clif"
def wsG : String := include_str "midval/real_zero_ws.opt.clif"
def serdeF : String := include_str "midval/real_zero_serde.unopt.clif"
def serdeG : String := include_str "midval/real_zero_serde.opt.clif"

theorem real_toml_c0_rejects : c0Verdict tomlF tomlG = some false := by native_decide
theorem real_toml_checked : checkedC tomlF tomlG = some (true, true) := by native_decide
theorem real_toml_sim : SimRefinesC tomlF tomlG := simC_of_checked real_toml_checked

theorem real_ws_c0_rejects : c0Verdict wsF wsG = some false := by native_decide
theorem real_ws_checked : checkedC wsF wsG = some (true, true) := by native_decide
theorem real_ws_sim : SimRefinesC wsF wsG := simC_of_checked real_ws_checked

theorem real_serde_c0_rejects : c0Verdict serdeF serdeG = some false := by native_decide
theorem real_serde_checked : checkedC serdeF serdeG = some (true, true) := by native_decide
theorem real_serde_sim : SimRefinesC serdeF serdeG := simC_of_checked real_serde_checked

end Opt.MidVal.ZeroWitness

