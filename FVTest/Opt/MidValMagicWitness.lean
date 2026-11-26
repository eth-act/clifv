import FVTest.Opt.MidValDivWitness
import FV.Opt.Proof.MidValMagic

/-! # Division by a constant with magic numbers in the mid-end validator: witnesses (#1119)

`magicPre` (`FV/Opt/MidValFold.lean`, inside `foldPre`) rewrites `f`'s `udiv`/`urem` at width 32
or 64 whose divisor is a constant other than 0, 1 and the powers of two into Cranelift's
multiply-high sequence (`Isle.Opt.Rust.magicU`, the port of `magic_u32`/`magic_u64`);
`check_soundC` composes the check with `foldPre_simU` (`magicPre_simU`,
`FV/Opt/Proof/MidValMagic.lean`).

* The magic numbers: `Isle.Opt.Rust.magicU` gives Cranelift's own test vectors
  (`opts/div_const.rs`: `magic_u32(7) = (0x24924925, true, 3)`, `magic_u32(10)`, `magic_u64(7)`,
  `magic_u64(10)`).
* Hand-made: `udiv x, 3` against `umulhi x, 0xAAAA…AB; ushr 1`, `urem x, 3` against the same
  quotient times 3 subtracted from `x`, `udiv x, 7` against the add sequence; each accepted and
  rejected without the rewrite (`*_check_rejects`, `*_c0_rejects`).
* Negative: a multiplier one too small (`udiv x, 3` against `umulhi x, 0xAAAA…AA; ushr 1`) is no
  simulation (`x = 3`: 1 against 0), so every certificate with every hint list is rejected
  (`low_rejected`); `sdiv` by 7, `udiv` by 0, by a power of two (left to `divPre`) and at width 8
  are left alone (`*_not_rewritten`).
* Real pairs (semver 1.0.28, serde_json 1.0.154 and crypto-bigint 0.7.11 builds, the #1119
  corpus, `FVTest/Opt/midval/real_magic_*.clif`), each rejected before (`checkC0`) and accepted by
  `checkCertC` with the requests `emitC` gives (decided), with the simulation and the program
  refinement: `udiv10` (semver, `udiv.i64` by 10), `udiv24` (dissimilar, `udiv` by 24, the most
  frequent divisor), `add32` (`core::time::Duration::new`, `udiv.i32`/`urem.i32` by 10^9, the add
  step), `urem192` (crypto_bigint, `urem.i32` by 192), `add64` (`core::num::int_log10::u64_impl`,
  `udiv` by 10^5 and 10^10, the add step at width 64).
-/

namespace Opt.MidVal.MagicWitness

open Clif Pairs NormWitness CondWitness FoldWitness DivWitness

/-! ## The magic numbers -/

theorem magicU_u32_7 : Isle.Opt.Rust.magicU 32 7 = (0x24924925, true, 3) := by native_decide
theorem magicU_u32_10 : Isle.Opt.Rust.magicU 32 10 = (0xcccccccd, false, 3) := by native_decide
theorem magicU_u64_7 : Isle.Opt.Rust.magicU 64 7 = (0x2492492492492493, true, 3) := by
  native_decide
theorem magicU_u64_10 : Isle.Opt.Rust.magicU 64 10 = (0xcccccccccccccccd, false, 3) := by
  native_decide

/-! ## Hand-made pairs -/

def gText (body : String) (ret : String) : String :=
  s!"function %f(i64) -> i64 \{\nblock0(v0: i64):\n{body}    return {ret}\n}"

/-- Cranelift's `udiv x, 3`: `umulhi x, 0xAAAA_AAAA_AAAA_AAAB`, then `ushr 1`. -/
def udiv3G : String :=
  gText "    v3 = iconst.i64 -6148914691236517205\n    v4 = umulhi v0, v3\n    v5 = iconst.i64 1\n    v6 = ushr v4, v5\n" "v6"

/-- Cranelift's `urem x, 3`: the quotient, times 3, subtracted from `x`. -/
def urem3G : String :=
  gText ("    v3 = iconst.i64 -6148914691236517205\n    v4 = umulhi v0, v3\n    v5 = iconst.i64 1\n" ++
    "    v6 = ushr v4, v5\n    v7 = iconst.i64 3\n    v8 = imul v6, v7\n    v9 = isub v0, v8\n") "v9"

/-- Cranelift's `udiv x, 7` (the add step): `q = umulhi x, M; ((x - q) >> 1 + q) >> 2`. -/
def udiv7G : String :=
  gText ("    v3 = iconst.i64 2635249153387078803\n    v4 = umulhi v0, v3\n    v5 = isub v0, v4\n" ++
    "    v6 = iconst.i64 1\n    v7 = ushr v5, v6\n    v8 = iadd v4, v7\n    v9 = iconst.i64 2\n" ++
    "    v10 = ushr v8, v9\n") "v10"

/-- A multiplier one too small. -/
def udiv3LowG : String :=
  gText "    v3 = iconst.i64 -6148914691236517206\n    v4 = umulhi v0, v3\n    v5 = iconst.i64 1\n    v6 = ushr v4, v5\n" "v6"

theorem pos_udiv3 : acceptsC (divText "udiv" "3") udiv3G = some true := by native_decide
theorem pos_udiv3_check_rejects : accepts (divText "udiv" "3") udiv3G = some false := by
  native_decide
theorem pos_udiv3_c0_rejects : acceptsC0 (divText "udiv" "3") udiv3G = some false := by
  native_decide

theorem pos_urem3 : acceptsC (divText "urem" "3") urem3G = some true := by native_decide
theorem pos_urem3_check_rejects : accepts (divText "urem" "3") urem3G = some false := by
  native_decide
theorem pos_urem3_c0_rejects : acceptsC0 (divText "urem" "3") urem3G = some false := by
  native_decide

theorem pos_udiv7 : acceptsC (divText "udiv" "7") udiv7G = some true := by native_decide
theorem pos_udiv7_check_rejects : accepts (divText "udiv" "7") udiv7G = some false := by
  native_decide
theorem pos_udiv7_c0_rejects : acceptsC0 (divText "udiv" "7") udiv7G = some false := by
  native_decide

/-! ## Negative pairs -/

/-- `g`: a multiplier one too small, then `ushr 1`. -/
def fnLow : Function :=
  { name := "f", sig := { params := [ap .i64], returns := [ap .i64], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i64)], cold := false,
        body := [{ results := [3], inst := .iconst .i64 0xaaaaaaaaaaaaaaaa },
          { results := [4], inst := .binary .umulhi .i64 0 3 },
          { results := [5], inst := .iconst .i64 1 },
          { results := [6], inst := .binary .ushr .i64 4 5 }],
        term := .ret [6] }] }

theorem udiv3_text : fn? (divText "udiv" "3") = some (fnDiv .udiv 3) := by native_decide
theorem low_text : fn? udiv3LowG = some fnLow := by native_decide

/-- Not a simulation: for `x = 3`, `udiv x, 3 = 1` and the low multiplier gives 0. -/
theorem low_not_sim : ¬ FunSimMU (fnDiv .udiv 3) fnLow :=
  not_funSimMU_ret_ne (b := (fnDiv .udiv 3).blocks.head!) (b' := fnLow.blocks.head!)
    (args := [⟨.i64, 3⟩]) (regs := Regs.empty.set 0 ⟨.i64, 3⟩) (m := Mem.empty)
    (vals := [⟨.i64, 1⟩]) (vals' := [⟨.i64, 0⟩]) rfl rfl rfl rfl rfl
    (.step rfl (.step rfl (.refl _ _))) rfl
    (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (by intro h; cases h)

theorem neg_low : acceptsC (divText "udiv" "3") udiv3LowG = some false := by native_decide

theorem low_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run (fnDiv .udiv 3)) fnLow cert hints = false := by
  cases h : checkCertC (ConstPhi.run (fnDiv .udiv 3)) fnLow cert hints
  · rfl
  · exact absurd (checkedC_simMU h) low_not_sim

/-- `sdiv` (rounding toward zero; Cranelift's signed sequence is a different one), a divisor 0
(the division traps), a power of two (`divPre`'s) and width 8 (Cranelift's rules are for 32 and 64
bits) are left alone. -/
theorem sdiv7_not_rewritten : magicPre (fnDiv .sdiv 7) [0] = fnDiv .sdiv 7 := by native_decide
theorem div0_not_rewritten : magicPre (fnDiv .udiv 0) [0] = fnDiv .udiv 0 := by native_decide
theorem pow2_not_rewritten : magicPre (fnDiv .udiv 8) [0] = fnDiv .udiv 8 := by native_decide

/-- `f`: `v2 = udiv.i8 v0, 3`. -/
def fnDiv8 : Function :=
  { name := "f", sig := { params := [ap .i8], returns := [ap .i8], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i8)], cold := false,
        body := [{ results := [1], inst := .iconst .i8 3 },
          { results := [2], inst := .div .udiv .i8 0 1 }],
        term := .ret [2] }] }

theorem i8_not_rewritten : magicPre fnDiv8 [0] = fnDiv8 := by native_decide

/-! ## Real pairs -/

def udiv10F : String := include_str "midval/real_magic_udiv10.unopt.clif"
def udiv10G : String := include_str "midval/real_magic_udiv10.opt.clif"
def udiv24F : String := include_str "midval/real_magic_udiv24.unopt.clif"
def udiv24G : String := include_str "midval/real_magic_udiv24.opt.clif"
def add32F : String := include_str "midval/real_magic_add32.unopt.clif"
def add32G : String := include_str "midval/real_magic_add32.opt.clif"
def urem192F : String := include_str "midval/real_magic_urem192.unopt.clif"
def urem192G : String := include_str "midval/real_magic_urem192.opt.clif"
def add64F : String := include_str "midval/real_magic_add64.unopt.clif"
def add64G : String := include_str "midval/real_magic_add64.opt.clif"

theorem real_udiv10_c0_rejects : c0Verdict udiv10F udiv10G = some false := by native_decide
theorem real_udiv10_checked : checkedC udiv10F udiv10G = some (true, true) := by native_decide
theorem real_udiv10_sim : SimRefinesC udiv10F udiv10G := simC_of_checked real_udiv10_checked

theorem real_udiv24_c0_rejects : c0Verdict udiv24F udiv24G = some false := by native_decide
theorem real_udiv24_checked : checkedC udiv24F udiv24G = some (true, true) := by native_decide
theorem real_udiv24_sim : SimRefinesC udiv24F udiv24G := simC_of_checked real_udiv24_checked

theorem real_add32_c0_rejects : c0Verdict add32F add32G = some false := by native_decide
theorem real_add32_checked : checkedC add32F add32G = some (true, true) := by native_decide
theorem real_add32_sim : SimRefinesC add32F add32G := simC_of_checked real_add32_checked

theorem real_urem192_c0_rejects : c0Verdict urem192F urem192G = some false := by native_decide
theorem real_urem192_checked : checkedC urem192F urem192G = some (true, true) := by native_decide
theorem real_urem192_sim : SimRefinesC urem192F urem192G := simC_of_checked real_urem192_checked

theorem real_add64_c0_rejects : c0Verdict add64F add64G = some false := by native_decide
theorem real_add64_checked : checkedC add64F add64G = some (true, true) := by native_decide
theorem real_add64_sim : SimRefinesC add64F add64G := simC_of_checked real_add64_checked

end Opt.MidVal.MagicWitness
