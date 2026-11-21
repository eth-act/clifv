import FVTest.Opt.MidValFoldWitness
import FV.Opt.Proof.MidValDiv

/-! # Division by a constant in the mid-end validator: witnesses (#1119, `skeleton-removed div`)

`divPre` (`FV/Opt/MidValFold.lean`, inside `foldPre`) rewrites `f`'s divisions whose divisor has
a constant: `udiv`/`sdiv` by 1 into `imul x, y`, `urem` by 1 into `iconst 0`, `udiv` by `2^k` into
`ushr x, k`, `urem` by `2^k` into `band x, 2^k-1`; `check_soundC` composes the check with
`foldPre_simU` (`FV/Opt/Proof/MidValDiv.lean`).

* Hand-made: `udiv x, 8` against `ushr x, 3`, `urem x, 8` against `band x, 7`, `udiv x, 1` and
  `sdiv x, 1` against `x` are accepted, and rejected without the rewrite (`*_check_rejects`,
  `*_c0_rejects`).
* Negative: the wrong shift (`udiv x, 8` against `ushr x, 2`), signed and unsigned swapped
  (`sdiv x, 8` against `ushr x, 3`, not rewritten: `sdiv_not_rewritten`; `udiv x, 8` against
  `sshr x, 3`) and the wrong mask (`urem x, 8` against `band x, 8`) are rejected and no
  simulation, so every certificate with every hint list is rejected; a divisor 0 and an `sdiv` by
  -1 are left alone (`div0_not_rewritten`, `sdivm1_not_rewritten`) and their pairs rejected.
* Real pairs (crypto-bigint 0.7.11, serde_json 1.0.154 and blake2 0.11.0 builds,
  `FVTest/Opt/midval/real_div_*.clif`), each rejected before (`checkC0`) and accepted by
  `checkCertC` with the requests `emitC` gives (decided), with the simulation and the program
  refinement: `urem` (num_integer, `urem` by `2^k`), `udiv` (serde_json, `udiv` by `2^k`),
  `urem32` (blake2, `urem.i32` by a constant computed from constants), `one` (clap_builder, `udiv`
  by 1).
-/

namespace Opt.MidVal.DivWitness

open Clif Pairs NormWitness CondWitness FoldWitness

/-- `f`: `v6 = op.i64 v0, c` (the constant `v5`), returned. -/
def fnDiv (op : DivOp) (c : BitVec 64) : Function :=
  { name := "f", sig := { params := [ap .i64], returns := [ap .i64], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i64)], cold := false,
        body := [{ results := [5], inst := .iconst .i64 c },
          { results := [6], inst := .div op .i64 0 5 }],
        term := .ret [6] }] }

/-- `g`: `v4 = op.i64 v0, c` (the constant `v3`), returned. -/
def fnBin (op : BinaryOp) (c : BitVec 64) : Function :=
  { name := "f", sig := { params := [ap .i64], returns := [ap .i64], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i64)], cold := false,
        body := [{ results := [3], inst := .iconst .i64 c },
          { results := [4], inst := .binary op .i64 0 3 }],
        term := .ret [4] }] }

def divText (op : String) (c : String) : String :=
  s!"function %f(i64) -> i64 \{\nblock0(v0: i64):\n    v5 = iconst.i64 {c}\n    v6 = {op} v0, v5\n    return v6\n}"

def binText (op : String) (c : String) : String :=
  s!"function %f(i64) -> i64 \{\nblock0(v0: i64):\n    v3 = iconst.i64 {c}\n    v4 = {op} v0, v3\n    return v4\n}"

def idText : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}"

/-! ## Hand-made pairs -/

theorem pos_udiv : acceptsC (divText "udiv" "8") (binText "ushr" "3") = some true := by native_decide
theorem pos_udiv_check_rejects : accepts (divText "udiv" "8") (binText "ushr" "3") = some false := by
  native_decide
theorem pos_udiv_c0_rejects : acceptsC0 (divText "udiv" "8") (binText "ushr" "3") = some false := by
  native_decide

theorem pos_urem : acceptsC (divText "urem" "8") (binText "band" "7") = some true := by native_decide
theorem pos_urem_check_rejects : accepts (divText "urem" "8") (binText "band" "7") = some false := by
  native_decide
theorem pos_urem_c0_rejects : acceptsC0 (divText "urem" "8") (binText "band" "7") = some false := by
  native_decide

theorem pos_udiv1 : acceptsC (divText "udiv" "1") idText = some true := by native_decide
theorem pos_udiv1_c0_rejects : acceptsC0 (divText "udiv" "1") idText = some false := by native_decide

theorem pos_sdiv1 : acceptsC (divText "sdiv" "1") idText = some true := by native_decide
theorem pos_sdiv1_c0_rejects : acceptsC0 (divText "sdiv" "1") idText = some false := by native_decide

/-! ## Negative pairs -/

theorem udiv8_text : fn? (divText "udiv" "8") = some (fnDiv .udiv 8) := by native_decide
theorem sdiv8_text : fn? (divText "sdiv" "8") = some (fnDiv .sdiv 8) := by native_decide
theorem urem8_text : fn? (divText "urem" "8") = some (fnDiv .urem 8) := by native_decide
theorem ushr2_text : fn? (binText "ushr" "2") = some (fnBin .ushr 2) := by native_decide
theorem ushr3_text : fn? (binText "ushr" "3") = some (fnBin .ushr 3) := by native_decide
theorem sshr3_text : fn? (binText "sshr" "3") = some (fnBin .sshr 3) := by native_decide
theorem band8_text : fn? (binText "band" "8") = some (fnBin .band 8) := by native_decide

/-- Not a simulation: for the argument `x`, `f` returns `a` and `g` returns `b ≠ a`. -/
theorem not_sim_at {op : DivOp} {c : BitVec 64} {bop : BinaryOp} {d : BitVec 64} (x a b : BitVec 64)
    (hf : LStar ⟨fnDiv op c, Regs.empty.set 0 ⟨.i64, x⟩, [], (fnDiv op c).blocks.head!.body,
      (fnDiv op c).blocks.head!.term⟩ Mem.empty
      ⟨fnDiv op c, ((Regs.empty.set 0 ⟨.i64, x⟩).set 5 ⟨.i64, c⟩).set 6 ⟨.i64, a⟩, [], [], .ret [6]⟩
      Mem.empty)
    (hg : LStar ⟨fnBin bop d, Regs.empty.set 0 ⟨.i64, x⟩, [], (fnBin bop d).blocks.head!.body,
      (fnBin bop d).blocks.head!.term⟩ Mem.empty
      ⟨fnBin bop d, ((Regs.empty.set 0 ⟨.i64, x⟩).set 3 ⟨.i64, d⟩).set 4 ⟨.i64, b⟩, [], [], .ret [4]⟩
      Mem.empty)
    (hne : b ≠ a) : ¬ FunSimMU (fnDiv op c) (fnBin bop d) :=
  not_funSimMU_ret_ne (b := (fnDiv op c).blocks.head!) (b' := (fnBin bop d).blocks.head!)
    (args := [⟨.i64, x⟩]) (regs := Regs.empty.set 0 ⟨.i64, x⟩) (m := Mem.empty)
    (vals := [⟨.i64, a⟩]) (vals' := [⟨.i64, b⟩]) rfl rfl rfl rfl rfl hf rfl hg rfl
    (by intro h; cases h; exact hne rfl)

/-- The wrong shift: for `x = 8`, `udiv x, 8 = 1` and `ushr x, 2 = 2`. -/
theorem shift_not_sim : ¬ FunSimMU (fnDiv .udiv 8) (fnBin .ushr 2) :=
  not_sim_at 8 1 2 (.step rfl (.step rfl (.refl _ _))) (.step rfl (.step rfl (.refl _ _))) (by decide)

theorem neg_shift : acceptsC (divText "udiv" "8") (binText "ushr" "2") = some false := by native_decide

theorem shift_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run (fnDiv .udiv 8)) (fnBin .ushr 2) cert hints = false := by
  cases h : checkCertC (ConstPhi.run (fnDiv .udiv 8)) (fnBin .ushr 2) cert hints
  · rfl
  · exact absurd (checkedC_simMU h) shift_not_sim

/-- Signed division is not rewritten into an unsigned shift. -/
theorem sdiv_not_rewritten : divPre (fnDiv .sdiv 8) [0] = fnDiv .sdiv 8 := by native_decide

/-- Signed and unsigned swapped: for `x = -8`, `sdiv x, 8 = -1` and `ushr x, 3 = 2^61 - 1`. -/
theorem signed_not_sim : ¬ FunSimMU (fnDiv .sdiv 8) (fnBin .ushr 3) :=
  not_sim_at (-8) (-1) 0x1FFFFFFFFFFFFFFF (.step rfl (.step rfl (.refl _ _)))
    (.step rfl (.step rfl (.refl _ _))) (by decide)

theorem neg_signed : acceptsC (divText "sdiv" "8") (binText "ushr" "3") = some false := by
  native_decide

theorem signed_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run (fnDiv .sdiv 8)) (fnBin .ushr 3) cert hints = false := by
  cases h : checkCertC (ConstPhi.run (fnDiv .sdiv 8)) (fnBin .ushr 3) cert hints
  · rfl
  · exact absurd (checkedC_simMU h) signed_not_sim

/-- Unsigned and signed swapped: for `x = 2^63`, `udiv x, 8 = 2^60` and `sshr x, 3 = -2^60`. -/
theorem unsigned_not_sim : ¬ FunSimMU (fnDiv .udiv 8) (fnBin .sshr 3) :=
  not_sim_at 0x8000000000000000 0x1000000000000000 0xF000000000000000
    (.step rfl (.step rfl (.refl _ _))) (.step rfl (.step rfl (.refl _ _))) (by decide)

theorem neg_unsigned : acceptsC (divText "udiv" "8") (binText "sshr" "3") = some false := by
  native_decide

theorem unsigned_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run (fnDiv .udiv 8)) (fnBin .sshr 3) cert hints = false := by
  cases h : checkCertC (ConstPhi.run (fnDiv .udiv 8)) (fnBin .sshr 3) cert hints
  · rfl
  · exact absurd (checkedC_simMU h) unsigned_not_sim

/-- The wrong mask: for `x = 1`, `urem x, 8 = 1` and `band x, 8 = 0`. -/
theorem mask_not_sim : ¬ FunSimMU (fnDiv .urem 8) (fnBin .band 8) :=
  not_sim_at 1 1 0 (.step rfl (.step rfl (.refl _ _))) (.step rfl (.step rfl (.refl _ _))) (by decide)

theorem neg_mask : acceptsC (divText "urem" "8") (binText "band" "8") = some false := by native_decide

theorem mask_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run (fnDiv .urem 8)) (fnBin .band 8) cert hints = false := by
  cases h : checkCertC (ConstPhi.run (fnDiv .urem 8)) (fnBin .band 8) cert hints
  · rfl
  · exact absurd (checkedC_simMU h) mask_not_sim

/-- A divisor 0 (the division traps) and an `sdiv` by -1 (it traps on the minimum) are left
alone, and their pairs against a trap-free `g` rejected. -/
theorem div0_not_rewritten : divPre (fnDiv .udiv 0) [0] = fnDiv .udiv 0 := by native_decide
theorem sdivm1_not_rewritten : divPre (fnDiv .sdiv (-1)) [0] = fnDiv .sdiv (-1) := by native_decide
theorem neg_div0 : acceptsC (divText "udiv" "0") (binText "band" "0") = some false := by
  native_decide
theorem neg_sdivm1 : acceptsC (divText "sdiv" "-1")
    "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v4 = ineg v0\n    return v4\n}" =
    some false := by native_decide

/-! ## Real pairs -/

def uremF : String := include_str "midval/real_div_urem.unopt.clif"
def uremG : String := include_str "midval/real_div_urem.opt.clif"
def udivF : String := include_str "midval/real_div_udiv.unopt.clif"
def udivG : String := include_str "midval/real_div_udiv.opt.clif"
def urem32F : String := include_str "midval/real_div_urem32.unopt.clif"
def urem32G : String := include_str "midval/real_div_urem32.opt.clif"
def oneF : String := include_str "midval/real_div_one.unopt.clif"
def oneG : String := include_str "midval/real_div_one.opt.clif"

theorem real_urem_c0_rejects : c0Verdict uremF uremG = some false := by native_decide
theorem real_urem_checked : checkedC uremF uremG = some (true, true) := by native_decide
theorem real_urem_sim : SimRefinesC uremF uremG := simC_of_checked real_urem_checked

theorem real_udiv_c0_rejects : c0Verdict udivF udivG = some false := by native_decide
theorem real_udiv_checked : checkedC udivF udivG = some (true, true) := by native_decide
theorem real_udiv_sim : SimRefinesC udivF udivG := simC_of_checked real_udiv_checked

theorem real_urem32_c0_rejects : c0Verdict urem32F urem32G = some false := by native_decide
theorem real_urem32_checked : checkedC urem32F urem32G = some (true, true) := by native_decide
theorem real_urem32_sim : SimRefinesC urem32F urem32G := simC_of_checked real_urem32_checked

theorem real_one_c0_rejects : c0Verdict oneF oneG = some false := by native_decide
theorem real_one_checked : checkedC oneF oneG = some (true, true) := by native_decide
theorem real_one_sim : SimRefinesC oneF oneG := simC_of_checked real_one_checked

end Opt.MidVal.DivWitness
