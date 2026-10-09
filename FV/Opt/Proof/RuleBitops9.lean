import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/bitops.isle:79`: an OR constant absorbs an AND mask

Normalize the Rust 64-bit complement before bit-blasting the guard. The guard then says
exactly that the two presented constants are complements at the matched CLIF width;
the existing graph-denotation template proves the rewrite without changing `RuleOk`.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- The Rust unsigned complement, transported back to its 64-bit pattern. -/
theorem masked_or_not64 (a : Int) :
    BitVec.ofInt 64 (Rust.asU64 (-a - 1)) = ~~~(BitVec.ofInt 64 a) := by
  simp only [asU64_bv, ofInt_natCast_toNat, BitVec.setWidth_eq,
    ofInt_sub', BitVec.ofInt_neg, BitVec.ofInt_ofNat]
  exact (BitVec.not_eq_neg_add (BitVec.ofInt 64 a)).symm

/-- Masking both unsigned immediates makes the guard a width-local complement test.
The integer subtraction has already been eliminated by `masked_or_not64`, so the
remaining four obligations contain only bitwise operations and zero-extension. -/
theorem masked_or_guard {t : Ty} (ht : t ≠ .i128) (y z : BitVec t.width) :
    (Rust.band64 (2 ^ t.width - 1) (z.toNat : Int) ==
      Rust.band64 (2 ^ t.width - 1) (Rust.asU64 (-(y.toNat : Int) - 1))) =
      (z == ~~~y) := by
  simp only [band64_bv, masked_or_not64, ofInt_natCast_toNat,
    natCast_beq_natCast, toNat_beq_toNat]
  imm_cases t y z <;>
    simp only [Int.reducePow, Int.reduceSub, BitVec.ofInt_ofNat, BitVec.setWidth_eq] <;>
    bv_decide

set_option maxHeartbeats 4000000 in
/-- `bitops.isle:79`, preserving the original match and if-let contract. -/
theorem ok_rule_bitops_79 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_79 := by
  rule_intro rule_bitops_79
  rule_lhs hG
  all_goals opt_split_i128
  all_goals rule_iflets_c [tyMask_ofClif, tyMask_ofClif_i128, panics_throw_bind,
    except_throw_bind, toExt_throw, masked_or_guard]
  all_goals (rule_rhs_y; opt_some_subst; rule_finish_x)

/-! Inhabited helper instances and matching guard/rewrite witnesses. -/

example : BitVec.ofInt 64 (Rust.asU64 (-0 - 1)) = ~~~(0#64) :=
  masked_or_not64 0
example : BitVec.ofInt 64 (Rust.asU64 (-18446744073709551615 - 1)) =
    ~~~(18446744073709551615#64) := masked_or_not64 18446744073709551615

example :
    (Rust.band64 255 128 == Rust.band64 255 (Rust.asU64 (-127 - 1))) =
      ((128#8) == ~~~(127#8)) :=
  masked_or_guard (t := .i8) (by decide) (127#8) (128#8)
example :
    (Rust.band64 18446744073709551615 9223372036854775808 ==
      Rust.band64 18446744073709551615 (Rust.asU64 (-9223372036854775807 - 1))) =
      ((9223372036854775808#64) == ~~~(9223372036854775807#64)) :=
  masked_or_guard (t := .i64) (by decide) (9223372036854775807#64) (9223372036854775808#64)

example : Rust.tyMask (CTy.ofClif .i8) = .ok 255 ∧
    Rust.band64 255 128 = Rust.band64 255 (Rust.asU64 (-127 - 1)) ∧
    Sem.bor (Sem.band (128#8) (127#8)) (128#8) = Sem.bor (128#8) (128#8) :=
  ⟨rfl, by decide⟩
example : Rust.tyMask (CTy.ofClif .i16) = .ok 65535 ∧
    Rust.band64 65535 32768 = Rust.band64 65535 (Rust.asU64 (-32767 - 1)) ∧
    Sem.bor (Sem.band (65535#16) (32767#16)) (32768#16) =
      Sem.bor (65535#16) (32768#16) := ⟨rfl, by decide⟩
example : Rust.tyMask (CTy.ofClif .i32) = .ok 4294967295 ∧
    Rust.band64 4294967295 2147483648 =
      Rust.band64 4294967295 (Rust.asU64 (-2147483647 - 1)) ∧
    Sem.bor (Sem.band (4294967295#32) (2147483647#32)) (2147483648#32) =
      Sem.bor (4294967295#32) (2147483648#32) := ⟨rfl, by decide⟩
example : Rust.tyMask (CTy.ofClif .i64) = .ok 18446744073709551615 ∧
    Rust.band64 18446744073709551615 9223372036854775808 =
      Rust.band64 18446744073709551615 (Rust.asU64 (-9223372036854775807 - 1)) ∧
    Sem.bor (Sem.band (18446744073709551615#64) (9223372036854775807#64))
      (9223372036854775808#64) =
      Sem.bor (18446744073709551615#64) (9223372036854775808#64) := ⟨rfl, by decide⟩
example : Rust.band64 18446744073709551615 0 =
      Rust.band64 18446744073709551615 (Rust.asU64 (-18446744073709551615 - 1)) ∧
    Sem.bor (Sem.band (9223372036854775808#64) (18446744073709551615#64)) (0#64) =
      Sem.bor (9223372036854775808#64) (0#64) := by decide
example : Rust.band64 18446744073709551615 18446744073709551615 =
      Rust.band64 18446744073709551615 (Rust.asU64 (-0 - 1)) ∧
    Sem.bor (Sem.band (0#64) (0#64)) (18446744073709551615#64) =
      Sem.bor (0#64) (18446744073709551615#64) := by decide

end Opt.Proof
