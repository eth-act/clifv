import FV.Opt.Proof.RuleRestEmbedBase

/-! # Helper specification `imm64_rotl` (cprop fold)

Part of `FV/Opt/Proof/RuleRestEmbed.lean` (which imports its parts); split off to bound
the elaboration memory of a module. -/

namespace Opt.Proof

open Isle Isle.Opt Clif

set_option linter.unusedSimpArgs false

@[opt_imm] theorem imm64Rotl_spec {t t' : Ty} (ht : t ≠ .i128) (ht' : t' ≠ .i128) (b : BitVec t.width)
    (c : BitVec t'.width) :
    Rust.imm64Rotl (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.rotl b c)) := by
  imm_pre [Rust.imm64Rotl]
  simp only [Rust.band64, Rust.bor64, Rust.asU64, int_toNat_natCast, ofInt_mul_two_pow,
    shiftLeft_toNat', natCast_div_two_pow, ushiftRight_toNat']
  imm_cases t b <;> imm_cases t' c <;> simp (disch := decide) only [rotl_mask, Nat.reduceBEq,
    Bool.false_eq_true, reduceIte, Int.reduceSub, Int.reducePow, Nat.reduceSub, Int.reduceNatCast,
    BitVec.ofInt_ofNat, ushr_sub_and, shl_sub_and, toNat_beq_zero] <;> imm_solve

end Opt.Proof
