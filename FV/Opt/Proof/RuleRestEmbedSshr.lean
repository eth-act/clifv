import FV.Opt.Proof.RuleRestEmbedBase

/-! # Helper specification `imm64_sshr` (cprop fold)

Part of `FV/Opt/Proof/RuleRestEmbed.lean` (which imports its parts); split off to bound
the elaboration memory of a module. -/

namespace Opt.Proof

open Isle Isle.Opt Clif

set_option linter.unusedSimpArgs false

@[opt_imm] theorem imm64Sshr_spec {t t' : Ty} (ht : t ≠ .i128) (hv : t.isVec = false)
    (ht' : t' ≠ .i128) (hv' : t'.isVec = false) (b : BitVec t.width)
    (c : BitVec t'.width) :
    Rust.imm64Sshr (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.sshr b c)) := by
  imm_pre [Rust.imm64Sshr]
  rw [show 64 - (64 - (CTy.ofClif t).bits) = t.width by cases t <;> simp_all [ofClif_bits, Ty.width],
    ofInt_imm64OfBits ht hv]
  simp only [Rust.band64, int_toNat_natCast, toInt_div_two_pow, sshiftRight_toNat']
  imm_cases t b <;> imm_cases t' c <;> simp (disch := decide) only [sshr_mask, Nat.reduceBEq,
    Bool.false_eq_true, reduceIte, Int.reduceSub, Int.reducePow, Nat.reduceSub, Int.reduceNatCast,
    ge_iff_le, Nat.reduceLeDiff, toInt_div_two_pow, sshiftRight_toNat', int_toNat_natCast] <;>
    imm_solve

end Opt.Proof
