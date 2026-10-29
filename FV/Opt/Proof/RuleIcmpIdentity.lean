module

public import FV.Opt.Proof.RuleInfraIcmp

@[expose] public section

/-!
# Returned comparison results in `opts/icmp.isle`

These roots return an existing class, not a made node. Transport its denotation
through the valuation preorder, normalize the literal, then use the i8 Boolean
range of `icmp` without enumerating operand widths or condition codes.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false
namespace Opt.Proof
open Isle Isle.Opt Clif
private theorem icmp_ne_uext_zero_same (t : Ty) (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp .ne (Sem.uextend t.width (Sem.icmp cc x y)) (0#t.width) = Sem.icmp cc x y := by
  simp only [Sem.icmp]
  generalize Sem.intcc cc x y = b
  cases b <;> cases t <;> decide
private theorem icmp_ne_zero_same (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp .ne (Sem.icmp cc x y) (0#8) = Sem.icmp cc x y := by
  simp only [Sem.icmp]
  generalize Sem.intcc cc x y = b
  cases b <;> decide
private theorem icmp_eq_uext_one_same (t : Ty) (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp .eq (Sem.uextend t.width (Sem.icmp cc x y)) (1#t.width) = Sem.icmp cc x y := by
  simp only [Sem.icmp]
  generalize Sem.intcc cc x y = b
  cases b <;> cases t <;> decide
private theorem icmp_eq_one_same (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp .eq (Sem.icmp cc x y) (1#8) = Sem.icmp cc x y := by
  simp only [Sem.icmp]
  generalize Sem.intcc cc x y = b
  cases b <;> decide
private theorem icmp_band_one_same (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.binary .band (Sem.icmp cc x y) (1#8) = Sem.icmp cc x y := by
  simp only [Sem.icmp]
  generalize Sem.intcc cc x y = b
  cases b <;> decide

set_option hygiene false in
local macro "icmp_identity_prefix " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals (rule_rhs_c []; opt_some_subst)
  all_goals try opt_den_subst
  all_goals (apply Valuation.le_trans hle1 hle3; opt_rw_lhs; apply some_val_congr)
  all_goals change @Eq (BitVec 8) _ _
  all_goals (
    simp (disch := first | assumption | decide) only [asU64_imm64OfBits, Int.natCast_eq_zero,
      Int.natCast_inj, toNat_eq_iff_ofNat, toNat_eq_zero_iff, Int.reduceToNat, natCast_toNat_eq_int,
      Int.reduceLE, true_and] at *
    try opt_destruct
    try subst_vars)))
theorem ok_rule_icmp_49 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_49 := by
  icmp_identity_prefix rule_icmp_49
  all_goals first
    | exact (icmp_ne_uext_zero_same _ _ _ _).symm
    | exact (icmp_ne_zero_same _ _ _).symm

theorem ok_rule_icmp_77 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_77 := by
  icmp_identity_prefix rule_icmp_77
  all_goals first
    | exact (icmp_eq_uext_one_same _ _ _ _).symm
    | exact (icmp_eq_one_same _ _ _).symm

theorem ok_rule_icmp_91 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_91 := by
  icmp_identity_prefix rule_icmp_91
  all_goals exact (icmp_band_one_same _ _ _).symm

-- Every identity has true and false comparison instances. The symbolic operand
-- width also admits zero; actual matched CLIF operands have widths 8 through 128.
example :
    Sem.icmp .ne (Sem.uextend 64 (Sem.icmp .slt (128#8) (127#8))) (0#64) = 1#8 ∧
    Sem.icmp .ne (Sem.uextend 16 (Sem.icmp .eq (0#32) (1#32))) (0#16) = 0#8 := by decide
example :
    Sem.icmp .ne (Sem.icmp .slt (128#8) (127#8)) (0#8) = 1#8 ∧
    Sem.icmp .ne (Sem.icmp .ne (0#0) (0#0)) (0#8) = 0#8 := by decide
example :
    Sem.icmp .eq (Sem.uextend 128 (Sem.icmp .eq (7#64) (7#64))) (1#128) = 1#8 ∧
    Sem.icmp .eq (Sem.uextend 32 (Sem.icmp .ne (7#64) (7#64))) (1#32) = 0#8 := by decide
example :
    Sem.icmp .eq (Sem.icmp .eq (255#8) (255#8)) (1#8) = 1#8 ∧
    Sem.icmp .eq (Sem.icmp .slt (0#0) (0#0)) (1#8) = 0#8 := by decide
example :
    Sem.binary .band (Sem.icmp .ugt (255#8) (0#8)) (1#8) = 1#8 ∧
    Sem.binary .band (Sem.icmp .slt (0#128) (0#128)) (1#8) = 0#8 := by decide

end Opt.Proof
