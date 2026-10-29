module

public import FV.Opt.Proof.RuleInfraIcmp

@[expose] public section

/-!
# Signed comparison bounds in `opts/icmp.isle`

The constant operand's type determines SMIN/SMAX; the comparison and replacement
constant have type `i8`, including when the operands are wider. Opening the graph
model before evaluating the RHS retains both facts without conflating the widths.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

-- Unlike a comparison RHS, `opt_node` leaves the constant's `Option Val`
-- equality intact. Strip that wrapper before the bit-vector finisher.
set_option hygiene false in
local macro "rule_bounds " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals rule_iflets_c [tySmin_ofClif, tySmax_ofClif]
  all_goals (rule_rhs_c [tySmin_ofClif, tySmax_ofClif]; opt_some_subst)
  all_goals (try opt_den_subst)
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
  all_goals (apply some_val_congr; fin_bits_k)))

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:155`: `sge(x, SMIN)` is true. -/
theorem ok_rule_icmp_155 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_155 := by
  rule_bounds rule_icmp_155

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:165`: `sle(x, SMAX)` is true. -/
theorem ok_rule_icmp_165 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_165 := by
  rule_bounds rule_icmp_165

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:170`: `sgt(x, SMAX)` is false. -/
theorem ok_rule_icmp_170 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_170 := by
  rule_bounds rule_icmp_170

-- Each guard is inhabited at narrow and wide operand widths. The same witnesses
-- check both equality at the signed endpoint and a different input, with i8 results.
example :
    Rust.tySmin (CTy.ofClif .i8) = .ok (Rust.asU64 (imm64OfBits (128#8))) ∧
    Sem.icmp .sge (128#8) (128#8) = 1#8 ∧
    Sem.icmp .sge (127#8) (128#8) = 1#8 := ⟨rfl, by decide, by decide⟩

example :
    Rust.tySmin (CTy.ofClif .i64) =
      .ok (Rust.asU64 (imm64OfBits (0x8000000000000000#64))) ∧
    Sem.icmp .sge (0x8000000000000000#64) (0x8000000000000000#64) = 1#8 ∧
    Sem.icmp .sge (0x7fffffffffffffff#64) (0x8000000000000000#64) = 1#8 :=
  ⟨rfl, by decide, by decide⟩

example :
    Rust.tySmax (CTy.ofClif .i8) = .ok (Rust.asU64 (imm64OfBits (127#8))) ∧
    Sem.icmp .sle (127#8) (127#8) = 1#8 ∧
    Sem.icmp .sle (128#8) (127#8) = 1#8 := ⟨rfl, by decide, by decide⟩

example :
    Rust.tySmax (CTy.ofClif .i64) =
      .ok (Rust.asU64 (imm64OfBits (0x7fffffffffffffff#64))) ∧
    Sem.icmp .sle (0x7fffffffffffffff#64) (0x7fffffffffffffff#64) = 1#8 ∧
    Sem.icmp .sle (0x8000000000000000#64) (0x7fffffffffffffff#64) = 1#8 :=
  ⟨rfl, by decide, by decide⟩

example :
    Rust.tySmax (CTy.ofClif .i8) = .ok (Rust.asU64 (imm64OfBits (127#8))) ∧
    Sem.icmp .sgt (127#8) (127#8) = 0#8 ∧
    Sem.icmp .sgt (128#8) (127#8) = 0#8 := ⟨rfl, by decide, by decide⟩

example :
    Rust.tySmax (CTy.ofClif .i64) =
      .ok (Rust.asU64 (imm64OfBits (0x7fffffffffffffff#64))) ∧
    Sem.icmp .sgt (0x7fffffffffffffff#64) (0x7fffffffffffffff#64) = 0#8 ∧
    Sem.icmp .sgt (0x8000000000000000#64) (0x7fffffffffffffff#64) = 0#8 :=
  ⟨rfl, by decide, by decide⟩

end Opt.Proof
