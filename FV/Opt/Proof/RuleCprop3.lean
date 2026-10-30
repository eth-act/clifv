import FV.Opt.Proof.RuleRestEmbed
import FV.Opt.Proof.KernelBV
import FV.Opt.Proof.RuleInfraShiftAmt

/-!
# `opts/cprop.isle` (part 3): proven `simplify` rules (R0)

320, 322, 324 (reassociating shifts of a constant) by `rule_auto_xr`; 375, 377, 379 (folding
`bswap` of a constant) by `rule_auto_bswap`, with the helper specs `bswap16_spec`,
`bswap32_spec`, `bswap64_spec` (`u64_bswap16/32/64` of a presented immediate is `Sem.bswap`).

The bit-vector goals of 320–324, `x <<< a <<< b = x <<< b <<< a` and the same for `>>>` and
`sshiftRight` (one per value type and pair of amount types), go to `kbv_amt` first
(`RuleInfraShiftAmt.lean`: both sides become one shift by the sum of the amounts). The general
`kbv` search closes them too, but took 25 s per goal at 16 bits.
-/

set_option linter.unusedSimpArgs false
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif

-- In this module `kbv` first tries `kbv_amt` (`RuleInfraShiftAmt.lean`) on the isolated goal, under
-- `kbv_guard` (a failure, also a runtime exception, falls through to the general search).
open Lean Elab Tactic in
local elab_rules : tactic
  | `(tactic| kbv) => Opt.Proof.KernelBV.isolate (do evalTactic (← `(tactic| kbv_guard 200000 kbv_amt)))

/-! ## `u64_bswap*` as `Sem.bswap` -/

/-- `i64` re-cast of an immediate, below 64 bits. -/
theorem ofInt_asI64 {w : Nat} (hw : w ≤ 64) (z : Int) :
    BitVec.ofInt w (Rust.asI64 z) = BitVec.ofInt w z := by
  unfold Rust.asI64
  by_cases h : w = 64
  · subst h; exact BitVec.ofInt_toInt
  · rw [ofInt_eq_setWidth (by omega), ofInt_eq_setWidth (w := w) (by omega), BitVec.ofInt_toInt]

theorem ofNat_byte {w : Nat} (hw : 8 ≤ w) (x : BitVec w) (k : Nat) :
    BitVec.ofNat w (x.toNat / 2 ^ k % 256) = (x >>> k) &&& BitVec.ofNat w 255 := by
  apply BitVec.eq_of_toNat_eq
  have h255 : 255 < 2 ^ w := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hw)
  have hlt : x.toNat / 2 ^ k % 256 < 2 ^ w := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h255, Nat.shiftRight_eq_div_pow,
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem asU64_natCast_toNat {w : Nat} (hw : w ≤ 64) (x : BitVec w) :
    (Rust.asU64 (x.toNat : Int)).toNat = x.toNat := by
  have : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hw)
  simp [Rust.asU64]
  omega


theorem ofInt_byte {w : Nat} (hw : 8 ≤ w) (x : BitVec w) (k : Nat) :
    BitVec.ofInt w ((x.toNat : Int) / 2 ^ k % 256) = (x >>> k) &&& BitVec.ofNat w 255 := by
  rw [show ((x.toNat : Int) / 2 ^ k % 256) = ((x.toNat / 2 ^ k % 256 : Nat) : Int) by rw [Int.natCast_emod, Int.natCast_ediv, Int.natCast_pow]; rfl,
    BitVec.ofInt_natCast, ofNat_byte hw]

/-- The Nat fold of `Rust.bswap` over `range k`, bitwise: bit `j` is bit `j % 8` of byte
`k - 1 - j / 8` of `N`, below `8 * k`. -/
private theorem rbswap_fold_testBit (N : Nat) : ∀ k j,
    ((List.range k).foldl (fun acc i => acc * 256 + N / 2 ^ (8 * i) % 256) 0).testBit j =
      (decide (j < 8 * k) && N.testBit (8 * (k - 1 - j / 8) + j % 8))
  | 0, j => by simp
  | k + 1, j => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.mul_comm,
      show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by decide))]
    by_cases h : j < 8
    · have h1 : 8 * (k + 1 - 1 - j / 8) + j % 8 = j + 8 * k := by omega
      simp only [h, ↓reduceIte, h1, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow,
        Nat.testBit_div_two_pow, show j < 8 * (k + 1) by omega, decide_true, Bool.true_and]
    · have h1 : 8 * (k - 1 - (j - 8) / 8) + (j - 8) % 8 = 8 * (k + 1 - 1 - j / 8) + j % 8 := by omega
      simp only [h, ↓reduceIte]
      rw [rbswap_fold_testBit N k (j - 8), h1]
      by_cases h2 : j < 8 * (k + 1)
      · simp [h2, show j - 8 < 8 * k by omega]
      · simp [h2, show ¬ j - 8 < 8 * k by omega]

/-- The `Int` fold of `Rust.bswap` on a natural number is the `Nat` fold. -/
private theorem rbswap_fold_natCast (N : Nat) : ∀ k,
    (List.range k).foldl (fun (acc : Int) i => acc * 256 + (N : Int) / 2 ^ (8 * i) % 256) 0 =
      (((List.range k).foldl (fun acc i => acc * 256 + N / 2 ^ (8 * i) % 256) 0 : Nat) : Int)
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, rbswap_fold_natCast N k]
    rw [Int.natCast_add, Int.natCast_mul, Int.natCast_emod, Int.natCast_ediv, Int.natCast_pow]
    rfl

/-- `Rust.bswap n` of a presented `8 * n`-bit immediate is `Sem.bswap` (bitwise:
`rbswap_fold_testBit`, `getLsbD_bswap`). -/
private theorem rbswap_spec {w : Nat} (n : Nat) (hn : w = 8 * n) (h64 : w ≤ 64) (x : BitVec w) :
    BitVec.ofInt w (Rust.asI64 (Rust.bswap n (x.toNat : Int))) = Sem.bswap x := by
  rw [ofInt_asI64 h64]
  simp only [Rust.bswap, asU64_natCast_toNat h64]
  rw [Nat.mod_eq_of_lt (hn ▸ x.isLt), rbswap_fold_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ofNat, rbswap_fold_testBit, getLsbD_bswap (by omega),
    show w / 8 = n by omega, ← BitVec.testBit_toNat]
  simp [hj, show j < 8 * n by omega]

/-- `u64_bswap16` of a presented `i16` immediate is `Sem.bswap`. -/
theorem bswap16_spec (x : BitVec 16) :
    BitVec.ofInt 16 (Rust.asI64 (Rust.bswap 2 (x.toNat : Int))) = Sem.bswap x :=
  rbswap_spec 2 rfl (by decide) x

/-- `u64_bswap32` of a presented `i32` immediate is `Sem.bswap`. -/
theorem bswap32_spec (x : BitVec 32) :
    BitVec.ofInt 32 (Rust.asI64 (Rust.bswap 4 (x.toNat : Int))) = Sem.bswap x :=
  rbswap_spec 4 rfl (by decide) x

/-- `u64_bswap64` of a presented `i64` immediate is `Sem.bswap`. -/
theorem bswap64_spec (x : BitVec 64) :
    BitVec.ofInt 64 (Rust.asI64 (Rust.bswap 8 (x.toNat : Int))) = Sem.bswap x :=
  rbswap_spec 8 rfl (by decide) x

/-- `rule_bits` with the `u64_bswap*` folds as `Sem.bswap` (`bswap16_spec` …). -/
macro "rule_bits_bswap" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits, bne_iff_ne, ne_eq, toNat_eq_zero_iff] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | rfl
    | (first | apply some_val_congr | apply val_congr | skip
       opt_cases_ty <;> opt_widths <;> (try sem_simp) <;>
         (try simp only [bswap16_spec, bswap32_spec, bswap64_spec] at *) <;>
         first | rfl | kbv)))

set_option hygiene false in
/-- `rule_auto` with `rule_bits_bswap`. -/
macro "rule_auto_bswap " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_no_iflets
  rule_lhs hG
  all_goals (
    rule_rhs
    try dsimp only
    apply GraphOk.make_val hG (by opt_P)
    opt_node
    all_goals rule_bits_bswap)))

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:320`. -/
theorem ok_rule_cprop_320 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_320 := by
  rule_auto_xr rule_cprop_320

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:322`. -/
theorem ok_rule_cprop_322 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_322 := by
  rule_auto_xr rule_cprop_322

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:324`. -/
theorem ok_rule_cprop_324 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_324 := by
  rule_auto_xr rule_cprop_324

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:375`. -/
theorem ok_rule_cprop_375 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_375 := by
  rule_auto_bswap rule_cprop_375

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:377`. -/
theorem ok_rule_cprop_377 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_377 := by
  rule_auto_bswap rule_cprop_377

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:379`. -/
theorem ok_rule_cprop_379 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_379 := by
  rule_auto_bswap rule_cprop_379

end Opt.Proof
