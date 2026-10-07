import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/cprop.isle` (part 3): proven `simplify` rules (R0)

320, 322, 324 (reassociating shifts of a constant) by `rule_auto_xr`; 375, 377, 379 (folding
`bswap` of a constant) by `rule_auto_bswap`, with the helper specs `bswap16_spec`,
`bswap32_spec`, `bswap64_spec` (`u64_bswap16/32/64` of a presented immediate is `Sem.bswap`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

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

/-- `u64_bswap16` of a presented `i16` immediate is `Sem.bswap`. -/
theorem bswap16_spec (x : BitVec 16) :
    BitVec.ofInt 16 (Rust.asI64 (Rust.bswap 2 (x.toNat : Int))) = Sem.bswap x := by
  rw [ofInt_asI64 (by decide)]
  simp only [Rust.bswap, asU64_natCast_toNat (by decide : (16 : Nat) ≤ 64)]
  simp only [List.range_succ, List.range_zero, List.foldl, List.nil_append, List.cons_append,
    Nat.reduceMul, Nat.mod_eq_of_lt x.isLt]
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, ofInt_byte (by decide : 8 ≤ 16)]
  simp only [Sem.bswap, List.range_succ, List.range_zero, List.foldl, List.nil_append, List.cons_append,
    Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  bv_decide

/-- `u64_bswap32` of a presented `i32` immediate is `Sem.bswap`. -/
theorem bswap32_spec (x : BitVec 32) :
    BitVec.ofInt 32 (Rust.asI64 (Rust.bswap 4 (x.toNat : Int))) = Sem.bswap x := by
  rw [ofInt_asI64 (by decide)]
  simp only [Rust.bswap, asU64_natCast_toNat (by decide : (32 : Nat) ≤ 64)]
  simp only [List.range_succ, List.range_zero, List.foldl, List.nil_append, List.cons_append,
    Nat.reduceMul, Nat.mod_eq_of_lt x.isLt]
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, ofInt_byte (by decide : 8 ≤ 32)]
  simp only [Sem.bswap, List.range_succ, List.range_zero, List.foldl, List.nil_append, List.cons_append,
    Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  bv_decide

/-- `u64_bswap64` of a presented `i64` immediate is `Sem.bswap`. -/
theorem bswap64_spec (x : BitVec 64) :
    BitVec.ofInt 64 (Rust.asI64 (Rust.bswap 8 (x.toNat : Int))) = Sem.bswap x := by
  rw [ofInt_asI64 (by decide)]
  simp only [Rust.bswap, asU64_natCast_toNat (by decide : (64 : Nat) ≤ 64)]
  simp only [List.range_succ, List.range_zero, List.foldl, List.nil_append, List.cons_append,
    Nat.reduceMul, Nat.mod_eq_of_lt x.isLt]
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, ofInt_byte (by decide : 8 ≤ 64)]
  simp only [Sem.bswap, List.range_succ, List.range_zero, List.foldl, List.nil_append, List.cons_append,
    Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  bv_decide

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
         first | rfl | bv_decide (config := { timeout := 120 }))))

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
