import FV.Opt.Proof.RuleExtEmbed

/-!
# `opts/bitops.isle` (part 10): LLVM-style byte-swap idioms

Keep graph matching separate from bit-vector reasoning. An opcode-indexed decoder
postpones the binary/`iconcat` choice until the opcode is known, avoiding a product
of impossible branches across the tree. Only the two closed-width identities are
bit-blasted; the rule proofs apply them after resolving immediate operands.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

-- Implicit matching must identify `.i32.width`/`.i64.width` with literal bit-vector widths.
attribute [local implicit_reducible] Ty.width

/-- The balanced 32-bit shift/mask/or tree in `bitops.isle:157`. -/
def llvmBswap32 (x : BitVec 32) : BitVec 32 :=
  ((x <<< 24) ||| ((x &&& 0xff00) <<< 8)) |||
    (((x >>> 8) &&& 0xff00) ||| (x >>> 24))

/-- The balanced 64-bit shift/mask/or tree in `bitops.isle:170`. -/
def llvmBswap64 (x : BitVec 64) : BitVec 64 :=
  (((x <<< 56) ||| ((x &&& 0xff00) <<< 40)) |||
    (((x &&& 0xff0000) <<< 24) ||| ((x &&& 0xff000000) <<< 8))) |||
  ((((x >>> 8) &&& 0xff000000) ||| ((x >>> 24) &&& 0xff0000)) |||
    (((x >>> 40) &&& 0xff00) ||| (x >>> 56)))

/-- Byte extraction and placement agree with the modeled byte reversal. -/
theorem llvmBswap32_eq (x : BitVec 32) : llvmBswap32 x = Sem.bswap x := by
  unfold llvmBswap32
  bswap_unroll
  bv_decide

/-- Eight disjoint byte lanes, with the source's balanced `bor` association. -/
theorem llvmBswap64_eq (x : BitVec 64) : llvmBswap64 x = Sem.bswap x := by
  unfold llvmBswap64
  bswap_unroll
  bv_decide

-- Distinct bytes exercise every lane; the second input places the high bit in
-- both end bytes, including the logical-right-shift sign boundary.
example : llvmBswap32 0x12345678 = 0x78563412 ∧
    Sem.bswap (0x12345678#32) = 0x78563412 := by decide
example : llvmBswap32 0x80fe0180 = 0x8001fe80 ∧
    Sem.bswap (0x80fe0180#32) = 0x8001fe80 := by decide
example : llvmBswap64 0x0123456789abcdef = 0xefcdab8967452301 ∧
    Sem.bswap (0x0123456789abcdef#64) = 0xefcdab8967452301 := by decide
example : llvmBswap64 0x80fe7f0102aa5580 = 0x8055aa02017ffe80 ∧
    Sem.bswap (0x80fe7f0102aa5580#64) = 0x8055aa02017ffe80 := by decide

/-- Keep the instruction alternative symbolic until its opcode is matched. -/
def byteSwapBinaryNode (slot : Option BinaryOp) (t : Ty) (x y : ValueId) : Inst :=
  match slot with
  | some op => .binary op t x y
  | none => .iconcat t x y

def byteSwapBinaryOpcode (slot : Option BinaryOp) : Nat :=
  match slot with
  | some op => binaryIdx op
  | none => 155

/-- Unlike `ofInst_binary`, this inversion does not immediately split every node
into binary and `iconcat` branches. The fixed opcode resolves the witness first. -/
theorem ofInst_byteSwapBinary {i : Inst} {fs : List V} :
    ofInst i = some (.data 53 2 fs) ↔
      ∃ slot t x y, i = byteSwapBinaryNode slot t x y ∧
        fs = [opcode (byteSwapBinaryOpcode slot), .values [.value x, .value y]] := by
  constructor
  · intro h
    rcases ofInst_binary.mp h with ⟨op, t, x, y, rfl, rfl⟩ | ⟨t, x, y, rfl, rfl⟩
    · exact ⟨some op, t, x, y, rfl, rfl⟩
    · exact ⟨none, t, x, y, rfl, rfl⟩
  · rintro ⟨slot, t, x, y, rfl, rfl⟩
    cases slot <;> rfl

theorem byteSwapBinaryOpcode_eq (slot : Option BinaryOp) (n : Nat) :
    byteSwapBinaryOpcode slot = n ↔
      (slot = none ∧ n = 155) ∨ ∃ op, slot = some op ∧ binaryIdx op = n := by
  cases slot <;> simp [byteSwapBinaryOpcode, eq_comm]

-- Both decoder alternatives are inhabited; ordinary binary opcodes remain distinct.
example : ofInst (.binary .bor .i64 0 1) =
    some (.data 53 2 [opcode (byteSwapBinaryOpcode (some .bor)), .values [.value 0, .value 1]]) := rfl
example : ofInst (.iconcat .i64 0 1) =
    some (.data 53 2 [opcode (byteSwapBinaryOpcode none), .values [.value 0, .value 1]]) := rfl
example : byteSwapBinaryOpcode (some .bor) = binaryIdx .bor ∧
    byteSwapBinaryOpcode (some .bor) ≠ 155 ∧ byteSwapBinaryOpcode none = 155 := by decide

attribute [local opt_match 1100] ofInst_byteSwapBinary
attribute [local opt_match] byteSwapBinaryOpcode_eq byteSwapBinaryNode

/-- Normalize immediate encodings and intermediate shift results before applying the
closed-width identities. Normalize both numeral encodings, without unfolding `bswap`. -/
macro "byte_swap_bits" : tactic => `(tactic| (
  simp only [asU64_imm64OfBits (t := .i32) (by decide),
    asU64_imm64OfBits (t := .i64) (by decide),
    ← Int.cast_ofNat_Int, Int.natCast_inj, toNat_eq_iff_ofNat] at *
  opt_destruct
  all_goals subst_vars
  all_goals simp only [Sem.shift, Option.some.injEq] at *
  all_goals subst_vars
  all_goals (
    first | apply some_val_congr | apply val_congr | skip
    opt_cases_val <;> opt_cases_ty <;> opt_widths
    all_goals simp only [Sem.binary, Sem.unary, Sem.shift, Sem.band, Sem.bor,
      Sem.ishl, Sem.ushr, Sem.shiftAmt]
    all_goals simp only [← llvmBswap32_eq, ← llvmBswap64_eq, llvmBswap32, llvmBswap64,
      Ty.width, BitVec.ofNat_eq_ofNat, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod])))

set_option hygiene false in
macro "byte_swap_finish" : tactic => `(tactic| (
  try dsimp only
  apply GraphOk.make_val hG (by opt_P)
  simp only [evalNode_unary, Clif.Frame.regs]
  refine ⟨_, by opt_den_x, ?_⟩
  byte_swap_bits))

open Lean Elab Tactic in
elab "byte_swap_noinfo " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

set_option maxHeartbeats 4000000 in
/-- `bitops.isle:157`: the 32-bit LLVM byte-swap tree. -/
theorem ok_rule_bitops_157 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_157 := by
  byte_swap_noinfo
    rule_intro rule_bitops_157
    rule_no_iflets
    rule_lhs_g hG
    all_goals (rule_rhs_x; byte_swap_finish)

set_option maxHeartbeats 4000000 in
/-- `bitops.isle:170`: the 64-bit LLVM byte-swap tree. -/
theorem ok_rule_bitops_170 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_170 := by
  byte_swap_noinfo
    rule_intro rule_bitops_170
    rule_no_iflets
    rule_lhs_g hG
    all_goals (rule_rhs_x; byte_swap_finish)

end Opt.Proof
