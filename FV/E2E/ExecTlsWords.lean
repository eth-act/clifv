import FV.E2E.BinCheck

/-! # lld's local-exec TLS words on the Arm model (T1)

rust-lld relaxes Cranelift's TLSDESC sequence (`adrp`, `ldr`, `add`, `blr`) of a static
executable to local exec: `movz x0, #hi, lsl #16`, `movk x0, #lo`, `nop`, `nop`, where
`hi * 2^16 + lo` is the variable's offset from the thread pointer (`BinCheck.RelocOk`'s
`tlsDescAdrPage21` clause checks these words, `movzW`/`movkW`/`nopW`, against `TpOff`). This file
states what the Arm model does on them: each decodes to an explicit record (`movzI`, `movkI`,
`nopI`) and `Arm.exec_inst` of the record writes `x0` (resp. only the pc). `movz_movk_val`: the
two words together put the offset `v < 2^32` into `x0`.
-/

namespace E2E.ExecWords

open E2E BinCheck Backend

private theorem toNat_app' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-! ## Instruction records -/

/-- `MOVZ X0, #imm, LSL #16`, as decoded. -/
def movzI (imm : Nat) : Arm.ArmInst :=
  .DPI (.Move_wide_imm { sf := 1#1, opc := 2#2, hw := 1#2, imm16 := BitVec.ofNat 16 imm, Rd := 0#5 })

/-- `MOVK X0, #imm`, as decoded. -/
def movkI (imm : Nat) : Arm.ArmInst :=
  .DPI (.Move_wide_imm { sf := 1#1, opc := 3#2, hw := 0#2, imm16 := BitVec.ofNat 16 imm, Rd := 0#5 })

/-- `NOP`, as decoded. -/
def nopI : Arm.ArmInst := .BR (.Hints { CRm := 0#4, op2 := 0#3 })

/-! ## Decoding -/

theorem movzW_bits {imm : Nat} (h : imm < 2 ^ 16) : movzW 0 imm = armBits (movzI imm) := by
  apply BitVec.eq_of_toNat_eq
  simp only [movzW, movzI, armBits, toNat_app', BitVec.toNat_ofNat]
  omega

theorem movkW_bits {imm : Nat} (h : imm < 2 ^ 16) : movkW 0 imm = armBits (movkI imm) := by
  apply BitVec.eq_of_toNat_eq
  simp only [movkW, movkI, armBits, toNat_app', BitVec.toNat_ofNat]
  omega

theorem nopW_bits : nopW = armBits nopI := by decide

/-! ## Execution -/

/-- `movz`'s value: `imm << 16`. -/
theorem movz_val {imm : Nat} (h : imm < 2 ^ 16) :
    Arm.BitVec.partInstall 16 16 (BitVec.ofNat 16 imm) (0#64) = BitVec.ofNat 64 (imm * 2 ^ 16) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Arm.BitVec.partInstall, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true,
    Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat,
    Nat.testBit_mul_two_pow]
  by_cases h16 : 16 ≤ i
  · by_cases h1 : i - 16 < 16
    · simp [h16, h1, show ¬ i < 16 by omega, show i - 16 < 64 by omega]
    · simp [h16, h1, show ¬ i < 16 by omega]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
  · simp [h16, show i < 16 by omega]

/-- **`movzW 0 imm`**: `x0 := imm << 16`. -/
theorem movzW_exec {imm : Nat} (h : imm < 2 ^ 16) :
    Arm.decode_raw_inst (movzW 0 imm) = some (movzI imm) ∧
      ∀ s, Arm.exec_inst (movzI imm) s = Arm.w .PC (Arm.r .PC s + 4)
        (Arm.w (.GPR 0#5) (BitVec.ofNat 64 (imm * 2 ^ 16)) s) := by
  refine ⟨by rw [movzW_bits h, decode_armBits]; rfl, fun s => ?_⟩
  simp only [movzI, Arm.exec_inst, Arm.DPI.exec_move_wide_imm, Arm.write_gpr_zr, Arm.write_gpr,
    Arm.write_pc, Arm.read_pc]
  simp [← movz_val h]

/-- **`movkW 0 imm`**: the low 16 bits of `x0 := imm`. -/
theorem movkW_exec {imm : Nat} (h : imm < 2 ^ 16) :
    Arm.decode_raw_inst (movkW 0 imm) = some (movkI imm) ∧
      ∀ s, Arm.exec_inst (movkI imm) s = Arm.w .PC (Arm.r .PC s + 4)
        (Arm.w (.GPR 0#5) (Arm.BitVec.partInstall 0 16 (BitVec.ofNat 16 imm)
          (Arm.r (.GPR 0#5) s)) s) := by
  refine ⟨by rw [movkW_bits h, decode_armBits]; rfl, fun s => ?_⟩
  simp only [movkI, Arm.exec_inst, Arm.DPI.exec_move_wide_imm, Arm.write_gpr_zr, Arm.write_gpr,
    Arm.read_gpr_zr, Arm.read_gpr, Arm.write_pc, Arm.read_pc]
  simp

/-- **`nopW`**: only the pc advances. -/
theorem nopW_exec : Arm.decode_raw_inst nopW = some nopI ∧
    ∀ s, Arm.exec_inst nopI s = Arm.w .PC (Arm.r .PC s + 4) s := by
  refine ⟨by rw [nopW_bits, decode_armBits]; rfl, fun s => ?_⟩
  simp [nopI, Arm.exec_inst, Arm.BR.exec_hints, Arm.write_pc, Arm.read_pc]

/-- `movz x0, #(v / 2^16), lsl #16; movk x0, #(v % 2^16)` put `v < 2^32` into `x0`. -/
theorem movz_movk_val {v : Nat} (h : v < 2 ^ 32) :
    Arm.BitVec.partInstall 0 16 (BitVec.ofNat 16 (v % 2 ^ 16))
      (BitVec.ofNat 64 (v / 2 ^ 16 * 2 ^ 16)) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Arm.BitVec.partInstall, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true,
    Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat,
    Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have := h
  by_cases h16 : i < 16
  · simp [h16, hi, show ¬ 16 ≤ i by omega]
  · simp [h16, hi, show 16 ≤ i by omega, show i - 16 + 16 = i by omega]

end E2E.ExecWords
