import FV.E2E.BinCheck

/-! # The resolved instruction words on the Arm model (M9)

The binary checks (`FV/E2E/BinCheck.lean`: `RelocOk`, `PairOk`) accept, at a relocated site,
the words `blW d`, `adrpW rd dp`, `addW rd rn imm`, `ldrW rt rn imm` of the executable. This
file states what the Lean Arm model does on them: each decodes (`Arm.decode_raw_inst`) to an
explicit instruction record (`blI`, `adrpI`, `addI`, `ldrI`), and `Arm.exec_inst` of the record
is the instruction's effect on registers and pc. `blr_exec` is the same for the compiled
`blr xn`. The address lemmas (`adrp_page`, `adrp_add_val`, `adrp_ldr_addr`) show that the
`adrp`+`add` / `adrp`+`ldr` pairs `PairOk` accepts compute the target / the GOT slot address.
-/

namespace E2E.ExecWords

open E2E BinCheck Backend

/-! ## Helpers -/

private theorem toNat_app {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

private theorem imm21_cast (d : Int) : (imm21 d : Int) = d % 2 ^ 21 :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

private theorem ofNat5_ne31' {n : Nat} (hn : n < 31) : BitVec.ofNat 5 n ≠ 31#5 := by
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

/-- Clearing the low 12 bits (`ADRP`'s page of the pc). -/
theorem partInstall_page (x : BitVec 64) :
    Arm.BitVec.partInstall 0 12 0#12 x = BitVec.ofNat 64 (x.toNat / 4096 * 4096) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e : x.toNat / 4096 * 4096 = x.toNat / 2 ^ 12 * 2 ^ 12 := rfl
  simp only [Arm.BitVec.partInstall, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true,
    Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Bool.not_and, Bool.not_not,
    BitVec.getLsbD_ofNat, e, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h : i < 12
  · simp [h, hi, show ¬ 12 ≤ i by omega]
  · simp [h, show 12 ≤ i by omega, show i - 12 + 12 = i by omega, BitVec.testBit_toNat]

/-! ## Instruction records -/

/-- `ADRP Xrd, page(pc) + dp pages`, as decoded. -/
def adrpI (rd : Nat) (dp : Int) : Arm.ArmInst :=
  .DPI (.PC_rel_addressing
    { op := 1#1, immlo := BitVec.ofNat 2 (imm21 dp % 4), immhi := BitVec.ofNat 19 (imm21 dp / 4),
      Rd := BitVec.ofNat 5 rd })

/-- `ADD Xrd, Xrn, #imm`, as decoded. -/
def addI (rd rn imm : Nat) : Arm.ArmInst :=
  .DPI (.Add_sub_imm
    { sf := 1#1, op := 0#1, S := 0#1, sh := 0#1, imm12 := BitVec.ofNat 12 imm,
      Rn := BitVec.ofNat 5 rn, Rd := BitVec.ofNat 5 rd })

/-- `LDR Xrt, [Xrn, #8 * imm]`, as decoded. -/
def ldrI (rt rn imm : Nat) : Arm.ArmInst :=
  .LDST (.Reg_unsigned_imm
    { size := 3#2, V := 0#1, opc := 1#2, imm12 := BitVec.ofNat 12 imm,
      Rn := BitVec.ofNat 5 rn, Rt := BitVec.ofNat 5 rt })

/-- `BL pc + d`, as decoded. -/
def blI (d : Int) : Arm.ArmInst :=
  .BR (.Uncond_branch_imm { op := 1#1, imm26 := BitVec.ofNat 26 (d / 4 % 2 ^ 26).toNat })

/-! ## Decoding -/

theorem adrpW_bits {rd : Nat} {dp : Int} (hrd : rd < 31) : adrpW rd dp = armBits (adrpI rd dp) := by
  have hk : imm21 dp < 2 ^ 21 := by have := imm21_cast dp; omega
  apply BitVec.eq_of_toNat_eq
  simp only [adrpW, adrLike, adrpI, armBits, toNat_app, BitVec.toNat_ofNat]
  generalize imm21 dp = k at hk ⊢
  have h1 : k % 4 < 4 := Nat.mod_lt _ (by decide)
  have h2 : k / 4 < 2 ^ 19 := by omega
  generalize k % 4 = lo at *
  generalize k / 4 = hi at *
  omega

theorem addW_bits {rd rn imm : Nat} (hrd : rd < 31) (hrn : rn < 31) (himm : imm < 4096) :
    addW rd rn imm = armBits (addI rd rn imm) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addW, addI, armBits, toNat_app, BitVec.toNat_ofNat]
  omega

theorem ldrW_bits {rt rn imm : Nat} (hrt : rt < 31) (hrn : rn < 31) (himm : imm < 4096) :
    ldrW rt rn imm = armBits (ldrI rt rn imm) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ldrW, ldrI, armBits, toNat_app, BitVec.toNat_ofNat]
  omega

theorem blW_bits (d : Int) : blW d = armBits (blI d) := by
  have : ((d / 4 % 2 ^ 26).toNat : Int) = d / 4 % 2 ^ 26 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  apply BitVec.eq_of_toNat_eq
  simp only [blW, blI, armBits, toNat_app, BitVec.toNat_ofNat]
  omega

/-! ## Execution -/

/-- `ADRP`'s immediate is `dp` pages when `dp` is in range. -/
theorem sext_adrp {dp : Int} (h : inR (-2 ^ 20) (2 ^ 20) dp = true) :
    BitVec.signExtend 64 (BitVec.ofNat 19 (imm21 dp / 4) ++ BitVec.ofNat 2 (imm21 dp % 4) ++
      BitVec.zero 12) = BitVec.ofInt 64 (dp * 4096) := by
  simp only [inR, Bool.and_eq_true, decide_eq_true_eq] at h
  have hk := imm21_cast dp
  unfold BitVec.signExtend
  congr 1
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [toNat_app, BitVec.toNat_ofNat, BitVec.zero_eq]
  split <;> omega

theorem adrp_val (pc : BitVec 64) (dp : Int) :
    BitVec.ofNat 64 (pc.toNat / 4096 * 4096) + BitVec.ofInt 64 (dp * 4096) =
      BitVec.ofInt 64 ((pageOf pc.toNat + dp) * 4096) := by
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  simp only [pageOf]
  omega

/-- **`adrpW`**: `Xrd := page(pc) + dp pages`. -/
theorem adrpW_exec {rd : Nat} {dp : Int} (hrd : rd < 31)
    (hdp : BinCheck.inR (-2 ^ 20) (2 ^ 20) dp = true) :
    Arm.decode_raw_inst (BinCheck.adrpW rd dp) = some (adrpI rd dp) ∧
      ∀ s, Arm.exec_inst (adrpI rd dp) s = Arm.w .PC (Arm.r .PC s + 4)
        (Arm.w (.GPR (BitVec.ofNat 5 rd))
          (BitVec.ofInt 64 ((BinCheck.pageOf (Arm.r .PC s).toNat + dp) * 4096)) s) := by
  refine ⟨by rw [adrpW_bits hrd, decode_armBits]; rfl, fun s => ?_⟩
  simp only [adrpI, Arm.exec_inst, Arm.DPI.exec_pc_rel_addressing, Arm.write_gpr_zr,
    Arm.write_gpr, Arm.write_pc, Arm.read_pc, sext_adrp hdp, partInstall_page,
    show ¬ (1#1 : BitVec 1) = 0#1 by decide, ↓reduceIte, ne_eq, ofNat5_ne31' hrd,
    not_false_eq_true, BitVec.setWidth_eq, adrp_val]
  rfl

/-- **`addW`**: `Xrd := Xrn + imm`. -/
theorem addW_exec {rd rn imm : Nat} (hrd : rd < 31) (hrn : rn < 31) (himm : imm < 4096) :
    Arm.decode_raw_inst (BinCheck.addW rd rn imm) = some (addI rd rn imm) ∧
      ∀ s, Arm.exec_inst (addI rd rn imm) s = Arm.w .PC (Arm.r .PC s + 4)
        (Arm.w (.GPR (BitVec.ofNat 5 rd))
          (Arm.r (.GPR (BitVec.ofNat 5 rn)) s + BitVec.ofNat 64 imm) s) := by
  refine ⟨by rw [addW_bits hrd hrn himm, decode_armBits]; rfl, fun s => ?_⟩
  have e : 0#52 ++ BitVec.ofNat 12 imm = BitVec.ofNat 64 imm := by
    apply BitVec.eq_of_toNat_eq
    simp only [toNat_app, BitVec.toNat_ofNat]
    omega
  rw [Arm.w_of_w_commute (by simp)]
  simp [addI, Arm.exec_inst, Arm.DPI.exec_add_sub_imm, Arm.write_gpr_zr, Arm.write_gpr,
    Arm.write_pc, Arm.read_pc, Arm.read_gpr, Arm.fst_AddWithCarry_eq_add, ofNat5_ne31' hrd]
  rw [e]

/-- **`ldrW`**: `Xrt := mem[Xrn + 8 * imm]` (8 bytes). -/
theorem ldrW_exec {rt rn imm : Nat} (hrt : rt < 31) (hrn : rn < 31) (himm : imm < 4096) :
    Arm.decode_raw_inst (BinCheck.ldrW rt rn imm) = some (ldrI rt rn imm) ∧
      ∀ s, Arm.exec_inst (ldrI rt rn imm) s = Arm.w .PC (Arm.r .PC s + 4)
        (Arm.w (.GPR (BitVec.ofNat 5 rt))
          (Arm.read_mem_bytes 8
            (Arm.r (.GPR (BitVec.ofNat 5 rn)) s + BitVec.ofNat 64 (8 * imm)) s) s) := by
  refine ⟨by rw [ldrW_bits hrt hrn himm, decode_armBits]; rfl, fun s => ?_⟩
  have e : BitVec.setWidth 64 (BitVec.ofNat 12 imm) <<< 3 = BitVec.ofNat 64 (8 * imm) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  simp [ldrI, Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
    Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
    Arm.LDST.reg_imm_constrain_unpredictable, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr,
    ofNat5_ne31' hrn, ofNat5_ne31' hrt, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, e]
  rfl

/-- `BL`'s offset is `d` when `d` is in range. -/
theorem sext_bl {d : Int} (hd : blRange d = true) :
    BitVec.signExtend 64 (BitVec.ofNat 26 (d / 4 % 2 ^ 26).toNat ++ 0b00#2) = BitVec.ofInt 64 d := by
  simp only [blRange, inR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
  have hk : ((d / 4 % 2 ^ 26).toNat : Int) = d / 4 % 2 ^ 26 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  unfold BitVec.signExtend
  congr 1
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [toNat_app, BitVec.toNat_ofNat]
  split <;> omega

/-- **`blW`**: `x30 := pc + 4; pc := pc + d`. -/
theorem blW_exec {d : Int} (hd : BinCheck.blRange d = true) :
    Arm.decode_raw_inst (BinCheck.blW d) = some (blI d) ∧
      ∀ s, Arm.exec_inst (blI d) s = Arm.w .PC (Arm.r .PC s + BitVec.ofInt 64 d)
        (Arm.w (.GPR 30#5) (Arm.r .PC s + 4) s) := by
  refine ⟨by rw [blW_bits d, decode_armBits]; rfl, fun s => ?_⟩
  simp only [blI, Arm.exec_inst, Arm.BR.exec_uncond_branch_imm,
    Arm.BR.Uncond_branch_imm_inst.branch_taken_pc, sext_bl hd, Arm.write_gpr, Arm.write_pc,
    Arm.read_pc]
  simp

/-- **`blr xn`** (the compiled record, `toArmInst_blr`): `x30 := pc + 4; pc := xn`. -/
theorem blr_exec (rn : BitVec 5) (hrn : rn.toNat < 31) (s : Arm.ArmState) :
    Arm.exec_inst (.BR (.Uncond_branch_reg { opc := 1, op2 := 31, op3 := 0, Rn := rn, op4 := 0 })) s =
      Arm.w .PC (Arm.r (.GPR rn) s) (Arm.w (.GPR 30#5) (Arm.r .PC s + 4) s) := by
  have hne : rn ≠ 31#5 := by intro e; subst e; simp at hrn
  simp [Arm.exec_inst, Arm.BR.exec_uncond_branch_reg, Arm.read_gpr_zr, Arm.read_gpr,
    Arm.write_gpr, Arm.write_pc, Arm.read_pc, hne]

/-! ## Address arithmetic of the pairs -/

theorem adrp_page {P T : Nat} :
    BitVec.ofInt 64 ((pageOf P + (pageOf T - pageOf P)) * 4096) =
      BitVec.ofNat 64 (T / 4096 * 4096) := by
  rw [← BitVec.ofInt_natCast]
  congr 1
  simp only [pageOf]
  omega

/-- `adrp`+`add` (`PairOk`, not GOT) put the target `T` in `rd`. -/
theorem adrp_add_val {P T : Nat} :
    BitVec.ofInt 64 ((pageOf P + (pageOf T - pageOf P)) * 4096) + BitVec.ofNat 64 (T % 4096) =
      BitVec.ofNat 64 T := by
  rw [adrp_page]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `adrp`+`ldr` (`PairOk`, GOT) load from the slot `G`. -/
theorem adrp_ldr_addr {P G : Nat} (h8 : G % 8 = 0) :
    BitVec.ofInt 64 ((pageOf P + (pageOf G - pageOf P)) * 4096) +
      BitVec.ofNat 64 (8 * (G % 4096 / 8)) = BitVec.ofNat 64 G := by
  rw [adrp_page]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end E2E.ExecWords
