import FV.Backend.Proof.Encode

/-!
# Arm meaning of allocated `MInst`s, through the actual pipeline

`MInst.sem m s` runs one allocated machine instruction the way the backend emits it:
`MInst.lines` (the `emit.rs` expansion, `FV/Backend/Asm.lean`) gives `Insn`s, each `Insn`
is executed by M5's `Insn.sem` (= `exec_inst` of `Insn.toArmInst`, `FV/Backend/Proof/Encode.lean`).
M5's `Insn.stepi_eq_sem` relates `Insn.sem` to `stepi` on the encoded word, so these lemmas
compose with the encoder theorem without re-proving any encoding fact.

Registers: allocation is modelled as a renaming `alloc ρ` of vregs to `x (ρ n)`; the
M6 checker theorem (`docs/contracts/regalloc.md`) is what justifies a given renaming per
instruction. `X k s` is the 64-bit contents of `x k`.
-/

namespace Backend.Proof

open Arm Backend

/-- Environment for straight-line code (no instruction here reads a label or the PC). -/
def isemEnv0 : Env := ⟨0, fun _ => none⟩

/-- One line of expanded code (only instructions; labels/data words are not executable). -/
def lineSem (s : ArmState) : Line → Except String ArmState
  | .ins i _ => Insn.sem isemEnv0 i s
  | _ => .error "not an instruction"

/-- Arm meaning of one allocated `MInst`: expansion, `Insn.toArmInst`, `exec_inst`. -/
def MInst.sem (m : MInst) (s : ArmState) : Except String ArmState := do
  let (ls, _) ← m.lines default {}
  ls.foldlM lineSem s

/-- Arm meaning of a straight-line `MInst` sequence. -/
def seqSem (ms : List MInst) (s : ArmState) : Except String ArmState :=
  ms.foldlM (fun s m => MInst.sem m s) s

/-- Register allocation as a renaming: vreg `n` lives in `x (ρ n)`. -/
def alloc (ρ : Nat → Nat) : Reg → Reg
  | .vreg n _ => .x (ρ n)
  | r => r

/-- The state field of `x k` (`k = 31` is SP). -/
abbrev gpr (k : Nat) : StateField := .GPR (BitVec.ofNat 5 k)

/-- Contents of `x k`. -/
abbrev X (k : Nat) (s : ArmState) : BitVec 64 := r (gpr k) s

/-- `s'` differs from `s` at most in the x-registers `ds`, the PC, and (if `fl`) NZCV. -/
def Frame (ds : List Nat) (fl : Bool) (s s' : ArmState) : Prop :=
  (∀ k, k < 32 → k ∉ ds → X k s' = X k s) ∧
  (∀ i, r (.SFP i) s' = r (.SFP i) s) ∧
  (fl = false → ∀ f, r (.FLAG f) s' = r (.FLAG f) s) ∧
  r .ERR s' = r .ERR s ∧
  (∀ a, read_mem a s' = read_mem a s)

theorem ofNat5_ne_31 {k : Nat} (h : k ≤ 30) : BitVec.ofNat 5 k ≠ 31#5 := by
  intro e
  have := congrArg BitVec.toNat e
  simp [Nat.mod_eq_of_lt (show k < 32 by omega)] at this
  omega

theorem ofNat5_inj {j k : Nat} (hj : j < 32) (hk : k < 32) (h : BitVec.ofNat 5 j = BitVec.ofNat 5 k) :
    j = k := by
  have := congrArg BitVec.toNat h
  simpa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] using this

/-! ## One lemma per emitted instruction form (registers symbolic, `≤ 30`) -/


/-- The two bitmask immediates the probe's rules use (UBFM #0, #7 = `uxtb`; AND #7). LNSym's
`decode_bit_masks` goes through `highest_set_bit`, whose kernel reduction is too deep, so these
two closed facts are evaluated by `native_decide`. -/
theorem dbm_uxtb : decode_bit_masks 0#1 7#6 0#6 false 32 = some (255#32, 255#32) := by native_decide
theorem dbm_and7 : decode_bit_masks 0#1 2#6 0#6 true 32 = some (7#32, 7#32) := by native_decide

section Insns
variable {d a b : Nat} (hd : d ≤ 30) (ha : a ≤ 30) (hb : b ≤ 30) (s : ArmState)

local macro "sem_simp" : tactic => `(tactic|
  simp (config := {decide := true}) [MInst.sem, MInst.lines, lineSem, Insn.sem, Insn.toArmInst,
    Insn.armFields, Reg.encZR, Reg.encSP, ALUOp.addSub?, ALUOp.logic?, b1, OperandSize.is64,
    exec_inst, ArmInst.norm, DPR.exec_add_sub_shifted_reg, DPI.exec_add_sub_imm, decode_shift,
    shift_reg, read_gpr_zr, write_gpr_zr, fst_AddWithCarry_eq_add, fst_AddWithCarry_eq_sub_neg,
    ofNat5_ne_31, uField, bitmaskEnc?, DPI.exec_logical_imm, DPI.exec_bitfield,
    DPR.exec_data_processing_two_source, DPR.exec_conditional_select, Insn.armFields.dp2,
    dbm_uxtb, dbm_and7, DPR.exec_data_processing_shift, *] <;> rfl)

include hd ha hb in
theorem sem_add32 : MInst.sem (.aluRRR .add .size32 (.x d) (.x a) (.x b)) s =
    .ok (write_gpr 32 (BitVec.ofNat 5 d) (read_gpr 32 (BitVec.ofNat 5 a) s + read_gpr 32 (BitVec.ofNat 5 b) s)
      (write_pc (read_pc s + 4#64) s)) := by
  sem_simp

include hd ha hb in
theorem sem_add64 : MInst.sem (.aluRRR .add .size64 (.x d) (.x a) (.x b)) s =
    .ok (write_gpr 64 (BitVec.ofNat 5 d) (read_gpr 64 (BitVec.ofNat 5 a) s + read_gpr 64 (BitVec.ofNat 5 b) s)
      (write_pc (read_pc s + 4#64) s)) := by
  sem_simp

include hd ha in
theorem sem_addi32 (i : Imm12) (hi : i.bits < 4096) : MInst.sem (.aluRRImm12 .add .size32 (.x d) (.x a) i) s =
    .ok (write_gpr 32 (BitVec.ofNat 5 d) (read_gpr 32 (BitVec.ofNat 5 a) s +
      BitVec.setWidth 32 (if i.shift12 = false then 0#52 ++ BitVec.ofNat 12 i.bits
        else (0#52 ++ BitVec.ofNat 12 i.bits) <<< 12))
      (write_pc (read_pc s + 4#64) s)) := by
  sem_simp

include hd ha in
theorem sem_addi64 (i : Imm12) (hi : i.bits < 4096) : MInst.sem (.aluRRImm12 .add .size64 (.x d) (.x a) i) s =
    .ok (write_gpr 64 (BitVec.ofNat 5 d) (read_gpr 64 (BitVec.ofNat 5 a) s +
      BitVec.setWidth 64 (if i.shift12 = false then 0#52 ++ BitVec.ofNat 12 i.bits
        else (0#52 ++ BitVec.ofNat 12 i.bits) <<< 12))
      (write_pc (read_pc s + 4#64) s)) := by
  sem_simp

include ha hb in
theorem sem_cmp32 : MInst.sem (.aluRRR .subS .size32 .xzr (.x a) (.x b)) s =
    .ok (write_pstate (AddWithCarry (read_gpr 32 (BitVec.ofNat 5 a) s)
      (~~~read_gpr 32 (BitVec.ofNat 5 b) s) 1#1).snd (write_pc (read_pc s + 4#64) s)) := by
  sem_simp

include ha hb in
theorem sem_cmp64 : MInst.sem (.aluRRR .subS .size64 .xzr (.x a) (.x b)) s =
    .ok (write_pstate (AddWithCarry (read_gpr 64 (BitVec.ofNat 5 a) s)
      (~~~read_gpr 64 (BitVec.ofNat 5 b) s) 1#1).snd (write_pc (read_pc s + 4#64) s)) := by
  sem_simp

include hd in
theorem sem_cset (c : Cond) (hc : c ≠ .al ∧ c ≠ .nv) : MInst.sem (.cset (.x d) c) s =
    .ok (write_gpr 64 (BitVec.ofNat 5 d) (if ConditionHolds c.invert.bits s then 0#64 else 1#64)
      (write_pc (read_pc s + 4#64) s)) := by
  cases c <;> simp at hc <;> sem_simp

theorem bitmaskEnc_7 : bitmaskEnc? false 7 = some (0#1, 0#6, 2#6) := by rfl

include hd ha in
theorem arm_uxtb32 : Insn.toArmInst isemEnv0 (.bfm .uBfm false (.x d) (.x a) 0 7) =
    .ok (.DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 0, imms := 7, Rn := BitVec.ofNat 5 a, Rd := BitVec.ofNat 5 d })) := by
  simp (config := {decide := true}) [Insn.toArmInst, Insn.armFields, Reg.encZR, b1, hd, ha,
    ArmInst.norm]
  rfl

include hd ha in
theorem arm_and7_32 : Insn.toArmInst isemEnv0 (.logicImm .and false (.x d) (.x a) 7) =
    .ok (.DPI (.Logical_imm { sf := 0, opc := 0, N := 0, immr := 0, imms := 2, Rn := BitVec.ofNat 5 a, Rd := BitVec.ofNat 5 d })) := by
  simp (config := {decide := true}) [Insn.toArmInst, Insn.armFields, bitmaskEnc_7, Reg.encZR,
    Reg.encSP, ALUOp.logic?, b1, hd, ha, ArmInst.norm]
  rfl

include hd ha in
theorem insn_uxtb32 : Insn.sem isemEnv0 (.bfm .uBfm false (.x d) (.x a) 0 7) s =
    .ok (let v := BitVec.ror (read_gpr 32 (BitVec.ofNat 5 a) s) 0 &&& 255#32 &&& 255#32
      write_pc (read_pc (write_gpr 32 (BitVec.ofNat 5 d) v s) + 4#64) (write_gpr 32 (BitVec.ofNat 5 d) v s)) := by
  have hl : BitVec.lsb (7#6) 5 = 0#1 := by decide
  rw [Insn.sem, arm_uxtb32 hd ha]
  show Except.ok (exec_inst _ s) = _
  simp only [exec_inst, DPI.exec_bitfield]
  simp
  simp only [hl, dbm_uxtb, read_gpr_zr, write_gpr_zr, ofNat5_ne_31 hd, ofNat5_ne_31 ha, ite_true,
    ne_eq, not_false_eq_true]

include hd ha in
theorem sem_uxtb32 : MInst.sem (.extend (.x d) (.x a) false 8 32) s =
    .ok (let v := BitVec.ror (read_gpr 32 (BitVec.ofNat 5 a) s) 0 &&& 255#32 &&& 255#32
      write_pc (read_pc (write_gpr 32 (BitVec.ofNat 5 d) v s) + 4#64) (write_gpr 32 (BitVec.ofNat 5 d) v s)) := by
  have h : MInst.sem (.extend (.x d) (.x a) false 8 32) s = Insn.sem isemEnv0 (.bfm .uBfm false (.x d) (.x a) 0 7) s := by
    simp [MInst.sem, MInst.lines, lineSem]
  rw [h, insn_uxtb32 hd ha]

include hd ha in
theorem insn_and7_32 : Insn.sem isemEnv0 (.logicImm .and false (.x d) (.x a) 7) s =
    .ok (write_gpr 32 (BitVec.ofNat 5 d) (read_gpr 32 (BitVec.ofNat 5 a) s &&& 7#32)
      (write_pc (read_pc s + 4#64) s)) := by
  have hl : BitVec.lsb (2#6) 5 = 0#1 := by decide
  rw [Insn.sem, arm_and7_32 hd ha]
  show Except.ok (exec_inst _ s) = _
  simp only [exec_inst, DPI.exec_logical_imm]
  simp
  simp only [hl, dbm_and7, read_gpr_zr, write_gpr_zr, ofNat5_ne_31 hd, ofNat5_ne_31 ha, ite_true,
    ne_eq, not_false_eq_true]
  simp [DPI.decode_op, DPI.exec_logical_imm_op]

include hd ha in
theorem sem_and7_32 : MInst.sem (.aluRRImmLogic .and .size32 (.x d) (.x a) ⟨7, .size32⟩) s =
    .ok (write_gpr 32 (BitVec.ofNat 5 d) (read_gpr 32 (BitVec.ofNat 5 a) s &&& 7#32)
      (write_pc (read_pc s + 4#64) s)) := by
  have h : MInst.sem (.aluRRImmLogic .and .size32 (.x d) (.x a) ⟨7, .size32⟩) s =
      Insn.sem isemEnv0 (.logicImm .and false (.x d) (.x a) 7) s := by
    simp [MInst.sem, MInst.lines, lineSem, mask64, OperandSize.is64]; rfl
  rw [h, insn_and7_32 hd ha]

include hd ha hb in
theorem sem_lsr32 : MInst.sem (.aluRRR .lsr .size32 (.x d) (.x a) (.x b)) s =
    .ok (let v := read_gpr 32 (BitVec.ofNat 5 a) s >>> ((read_gpr 32 (BitVec.ofNat 5 b) s).toInt % 32 % 64).toNat
      write_pc (read_pc (write_gpr 32 (BitVec.ofNat 5 d) v s) + 4#64) (write_gpr 32 (BitVec.ofNat 5 d) v s)) := by
  sem_simp

end Insns

end Backend.Proof
