import FV.Backend.Proof.StockMemoryAccessArmFault
import FV.Backend.Encode

namespace Backend.Stock.Proof.MemoryFaults
open Backend
set_option autoImplicit false
set_option Elab.async false

/-- Encoding the actual unsigned i64 load preserves its physical registers and offset. -/
theorem load64_unsigned_encoding (env : Env) {base destination offset : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30)
    (aligned : offset % 8 = 0) (bounded : offset / 8 < 2^12) :
    (Insn.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)).toArmInst env =
      .ok (.LDST (.Reg_unsigned_imm {size := 3,V := 0,opc := 1,imm12 := BitVec.ofNat 12 (offset/8),Rn := BitVec.ofNat 5 base,Rt := BitVec.ofNat 5 destination})) := by
  simp [Insn.toArmInst,LoadOp.fields,LoadOp.bytes,ldstFields,Reg.encSP,Reg.encZR,uField,
    baseReg,destinationReg,aligned,bounded]

/-- Encoding the actual computed i64 store preserves its offset8 access. -/
theorem store64_eight_encoding (env : Env) {base value : Nat}
    (baseReg : base ≤ 30) (valueReg : value ≤ 30) :
    (Insn.store .store64 (.x value) (.unsignedOffset (.x base) 8)).toArmInst env =
      .ok (.LDST (.Reg_unsigned_imm {size := 3,V := 0,opc := 0,imm12 := 1,Rn := BitVec.ofNat 5 base,Rt := BitVec.ofNat 5 value})) := by
  simp [Insn.toArmInst,StoreOp.fields,StoreOp.bytes,ldstFields,Reg.encSP,Reg.encZR,uField,
    baseReg,valueReg]

private theorem physical_base_not_sp {base : Nat} (baseReg : base ≤ 30) :
    BitVec.ofNat 5 base ≠ 31#5 := by
  intro same
  have bad : base = 31 := by
    simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show base < 32 by omega)] using congrArg BitVec.toNat same
  omega

/-- The two actual source load offsets fault at the real encoded ARM instruction. -/
theorem encoded_load64_access_fault {env : Env} {base destination offset : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30)
    (sourceOffset : offset = 0 ∨ offset = 16) {ai : Arm.ArmInst} {mp : ArmFault.MemMap} {s : Arm.ArmState}
    (encoded : (Insn.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)).toArmInst env = .ok ai)
    (unmapped : ∃ k < 8,mp ((Arm.read_gpr 64 (BitVec.ofNat 5 base) s +
      BitVec.ofNat 64 offset) + BitVec.ofNat 64 k) = .none) : ArmFault.InstFaults mp ai s := by
  have ordinaryBase := physical_base_not_sp baseReg
  rcases sourceOffset with rfl | rfl
  · rw [load64_unsigned_encoding env baseReg destinationReg (by decide) (by decide)] at encoded
    cases encoded
    apply instFaults_unsigned_load64 ordinaryBase
    simpa only [Arm.LDST.Reg_offset.value] using unmapped
  · rw [load64_unsigned_encoding env baseReg destinationReg (by decide) (by decide)] at encoded
    cases encoded
    apply instFaults_unsigned_load64 ordinaryBase
    simpa only [Arm.LDST.Reg_offset.value] using unmapped

/-- The computed source store faults before the actual encoded instruction writes memory. -/
theorem encoded_store64_eight_access_fault {env : Env} {base value : Nat}
    (baseReg : base ≤ 30) (valueReg : value ≤ 30) {ai : Arm.ArmInst}
    {mp : ArmFault.MemMap} {s : Arm.ArmState}
    (encoded : (Insn.store .store64 (.x value) (.unsignedOffset (.x base) 8)).toArmInst env = .ok ai)
    (unmapped : ∃ k < 8,mp ((Arm.read_gpr 64 (BitVec.ofNat 5 base) s + 8#64) +
      BitVec.ofNat 64 k) = .none) : ArmFault.InstFaults mp ai s := by
  rw [store64_eight_encoding env baseReg valueReg] at encoded
  cases encoded
  apply instFaults_unsigned_store64 (physical_base_not_sp baseReg)
  simpa only [Arm.LDST.Reg_offset.value] using unmapped

/-- At the real decoded load, the existing fault machine takes its memory-fault step. -/
theorem encoded_load64_fault_step {env : Env} {base destination offset : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30)
    (sourceOffset : offset = 0 ∨ offset = 16) {ai : Arm.ArmInst} {mp : ArmFault.MemMap} {s : Arm.ArmState}
    (encoded : (Insn.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)).toArmInst env = .ok ai)
    (clean : Arm.read_err s = .None) (decoded : Concurrency.ArmFoot.decodeAt s = some ai)
    (unmapped : ∃ k < 8,mp ((Arm.read_gpr 64 (BitVec.ofNat 5 base) s +
      BitVec.ofNat 64 offset) + BitVec.ofNat 64 k) = .none) :
    ArmFault.stepF mp s = Arm.write_err ArmFault.memFault s := by
  exact ArmFault.stepF_fault ((ArmFault.faults_iff clean decoded).mpr
    (encoded_load64_access_fault baseReg destinationReg sourceOffset encoded unmapped))

/-- At the real decoded store, the existing fault machine stops before the write. -/
theorem encoded_store64_eight_fault_step {env : Env} {base value : Nat}
    (baseReg : base ≤ 30) (valueReg : value ≤ 30) {ai : Arm.ArmInst}
    {mp : ArmFault.MemMap} {s : Arm.ArmState}
    (encoded : (Insn.store .store64 (.x value) (.unsignedOffset (.x base) 8)).toArmInst env = .ok ai)
    (clean : Arm.read_err s = .None) (decoded : Concurrency.ArmFoot.decodeAt s = some ai)
    (unmapped : ∃ k < 8,mp ((Arm.read_gpr 64 (BitVec.ofNat 5 base) s + 8#64) +
      BitVec.ofNat 64 k) = .none) :
    ArmFault.stepF mp s = Arm.write_err ArmFault.memFault s := by
  exact ArmFault.stepF_fault ((ArmFault.faults_iff clean decoded).mpr
    (encoded_store64_eight_access_fault baseReg valueReg encoded unmapped))

end Backend.Stock.Proof.MemoryFaults
