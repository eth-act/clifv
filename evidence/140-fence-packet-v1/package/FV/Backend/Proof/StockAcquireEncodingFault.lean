import FV.Backend.Proof.StockAcquireArmFault
import FV.Backend.Encode

namespace Backend.Stock.Proof.Acquire810
open Backend
set_option autoImplicit false
set_option Elab.async false

/-- The actual byte acquire encoding preserves both physical registers. -/
theorem acquire_byte_encoding (env : Env) {base destination : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30) :
    (Insn.ldar 8 (.x destination) (.x base)).toArmInst env =
      .ok (.LDST (.Reg_exclusive {size := 0,ord := 1,L := 1,Rs := 31,o0 := 1,Rn := BitVec.ofNat 5 base,Rt := BitVec.ofNat 5 destination})) := by
  simp [Insn.toArmInst,Insn.armFields,Insn.armFields.exclFields,Arm.ArmInst.norm,
    Reg.encSP,Reg.encZR,baseReg,destinationReg]
  rfl

/-- The real encoded acquire faults before reading its unmapped byte. -/
theorem encoded_acquire_byte_fault {env : Env} {base destination : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30) {ai : Arm.ArmInst}
    {mp : ArmFault.MemMap} {s : Arm.ArmState}
    (encoded : (Insn.ldar 8 (.x destination) (.x base)).toArmInst env = .ok ai)
    (unmapped : mp (Arm.read_gpr 64 (BitVec.ofNat 5 base) s) = .none) :
    ArmFault.InstFaults mp ai s := by
  rw [acquire_byte_encoding env baseReg destinationReg] at encoded
  cases encoded
  apply instFaults_acquire_byte _ unmapped
  intro same
  have bad : base = 31 := by
    simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show base < 32 by omega)] using congrArg BitVec.toNat same
  omega

/-- The existing fault machine takes its memory-fault step at the actual acquire. -/
theorem encoded_acquire_byte_fault_step {env : Env} {base destination : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30) {ai : Arm.ArmInst}
    {mp : ArmFault.MemMap} {s : Arm.ArmState}
    (encoded : (Insn.ldar 8 (.x destination) (.x base)).toArmInst env = .ok ai)
    (clean : Arm.read_err s = .None) (decoded : Concurrency.ArmFoot.decodeAt s = some ai)
    (unmapped : mp (Arm.read_gpr 64 (BitVec.ofNat 5 base) s) = .none) :
    ArmFault.stepF mp s = Arm.write_err ArmFault.memFault s := by
  exact ArmFault.stepF_fault ((ArmFault.faults_iff clean decoded).mpr
    (encoded_acquire_byte_fault baseReg destinationReg encoded unmapped))

end Backend.Stock.Proof.Acquire810
