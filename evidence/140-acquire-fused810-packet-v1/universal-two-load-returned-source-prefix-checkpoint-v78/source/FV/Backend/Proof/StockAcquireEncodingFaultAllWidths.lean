import FV.Backend.Proof.StockAcquireArmFaultAllWidths

namespace Backend.Stock.Proof.Acquire810
open Backend
set_option autoImplicit false
set_option Elab.async false

/-- Every admitted acquire encoding preserves its exact physical operands and access size. -/
theorem acquire_all_widths_encoding (env : Env) {base destination width : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30)
    (widthOk : width = 8 ∨ width = 16 ∨ width = 32 ∨ width = 64) :
    ∃ size : BitVec 2,((8 <<< size.toNat)/8) = width/8 ∧
      (Insn.ldar width (.x destination) (.x base)).toArmInst env =
        .ok (.LDST (.Reg_exclusive {size := size,ord := 1,L := 1,Rs := 31,o0 := 1,Rn := BitVec.ofNat 5 base,Rt := BitVec.ofNat 5 destination})) := by
  rcases widthOk with rfl | rfl | rfl | rfl
  · refine ⟨0,rfl,?_⟩
    simp [Insn.toArmInst,Insn.armFields,Insn.armFields.exclFields,Arm.ArmInst.norm,Reg.encSP,Reg.encZR,baseReg,destinationReg]
  · refine ⟨1,rfl,?_⟩
    simp [Insn.toArmInst,Insn.armFields,Insn.armFields.exclFields,Arm.ArmInst.norm,Reg.encSP,Reg.encZR,baseReg,destinationReg]
  · refine ⟨2,rfl,?_⟩
    simp [Insn.toArmInst,Insn.armFields,Insn.armFields.exclFields,Arm.ArmInst.norm,Reg.encSP,Reg.encZR,baseReg,destinationReg]
  · refine ⟨3,rfl,?_⟩
    simp [Insn.toArmInst,Insn.armFields,Insn.armFields.exclFields,Arm.ArmInst.norm,Reg.encSP,Reg.encZR,baseReg,destinationReg]

/-- An unmapped byte faults in the actual acquire encoding for all original atomic widths. -/
theorem encoded_acquire_all_widths_fault {env : Env} {base destination width : Nat}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30)
    (widthOk : width = 8 ∨ width = 16 ∨ width = 32 ∨ width = 64) {ai : Arm.ArmInst}
    {mp : ArmFault.MemMap} {s : Arm.ArmState} {j : Nat}
    (encoded : (Insn.ldar width (.x destination) (.x base)).toArmInst env = .ok ai)
    (bound : j < width/8)
    (unmapped : mp (Arm.read_gpr 64 (BitVec.ofNat 5 base) s+BitVec.ofNat 64 j) = .none) :
    ArmFault.InstFaults mp ai s := by
  obtain ⟨size,bytes,encoding⟩ := acquire_all_widths_encoding env baseReg destinationReg widthOk
  rw [encoding] at encoded
  cases encoded
  apply instFaults_acquire_all_widths (size := size) _ (by rwa [bytes]) unmapped
  intro same
  have bad : base = 31 := by
    simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show base < 32 by omega)] using congrArg BitVec.toNat same
  omega

end Backend.Stock.Proof.Acquire810
