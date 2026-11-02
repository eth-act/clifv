import FV.Backend.Proof.StockMemoryAccessTrap
import FV.ArmFault.Step

/-! Additive ordinary-access fault shapes. The old atomic observable stays unchanged.
These drafts require the complete current normal-key ArmFault context before verification. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Convert the existing source-map fault property to the same 64-bit byte range. -/
theorem sourceAddrPred_unmapped {mp : ArmFault.MemMap} {address : BitVec 64} {bytes : Nat}
    (property : sourceAddrPred (fun a n => ∃ k < n,mp (BitVec.ofNat 64 (a+k)) = .none) address bytes) :
    ∃ k < bytes,mp (address + BitVec.ofNat 64 k) = .none := by
  obtain ⟨a,rfl,k,bound,unmapped⟩ := property
  exact ⟨k,bound,by simpa only [← BitVec.ofNat_add] using unmapped⟩

/-- The actual unsigned i64 load faults if its access has an unmapped byte. -/
theorem instFaults_unsigned_load64 {mp : ArmFault.MemMap} {s : Arm.ArmState}
    {base destination : BitVec 5} {offset : BitVec 12}
    (ordinaryBase : base ≠ 31#5)
    (unmapped : ∃ k < 8,mp ((Arm.read_gpr 64 base s +
      Arm.LDST.Reg_offset.value (.uimm12 offset) 3 s) + BitVec.ofNat 64 k) = .none) :
    ArmFault.InstFaults mp (.LDST (.Reg_unsigned_imm
      {size := 3,V := 0,opc := 1,imm12 := offset,Rn := base,Rt := destination})) s := by
  obtain ⟨k,bound,missing⟩ := unmapped
  refine ArmFault.instFaults_of_byte (e := ⟨.plainR,
    Arm.read_gpr 64 base s + Arm.LDST.Reg_offset.value (.uimm12 offset) 3 s,
    8,Concurrency.ArmFoot.readM 8
      (Arm.read_gpr 64 base s + Arm.LDST.Reg_offset.value (.uimm12 offset) 3 s) s.mem⟩) ?_ bound ?_
  · simp [Concurrency.ArmInstFoot.instEvs,Concurrency.ArmInstFoot.immEvs,
      Arm.LDST.reg_imm_constrain_unpredictable,ordinaryBase]
  · simp [missing,ArmFault.Perm.allows,Concurrency.ArmFoot.AKind.dir]

/-- The actual unsigned i64 store faults before its write if a byte is unmapped. -/
theorem instFaults_unsigned_store64 {mp : ArmFault.MemMap} {s : Arm.ArmState}
    {base value : BitVec 5} {offset : BitVec 12}
    (ordinaryBase : base ≠ 31#5)
    (unmapped : ∃ k < 8,mp ((Arm.read_gpr 64 base s +
      Arm.LDST.Reg_offset.value (.uimm12 offset) 3 s) + BitVec.ofNat 64 k) = .none) :
    ArmFault.InstFaults mp (.LDST (.Reg_unsigned_imm
      {size := 3,V := 0,opc := 0,imm12 := offset,Rn := base,Rt := value})) s := by
  obtain ⟨k,bound,missing⟩ := unmapped
  refine ArmFault.instFaults_of_byte (e := ⟨.plainW,
    Arm.read_gpr 64 base s + Arm.LDST.Reg_offset.value (.uimm12 offset) 3 s,
    8,Arm.read_gpr_zr 64 value s⟩) ?_ bound ?_
  · simp [Concurrency.ArmInstFoot.instEvs,Concurrency.ArmInstFoot.immEvs,
      Arm.LDST.reg_imm_constrain_unpredictable,ordinaryBase,Concurrency.ArmInstFoot.shl_div,
      Arm.LDST.ldst_read]
  · simp [missing,ArmFault.Perm.allows,Concurrency.ArmFoot.AKind.dir]

end Backend.Stock.Proof.MemoryFaults
