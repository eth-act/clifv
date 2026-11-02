import FV.Backend.Proof.StockMemoryAccessArmFault

namespace Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The actual byte acquire faults before its read at an unmapped address. -/
theorem instFaults_acquire_byte {mp : ArmFault.MemMap} {s : Arm.ArmState}
    {base destination : BitVec 5} (ordinaryBase : base ≠ 31#5)
    (unmapped : mp (Arm.read_gpr 64 base s) = .none) :
    ArmFault.InstFaults mp (.LDST (.Reg_exclusive
      {size := 0,ord := 1,L := 1,Rs := 31,o0 := 1,Rn := base,Rt := destination})) s := by
  refine ArmFault.instFaults_of_byte (e := ⟨.acqR,Arm.read_gpr 64 base s,
    1,Concurrency.ArmFoot.readM 1 (Arm.read_gpr 64 base s) s.mem⟩) (i := 0) ?_ (by decide) ?_
  · simp [Concurrency.ArmInstFoot.instEvs,Concurrency.ArmInstFoot.exclEvs,
      Concurrency.ArmInstFoot.exclKind,ordinaryBase]
  · simp [unmapped,ArmFault.Perm.allows,Concurrency.AKind.dir]

end Backend.Stock.Proof.Acquire810
