import FV.Backend.Proof.StockAcquireAllocatedLineAllWidths

namespace Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Every acquire width faults on any unmapped byte in its exact ARM footprint. -/
theorem instFaults_acquire_all_widths {mp : ArmFault.MemMap} {s : Arm.ArmState}
    {base destination : BitVec 5} {size : BitVec 2} (ordinaryBase : base ≠ 31#5)
    {j : Nat} (bound : j < ((8 <<< size.toNat)/8))
    (unmapped : mp (Arm.read_gpr 64 base s+BitVec.ofNat 64 j) = .none) :
    ArmFault.InstFaults mp (.LDST (.Reg_exclusive
      {size := size,ord := 1,L := 1,Rs := 31,o0 := 1,Rn := base,Rt := destination})) s := by
  refine ArmFault.instFaults_of_byte (e := ⟨.acqR,Arm.read_gpr 64 base s,
    ((8 <<< size.toNat)/8),Concurrency.ArmFoot.readM (((8 <<< size.toNat)/8)) (Arm.read_gpr 64 base s) s.mem⟩) (i := j) ?_ bound ?_
  · simp [Concurrency.ArmInstFoot.instEvs,Concurrency.ArmInstFoot.exclEvs,
      Concurrency.ArmInstFoot.exclKind,ordinaryBase]
  · simp [unmapped,ArmFault.Perm.allows,Concurrency.AKind.dir]

end Backend.Stock.Proof.Acquire810
