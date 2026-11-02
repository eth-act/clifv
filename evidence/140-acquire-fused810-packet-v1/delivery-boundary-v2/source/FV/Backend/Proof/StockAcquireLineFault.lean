import FV.Backend.Proof.StockAcquireEncodingFault
import FV.Backend.Proof.StockMemoryAccessLineFacts
import FV.E2E.MemTrapStatement

namespace Backend.Stock.Proof.Acquire810
open Backend Backend.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual linked acquire line reaches its original trap entry and memory fault. -/
theorem acquire_byte_line_fault {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {j base destination : Nat} {code : Clif.TrapCode}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30)
    (line : R.L[j]? = some (.ins (.ldar 8 (.x destination) (.x base)) (some code)))
    (pc : Arm.r .PC s = R.pcOf j) (clean : Arm.r .ERR s = .None)
    (program : s.program = R.fb.program R.base) {mp : ArmFault.MemMap}
    (unmapped : mp (Arm.read_gpr 64 (BitVec.ofNat 5 base) s) = .none) :
    TrapAtF mp R.fb R.base code s := by
  have trap := MemoryFaults.access_trapAt_ins wellFormed line pc clean
  obtain ⟨inst,encoded,decoded⟩ := MemoryFaults.access_decodeAt_line wellFormed line program pc
  exact ⟨trap,(ArmFault.faults_iff (show Arm.read_err s = .None from clean) decoded).mpr
    (encoded_acquire_byte_fault baseReg destinationReg encoded unmapped)⟩

end Backend.Stock.Proof.Acquire810
