import FV.E2E.ExecFrame
import FV.E2E.DeadCleanupExecStatic
import FV.E2E.ExecFrameSim
import FV.E2E.DeadCleanupBinary
import FV.E2E.DeadCleanupBinCheck

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open E2E.ExecBytes Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

variable {I : LinkInput}

/-- **Frame property of the instruction semantics for `Sim`**: if `e` simulates `m` and the
memory reads of the decoded instruction `a` at `m` avoid the relocated instruction bytes, then
`e` simulates `m` after `a`. -/
theorem exec_sim {m e : Arm.ArmState} (a : Arm.ArmInst) (h : Sim I m e)
    (hR : ∀ p ∈ MemReads a m, ∀ k < p.2, ¬ E2E.DeadCleanupBinCheck.RelocAt I (p.1 + BitVec.ofNat 64 k)) :
    Sim I (Arm.exec_inst a m) (Arm.exec_inst a e) :=
  ExecFrame.exec_simR a h hR

/-- `StepOkD.insn` (D2) from the memory reads of the word at the pc. -/
theorem insn_of_memReads {file : ByteArray} {g : Clif.Function} {m : Arm.ArmState}
    (hR : ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
      ∀ p ∈ MemReads a m, ∀ k < p.2, ¬ E2E.DeadCleanupBinCheck.RelocAt I (p.1 + BitVec.ofNat 64 k)) :
    ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
      ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
      ∀ e, Sim I m e → Sim I (Arm.exec_inst a m) (Arm.exec_inst a e) :=
  fun _ _ _ a ha _ h => exec_sim a h (hR a ha)

end E2E.DeadCleanupExecBytes
