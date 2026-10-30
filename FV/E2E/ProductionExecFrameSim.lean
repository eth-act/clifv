import FV.E2E.ExecFrame
import FV.E2E.ProductionExecBytes

/-! # D2 of `RunOkD` from the memory reads (L3 (c))

`exec_sim`: `ProductionExecBytes.Sim I` (registers equal, bytes equal outside the relocated instruction
bytes `RelocAtWithResults I I.results`) is preserved by every decoded instruction whose memory reads (`MemReads`)
avoid `RelocAtWithResults I I.results` (`ExecFrame.exec_simR` at `R = RelocAtWithResults I I.results`). `insn_of_memReads`: so `StepOkD`'s
D2 field `insn` follows from the per-state fact "the reads of the word at the pc avoid
`RelocAtWithResults I I.results`".
-/

namespace E2E.ProductionExecBytes

abbrev MemReads := E2E.ExecBytes.MemReads

open Backend Backend.Proof E2E.LinkCheck E2E.ProductionBinary E2E.BinCheck

variable {I : ProductionStackBound.CompilerInput}

/-- **Frame property of the instruction semantics for `Sim`**: if `e` simulates `m` and the
memory reads of the decoded instruction `a` at `m` avoid the relocated instruction bytes, then
`e` simulates `m` after `a`. -/
theorem exec_sim {m e : Arm.ArmState} (a : Arm.ArmInst) (h : Sim I m e)
    (hR : ∀ p ∈ MemReads a m, ∀ k < p.2, ¬ RelocAtWithResults I I.results (p.1 + BitVec.ofNat 64 k)) :
    Sim I (Arm.exec_inst a m) (Arm.exec_inst a e) :=
  ExecFrame.exec_simR a h hR

/-- `StepOkD.insn` (D2) from the memory reads of the word at the pc. -/
theorem insn_of_memReads {file : ByteArray} {g : Clif.Function} {m : Arm.ArmState}
    (hR : ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
      ∀ p ∈ MemReads a m, ∀ k < p.2, ¬ RelocAtWithResults I I.results (p.1 + BitVec.ofNat 64 k)) :
    ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
      ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
      ∀ e, Sim I m e → Sim I (Arm.exec_inst a m) (Arm.exec_inst a e) :=
  fun _ _ _ a ha _ h => exec_sim a h (hR a ha)

end E2E.ProductionExecBytes
