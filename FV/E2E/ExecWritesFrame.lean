module

public import FV.E2E.ExecWrites

@[expose] public section

/-!
# The memory writes of the frame lines (A3, #412, slice F8b)

The memory writes of the prologue's `stp x29, x30, [sp, #-16]!` and the epilogue's `ldp
x29, x30, [sp], #16`, by the pattern of `memReads_ldp_fplr` in `FV/E2E/ExecReads.lean`.
-/

namespace Backend.Proof

open Backend E2E.ExecBytes E2E.ExecFrame

/-- The prologue's `stp x29, x30, [sp, #-16]!` writes 16 bytes at `sp - 16`. -/
theorem memWrites_stp_pre {env : Env} {a : Arm.ArmInst}
    (h : (Insn.stp Reg.fp Reg.lr (.spPreIndexed (-16))).toArmInst env = .ok a) (s : Arm.ArmState) :
    MemWrites a s = [(spOf s - 16#64, 16)] := by
  have e : (Insn.stp Reg.fp Reg.lr (.spPreIndexed (-16))).toArmInst env = .ok
      (.LDST (.Reg_pair_pre_indexed { opc := 2, V := 0, L := 0, imm7 := 126#7, Rt2 := 30, Rn := 31, Rt := 29 })) := by
    simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl
  rw [e, Except.ok.injEq] at h
  subst h
  simp (config := {decide := true}) [MemWrites, RegPair.writes, RegPair.mk, RegPair.addr,
    RegPair.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr]
  bv_omega

end Backend.Proof
