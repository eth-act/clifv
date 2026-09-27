import FV.Backend.Proof.RegallocTac

/-!
# `OperandsSound` for integer forms with a zero-register operand (M6 proof)

`xzr` in an operand position is Cranelift's `reg_fixed_nonallocatable`: no operand, the same
register in the canonical and the allocated instruction. Forms emitted by the ISLE rules:
`neg`/`mvn` (`rn = xzr`), `cmp`/`cmn`/`tst` (`rd = xzr`), `mul` (`madd` with `ra = xzr`).
-/

namespace Backend.Proof

open Backend

set_option maxHeartbeats 4000000 in
theorem corr_aluRRR_rnZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d m : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRR op sz (r.getD 0 .xzr) .xzr (r.getD 1 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRR_rdZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (n m : Nat) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩, ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRR op sz .xzr (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRImm12_rdZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (n : Nat) (imm : Imm12) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩]
      (fun r => .aluRRImm12 op sz .xzr (r.getD 0 .xzr) imm) := by
  by_cases hi : imm.bits < 4096 <;> cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRImmLogic_rdZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (n : Nat) (imm : ImmLogic) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩]
      (fun r => .aluRRImmLogic op sz .xzr (r.getD 0 .xzr) imm) := by
  cases sz
  · rcases hb : bitmaskEnc? false (mask64 imm.value % 4294967296) with _ | ⟨N, immr, imms⟩ <;>
      rcases hb' : bitmaskEnc? false (mask64 imm.invert.value % 4294967296) with _ | ⟨N', immr', imms'⟩ <;>
      cases op <;> corr_tac
  · rcases hb : bitmaskEnc? true (mask64 imm.value) with _ | ⟨N, immr, imms⟩ <;>
      rcases hb' : bitmaskEnc? true (mask64 imm.invert.value) with _ | ⟨N', immr', imms'⟩ <;>
      cases op <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRRShift_rdZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (n m : Nat) (sh : ShiftOpAndAmt) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩, ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRRShift op sz .xzr (r.getD 0 .xzr) (r.getD 1 .xzr) sh) := by
  obtain ⟨sop, amt⟩ := sh
  by_cases h64 : 64 ≤ amt <;> by_cases h32 : 32 ≤ amt <;> cases sop <;> cases op <;> cases sz <;>
    corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRRShift_rnZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d m : Nat) (sh : ShiftOpAndAmt) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRRShift op sz (r.getD 0 .xzr) .xzr (r.getD 1 .xzr) sh) := by
  obtain ⟨sop, amt⟩ := sh
  by_cases h64 : 64 ≤ amt <;> by_cases h32 : 32 ≤ amt <;> cases sop <;> cases op <;> cases sz <;>
    corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRRExtend_rdZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (n m : Nat) (e : ExtendOp) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩, ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRRExtend op sz .xzr (r.getD 0 .xzr) (r.getD 1 .xzr) e) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRRR_raZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp3)
    (sz : OperandSize) (d n m : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) .xzr) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
/-- `op rd, rn, xzr` (e.g. `subs rd, rn, xzr`: compare with zero). -/
theorem corr_aluRRR_rmZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .aluRRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr) .xzr) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
/-- `op xzr, rn, xzr` (e.g. `cmp rn, xzr`). -/
theorem corr_aluRRR_rdZ_rmZ (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (n : Nat) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩]
      (fun r => .aluRRR op sz .xzr (r.getD 0 .xzr) .xzr) := by
  cases op <;> cases sz <;> corr_tac

end Backend.Proof
