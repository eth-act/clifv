import FV.Backend.Proof.RegallocTac

/-!
# `OperandsSound` for the integer instructions (M6 proof)

Every integer straight-line `MInst` form the backend emits, with vreg operands, satisfies
`OperandsSound F (execMInst ctx env) (csem F ctx X)`: `os_of_corr` plus `Corr` by `corr_tac`.
-/

namespace Backend.Proof

open Backend

/-! ## ALU, three registers -/

set_option maxHeartbeats 4000000 in
theorem corr_aluRRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n m : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

/-! ## Other integer forms -/

set_option maxHeartbeats 4000000 in
theorem corr_aluRRRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp3)
    (sz : OperandSize) (d n m a : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩, ⟨a, .int, .use, .early, .reg⟩]
      (fun r => .aluRRRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) (r.getD 3 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRImm12 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n : Nat) (imm : Imm12) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .aluRRImm12 op sz (r.getD 0 .xzr) (r.getD 1 .xzr) imm) := by
  by_cases hi : imm.bits < 4096 <;> cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_bitRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : BitOp)
    (sz : OperandSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .bitRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_mov (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : OperandSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .mov sz (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_movWide (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : MoveWideOp)
    (imm : MoveWideConst) (sz : OperandSize) (d : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩]
      (fun r => .movWide op (r.getD 0 .xzr) imm sz) := by
  by_cases hi : imm.bits < 65536 <;> by_cases h4 : 4 ≤ imm.shift <;> by_cases h2 : 2 ≤ imm.shift <;>
    cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_bitfieldMove (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : OperandSize)
    (op : BfmOp) (d n immr imms : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .bitfieldMove sz op (r.getD 0 .xzr) (r.getD 1 .xzr) immr imms) := by
  by_cases h1 : 64 ≤ immr <;> by_cases h2 : 64 ≤ imms <;> by_cases h3 : 32 ≤ immr <;>
    by_cases h4 : 32 ≤ imms <;> cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_cset (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (c : Cond) (d : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩] (fun r => .cset (r.getD 0 .xzr) c) := by
  cases c <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_csel (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (c : Cond) (d n m : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .csel (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) c) := by
  cases c <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_ccmp (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : OperandSize)
    (nzcv : NZCV) (c : Cond) (n m : Nat) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩, ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .ccmp sz (r.getD 0 .xzr) (r.getD 1 .xzr) nzcv c) := by
  cases c <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_ccmpImm (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : OperandSize)
    (imm : Nat) (nzcv : NZCV) (c : Cond) (n : Nat) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩]
      (fun r => .ccmpImm sz (r.getD 0 .xzr) imm nzcv c) := by
  by_cases hi : imm < 32 <;> cases c <;> cases sz <;> corr_tac


set_option maxHeartbeats 4000000 in
theorem corr_aluRRImmLogic (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n : Nat) (imm : ImmLogic) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .aluRRImmLogic op sz (r.getD 0 .xzr) (r.getD 1 .xzr) imm) := by
  cases sz
  · rcases hb : bitmaskEnc? false (mask64 imm.value % 4294967296) with _ | ⟨N, immr, imms⟩ <;>
      rcases hb' : bitmaskEnc? false (mask64 imm.invert.value % 4294967296) with _ | ⟨N', immr', imms'⟩ <;>
      cases op <;> corr_tac
  · rcases hb : bitmaskEnc? true (mask64 imm.value) with _ | ⟨N, immr, imms⟩ <;>
      rcases hb' : bitmaskEnc? true (mask64 imm.invert.value) with _ | ⟨N', immr', imms'⟩ <;>
      cases op <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRImmShift (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n amt : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .aluRRImmShift op sz (r.getD 0 .xzr) (r.getD 1 .xzr) amt) := by
  by_cases h64 : 64 ≤ amt <;> by_cases h32 : 32 ≤ amt <;> cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRRShift (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n m : Nat) (sh : ShiftOpAndAmt) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRRShift op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) sh) := by
  obtain ⟨sop, amt⟩ := sh
  by_cases h64 : 64 ≤ amt <;> by_cases h32 : 32 ≤ amt <;> cases sop <;> cases op <;> cases sz <;>
    corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_aluRRRExtend (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n m : Nat) (e : ExtendOp) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRRExtend op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) e) := by
  cases op <;> cases sz <;> corr_tac


set_option maxHeartbeats 4000000 in
theorem corr_movK (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (imm : MoveWideConst)
    (sz : OperandSize) (n d : Nat) :
    Corr F ctx env #[⟨n, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reuse 0⟩]
      (fun r => .movK (r.getD 1 .xzr) (r.getD 0 .xzr) imm sz) := by
  by_cases hi : imm.bits < 65536 <;> by_cases h4 : 4 ≤ imm.shift <;> by_cases h2 : 2 ≤ imm.shift <;>
    cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_extend (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (signed : Bool)
    (fromBits toBits d n : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .extend (r.getD 0 .xzr) (r.getD 1 .xzr) signed fromBits toBits) := by
  cases signed
  · by_cases h1 : fromBits = 1
    · subst h1; corr_tac
    by_cases h2 : fromBits = 32 ∧ toBits = 64
    · obtain ⟨rfl, rfl⟩ := h2; corr_tac
    by_cases h4 : 32 ≤ fromBits - 1 <;> corr_tac
  · by_cases h3 : 32 < toBits <;> by_cases h4 : 32 ≤ fromBits - 1 <;>
      by_cases h5 : 64 ≤ fromBits - 1 <;> corr_tac


end Backend.Proof
