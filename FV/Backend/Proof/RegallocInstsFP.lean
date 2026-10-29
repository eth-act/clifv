module

public import FV.Backend.Proof.RegallocTac

@[expose] public section

/-!
# `Corr` for the float/vector instructions (M6 proof)

`movToFpu` (`fmov`), `movFromVec` (`umov`, every lane index), `vecMisc cnt`,
`vecLanes addv/uaddlv`, `vecRRR addp` (the popcount sequence), all sizes/arrangements;
the scalar FP data movement of S11e1: `fpuCSel` (`fcsel`, every size and condition),
`fpuMoveFPImm` (`fmov #imm`, symbolic immediate), `vecDupImm` (the plain `movi`, symbolic
immediate; the other forms do not expand): `corr_tac` with the Arm model's SIMD&FP execution
functions added to `csimp_rules`.
Arrangements the encoder rejects or the model reports as illegal have `csem = none`
(vacuous). `umov`'s lane index is a symbolic immediate whose `match_bv` decoding needs it
concrete: the valid indices are enumerated.
-/

namespace Backend.Proof

open Backend

/-- `bind`/`map` distribute over an encoder range check (`uField`). -/
theorem except_ite_bind {ε α β : Type} (c : Prop) [Decidable c] (x y : Except ε α)
    (f : α → Except ε β) : ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl
theorem except_map_ite {ε α β : Type} (c : Prop) [Decidable c] (x y : Except ε α)
    (f : α → β) : (f <$> (if c then x else y)) = if c then f <$> x else f <$> y := by
  split <;> rfl
attribute [csimp_rules] except_ite_bind except_map_ite
attribute [csimp_rules] Arm.DPSFP.exec_conversion_between_FP_and_Int Arm.DPSFP.exec_fmov_general
  Arm.DPSFP.fmov_general_aux Arm.Vpart_read Arm.Vpart_write Arm.read_sfp Arm.write_sfp Reg.encV
  Arm.DPSFP.exec_advanced_simd_copy Arm.DPSFP.exec_smov_umov
  Arm.DPSFP.exec_advanced_simd_two_reg_misc Arm.DPSFP.exec_cnt
  Arm.DPSFP.exec_advanced_simd_across_lanes Arm.DPSFP.exec_addv Arm.DPSFP.exec_uaddlv
  Arm.DPSFP.exec_advanced_simd_three_same Arm.DPSFP.exec_addp_vector VectorSize.qsize

theorem bv8_toNat_lt (x : BitVec 8) : x.toNat < 256 := x.isLt

attribute [csimp_rules] Arm.DPSFP.exec_fp_conditional_select Arm.DPSFP.exec_fp_immediate
  Arm.DPSFP.fp_write_result Arm.DPSFP.exec_advanced_simd_modified_immediate
  Arm.DPSFP.decode_immediate_op Arm.DPSFP.AdvSIMDExpandImm bv8_toNat_lt Insn.armFields.fpFtype

set_option maxHeartbeats 4000000 in
theorem corr_movFromVec (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (idx : Nat)
    (sz : ScalarSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .movFromVec (r.getD 0 .xzr) (r.getD 1 .xzr) idx sz) := by
  cases sz
  · by_cases hi : idx * 2 + 1 < 32
    · have hl : idx < 16 := by omega
      clear hi
      iterate 16 (rcases idx with _ | idx; · corr_tac)
      omega
    · corr_tac
  · by_cases hi : idx * 4 + 2 < 32
    · have hl : idx < 8 := by omega
      clear hi
      iterate 8 (rcases idx with _ | idx; · corr_tac)
      omega
    · corr_tac
  · by_cases hi : idx * 8 + 4 < 32
    · have hl : idx < 4 := by omega
      clear hi
      iterate 4 (rcases idx with _ | idx; · corr_tac)
      omega
    · corr_tac
  · by_cases hi : idx * 16 + 8 < 32
    · have hl : idx < 2 := by omega
      clear hi
      iterate 2 (rcases idx with _ | idx; · corr_tac)
      omega
    · corr_tac
  · corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_movToFpu (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .movToFpu (r.getD 0 .xzr) (r.getD 1 .xzr) sz) := by
  cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_vecMisc (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : VecMisc2)
    (sz : VectorSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .vecMisc op (r.getD 0 .xzr) (r.getD 1 .xzr) sz) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_vecLanes (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : VecLanesOp)
    (sz : VectorSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .vecLanes op (r.getD 0 .xzr) (r.getD 1 .xzr) sz) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_vecRRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : VecALUOp)
    (sz : VectorSize) (d n m : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩,
      ⟨m, .float, .use, .early, .reg⟩]
      (fun r => .vecRRR op (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) sz) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_fpuCSel (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize) (c : Cond)
    (d n m : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩,
      ⟨m, .float, .use, .early, .reg⟩]
      (fun r => .fpuCSel sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) c) := by
  cases sz <;> cases c <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_fpuMoveFPImm (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (imm : ASIMDFPModImm)
    (sz : ScalarSize) (d : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩]
      (fun r => .fpuMoveFPImm (r.getD 0 .xzr) imm sz) := by
  cases sz <;> corr_tac

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem corr_vecDupImm (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (imm : ASIMDMovModImm)
    (inv : Bool) (sz : VectorSize) (d : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩]
      (fun r => .vecDupImm (r.getD 0 .xzr) imm inv sz) := by
  by_cases h : (inv || imm.shift != 0 || imm.shiftOnes || imm.is64) = true
  · intro regs s w t' _ _ _ _ hex _
    simp [execMInst, MInst.lines, h, throw, throwThe, MonadExceptOf.throw] at hex
  · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Bool.not_eq_true, Decidable.not_not] at h
    obtain ⟨⟨⟨rfl, h2⟩, h3⟩, h4⟩ := h
    cases sz <;> corr_tac

/-! ### S11f: scalar FP arithmetic and comparison -/

attribute [csimp_rules] Arm.DPSFP.exec_fp_data_processing_two_source
  Arm.DPSFP.exec_fp_data_processing_one_source Arm.DPSFP.exec_fp_compare Arm.DPSFP.fpFmt

set_option maxHeartbeats 4000000 in
theorem corr_fpuRRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : FPUOp2)
    (sz : ScalarSize) (d n m : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩,
      ⟨m, .float, .use, .early, .reg⟩]
      (fun r => .fpuRRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_fpuRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : FPUOp1)
    (sz : ScalarSize) (d n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .fpuRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_fpuCmp (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize)
    (n m : Nat) :
    Corr F ctx env #[⟨n, .float, .use, .early, .reg⟩, ⟨m, .float, .use, .early, .reg⟩]
      (fun r => .fpuCmp sz (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases sz <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_fpuRound (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : FpuRoundMode)
    (d n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .fpuRound op (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases op <;> corr_tac

/-! ### S11f-cvt: float ↔ integer conversions -/

attribute [csimp_rules] Arm.DPSFP.exec_fp_int_cvt Arm.DPSFP.FPDecodeRounding

set_option maxHeartbeats 4000000 in
theorem corr_fpuToInt (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : FpuToIntOp)
    (d n : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .fpuToInt op (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases op <;> corr_tac

set_option maxHeartbeats 4000000 in
theorem corr_intToFpu (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : IntToFpuOp)
    (d n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .intToFpu op (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  cases op <;> corr_tac

end Backend.Proof
