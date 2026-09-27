import FV.Backend.Proof.RegallocTac

/-!
# `Corr` for the float/vector instructions (M6 proof)

`movToFpu` (`fmov`), `movFromVec` (`umov`, every lane index), `vecMisc cnt`,
`vecLanes addv/uaddlv`, `vecRRR addp` (the popcount sequence), all sizes/arrangements:
`corr_tac` with the Arm model's SIMD&FP execution functions added to `csimp_rules`.
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

end Backend.Proof
