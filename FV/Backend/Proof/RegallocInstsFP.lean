import FV.Backend.Proof.RegallocTac

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

/-! ### #35: `ushr`/`sli` (`fcopysign`) and `fmadd`… (`fma`) -/

attribute [csimp_rules] Arm.DPSFP.exec_fp_data_processing_three_source

set_option maxHeartbeats 4000000 in
theorem corr_fpuRRRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : FPUOp3)
    (sz : ScalarSize) (d n m a : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩,
      ⟨m, .float, .use, .early, .reg⟩, ⟨a, .float, .use, .early, .reg⟩]
      (fun r => .fpuRRRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr) (r.getD 3 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

/-- A float register below 32 encodes as its number. -/
theorem encV_vlt {d : Nat} (hd : d < 32) : (Reg.v d).encV = .ok (BitVec.ofNat 5 d) := by
  simp [Reg.encV, show d ≤ 31 by omega]

/-- The 7-bit `immh:immb` field of a shift by immediate, split as the encoder does. -/
theorem imm7_split (x : BitVec 7) : x.extractLsb' 3 4 ++ x.extractLsb' 0 3 = x := by
  refine BitVec.eq_of_getLsbD_eq ?_
  intro i hi
  repeat rw [BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb']
  revert i
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp

theorem imm7_hi {v : Nat} (h : v < 128) : ((BitVec.ofNat 7 v).extractLsb' 3 4).toNat = v / 8 := by
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem imm7_val {v : Nat} (h : v < 128) :
    ((BitVec.ofNat 7 v).extractLsb' 3 4 ++ (BitVec.ofNat 7 v).extractLsb' 0 3).toNat = v := by
  rw [imm7_split, BitVec.toNat_ofNat]
  omega

theorem imm7_ne {v : Nat} (h : v < 128) (h8 : 8 ≤ v) : (BitVec.ofNat 7 v).extractLsb' 3 4 ≠ 0#4 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [imm7_hi h] at this
  simp at this
  omega

/-- The expansion of a one-instruction form runs that instruction (the pc advances by 4). -/
theorem execMInst_one {ctx : FnCtx} {env : Env} {m : MInst} {x : Insn} {ai : Arm.ArmInst}
    {s t : Arm.ArmState} (hl : m.lines ctx {} = .ok ([.ins x none], {}))
    (ha : x.toArmInst env = .ok ai) (he : Arm.exec_inst ai s = t)
    (hpc : Arm.r .PC t = Arm.r .PC s + 4#64) : execMInst ctx env m s = some t := by
  simp only [execMInst, hl, execLines, ha, he, hpc, ite_true]

theorem pc_write_pc_sfp (s : Arm.ArmState) (i : BitVec 5) (v : BitVec 64) :
    Arm.r .PC (Arm.write_pc (Arm.read_pc s + 4#64) (Arm.write_sfp 64 i v s)) =
      Arm.r .PC s + 4#64 := by
  simp [Arm.write_pc, Arm.read_pc, Arm.write_sfp]

/-- `ushr vD.2s, vN.2s, #k` on the Arm model: the encoder's fields, `exec_ushr_2s`. -/
theorem execMInst_ushr32 {k : Nat} (h0 : 0 < k) (h1 : k ≤ 32) (ctx : FnCtx) (env : Env)
    {d m : Nat} (hd : d < 32) (hm : m < 32) (s : Arm.ArmState) :
    execMInst ctx env (.fpuRRI (.uShr32 k) (.v d) (.v m)) s =
      some (Arm.write_pc (Arm.read_pc s + 4#64) (Arm.write_sfp 64 (BitVec.ofNat 5 d)
        ((Arm.read_sfp 64 (BitVec.ofNat 5 m) s).extractLsb' 32 32 >>> k ++
          (Arm.read_sfp 64 (BitVec.ofNat 5 m) s).extractLsb' 0 32 >>> k) s)) := by
  have hv : 64 - k < 128 := by omega
  have hok : ushrImmOk (FPUOpRI.uShr32 k).amount (FPUOpRI.uShr32 k).lane = true := by
    simp [ushrImmOk, FPUOpRI.amount, FPUOpRI.lane] <;>
      first | exact ⟨by omega, decide_eq_true (by omega)⟩ | exact decide_eq_true (by omega) | omega
  refine execMInst_one (ai := .DPSFP (.Advanced_simd_shift_by_immediate
      { Q := 0, U := 1, immh := (BitVec.ofNat 7 (64 - k)).extractLsb' 3 4,
        immb := (BitVec.ofNat 7 (64 - k)).extractLsb' 0 3, opcode := 0,
        Rn := BitVec.ofNat 5 m, Rd := BitVec.ofNat 5 d })) rfl ?_ ?_ (pc_write_pc_sfp _ _ _)
  · have hok' : ushrImmOk (k : Int) ((32 : Nat) : Int) = true := hok
    simp only [Insn.toArmInst, Insn.armFields, FPUOpRI.amount, FPUOpRI.lane, Nat.reduceMul, hok',
      Bool.not_true, Bool.false_eq_true, ite_false, encV_vlt hd, encV_vlt hm, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map]
    simp only [Arm.ArmInst.norm, imm7_ne hv (by omega), ite_false]
  · rw [Arm.exec_inst, Arm.DPSFP.exec_ushr_2s _ _ rfl rfl rfl (by simp only [imm7_hi hv]; omega)
      (by simp only [imm7_hi hv]; omega)]
    simp only [imm7_val hv, show 64 - (64 - k) = k by omega]

/-- `ushr dD, dN, #k` on the Arm model (`exec_ushr_scalar_64`). -/
theorem execMInst_ushr64 {k : Nat} (h0 : 0 < k) (h1 : k ≤ 64) (ctx : FnCtx) (env : Env)
    {d m : Nat} (hd : d < 32) (hm : m < 32) (s : Arm.ArmState) :
    execMInst ctx env (.fpuRRI (.uShr64 k) (.v d) (.v m)) s =
      some (Arm.write_pc (Arm.read_pc s + 4#64) (Arm.write_sfp 64 (BitVec.ofNat 5 d)
        (Arm.read_sfp 64 (BitVec.ofNat 5 m) s >>> k) s)) := by
  have hv : 128 - k < 128 := by omega
  have hok : ushrImmOk (k : Int) ((64 : Nat) : Int) = true := by
    simp [ushrImmOk] <;>
      first | exact ⟨by omega, decide_eq_true (by omega)⟩ | exact decide_eq_true (by omega) | omega
  refine execMInst_one (ai := .DPSFP (.Advanced_simd_scalar_shift_by_immediate
      { U := 1, immh := (BitVec.ofNat 7 (128 - k)).extractLsb' 3 4,
        immb := (BitVec.ofNat 7 (128 - k)).extractLsb' 0 3, opcode := 0,
        Rn := BitVec.ofNat 5 m, Rd := BitVec.ofNat 5 d })) rfl ?_ ?_ (pc_write_pc_sfp _ _ _)
  · simp only [Insn.toArmInst, Insn.armFields, FPUOpRI.amount, FPUOpRI.lane, Nat.reduceMul, hok,
      Bool.not_true, Bool.false_eq_true, ite_false, encV_vlt hd, encV_vlt hm, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map]
    simp only [Arm.ArmInst.norm]
  · rw [Arm.exec_inst, Arm.DPSFP.exec_ushr_scalar_64 _ _ rfl rfl (by simp only [imm7_hi hv]; omega)]
    simp only [imm7_val hv, show 128 - (128 - k) = k by omega]

/-- `sli vD.2s, vN.2s, #k` on the Arm model (`exec_sli_2s`); `ri` is not read (tied to `rd`). -/
theorem execMInst_sli32 {k : Nat} (h1 : k < 32) (ctx : FnCtx) (env : Env) {d m : Nat} (ri : Reg)
    (hd : d < 32) (hm : m < 32) (s : Arm.ArmState) :
    execMInst ctx env (.fpuRRIMod (.sli32 k) (.v d) ri (.v m)) s =
      some (Arm.write_pc (Arm.read_pc s + 4#64) (Arm.write_sfp 64 (BitVec.ofNat 5 d)
        (((Arm.read_sfp 64 (BitVec.ofNat 5 d) s).extractLsb' 32 32 &&&
              ~~~(BitVec.allOnes 32 <<< k) |||
            (Arm.read_sfp 64 (BitVec.ofNat 5 m) s).extractLsb' 32 32 <<< k) ++
          ((Arm.read_sfp 64 (BitVec.ofNat 5 d) s).extractLsb' 0 32 &&&
              ~~~(BitVec.allOnes 32 <<< k) |||
            (Arm.read_sfp 64 (BitVec.ofNat 5 m) s).extractLsb' 0 32 <<< k)) s)) := by
  have hv : 32 + k < 128 := by omega
  have hok : sliImmOk (k : Int) ((32 : Nat) : Int) = true := by
    simp [sliImmOk] <;>
      first | exact ⟨by omega, decide_eq_true (by omega)⟩ | exact decide_eq_true (by omega) | omega
  refine execMInst_one (ai := .DPSFP (.Advanced_simd_shift_by_immediate
      { Q := 0, U := 1, immh := (BitVec.ofNat 7 (32 + k)).extractLsb' 3 4,
        immb := (BitVec.ofNat 7 (32 + k)).extractLsb' 0 3, opcode := 0b01010,
        Rn := BitVec.ofNat 5 m, Rd := BitVec.ofNat 5 d })) rfl ?_ ?_ (pc_write_pc_sfp _ _ _)
  · simp only [Insn.toArmInst, Insn.armFields, FPUOpRIMod.amount, FPUOpRIMod.lane, hok,
      Bool.not_true, Bool.false_eq_true, ite_false, encV_vlt hd, encV_vlt hm, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map]
    simp only [Arm.ArmInst.norm, imm7_ne hv (by omega), ite_false]
  · rw [Arm.exec_inst, Arm.DPSFP.exec_sli_2s _ _ rfl rfl rfl (by simp only [imm7_hi hv]; omega)
      (by simp only [imm7_hi hv]; omega)]
    simp only [imm7_val hv, show 32 + k - 32 = k by omega]

/-- `sli dD, dN, #k` on the Arm model (`exec_sli_scalar_64`); `ri` is not read. -/
theorem execMInst_sli64 {k : Nat} (h1 : k < 64) (ctx : FnCtx) (env : Env) {d m : Nat} (ri : Reg)
    (hd : d < 32) (hm : m < 32) (s : Arm.ArmState) :
    execMInst ctx env (.fpuRRIMod (.sli64 k) (.v d) ri (.v m)) s =
      some (Arm.write_pc (Arm.read_pc s + 4#64) (Arm.write_sfp 64 (BitVec.ofNat 5 d)
        ((Arm.read_sfp 64 (BitVec.ofNat 5 d) s &&& ~~~(BitVec.allOnes 64 <<< k)) |||
          (Arm.read_sfp 64 (BitVec.ofNat 5 m) s <<< k)) s)) := by
  have hv : 64 + k < 128 := by omega
  have hok : sliImmOk (k : Int) ((64 : Nat) : Int) = true := by
    simp [sliImmOk] <;>
      first | exact ⟨by omega, decide_eq_true (by omega)⟩ | exact decide_eq_true (by omega) | omega
  refine execMInst_one (ai := .DPSFP (.Advanced_simd_scalar_shift_by_immediate
      { U := 1, immh := (BitVec.ofNat 7 (64 + k)).extractLsb' 3 4,
        immb := (BitVec.ofNat 7 (64 + k)).extractLsb' 0 3, opcode := 0b01010,
        Rn := BitVec.ofNat 5 m, Rd := BitVec.ofNat 5 d })) rfl ?_ ?_ (pc_write_pc_sfp _ _ _)
  · simp only [Insn.toArmInst, Insn.armFields, FPUOpRIMod.amount, FPUOpRIMod.lane, hok,
      Bool.not_true, Bool.false_eq_true, ite_false, encV_vlt hd, encV_vlt hm, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map]
    simp only [Arm.ArmInst.norm]
  · rw [Arm.exec_inst, Arm.DPSFP.exec_sli_scalar_64 _ _ rfl rfl (by simp only [imm7_hi hv]; omega)]
    simp only [imm7_val hv, show 64 + k - 64 = k by omega]

/-- An amount outside Cranelift's range does not encode: no run. -/
theorem execMInst_fpuRRI_none {op : FPUOpRI} (h : ushrImmOk op.amount op.lane = false)
    (ctx : FnCtx) (env : Env) (rd rn : Reg) (s : Arm.ArmState) :
    execMInst ctx env (.fpuRRI op rd rn) s = none := by
  simp [execMInst, MInst.lines, execLines, Insn.toArmInst, Insn.armFields, h, throw, throwThe,
    MonadExceptOf.throw]

/-- `sli` with an amount outside Cranelift's range does not encode: no run. -/
theorem execMInst_fpuRRIMod_none {op : FPUOpRIMod} (h : sliImmOk op.amount op.lane = false)
    (ctx : FnCtx) (env : Env) (rd ri rn : Reg) (s : Arm.ArmState) :
    execMInst ctx env (.fpuRRIMod op rd ri rn) s = none := by
  simp [execMInst, MInst.lines, execLines, Insn.toArmInst, Insn.armFields, h, throw, throwThe,
    MonadExceptOf.throw]

theorem ushrImmOk_iff (op : FPUOpRI) :
    ushrImmOk op.amount op.lane = true ↔ 0 < op.amount ∧ op.amount ≤ op.lane := by
  cases op <;> simp only [ushrImmOk, FPUOpRI.amount, FPUOpRI.lane, Bool.and_eq_true] <;> constructor
  all_goals first
    | (rintro ⟨⟨-, h0⟩, h1⟩
       exact ⟨by have := of_decide_eq_true h0; omega, by have := of_decide_eq_true h1; omega⟩)
    | (rintro ⟨h0, h1⟩
       exact ⟨⟨by decide, decide_eq_true (by omega)⟩, decide_eq_true (by omega)⟩)

theorem sliImmOk_iff (op : FPUOpRIMod) :
    sliImmOk op.amount op.lane = true ↔ op.amount < op.lane := by
  cases op <;> simp only [sliImmOk, FPUOpRIMod.amount, FPUOpRIMod.lane, Bool.and_eq_true] <;>
    constructor
  all_goals first
    | (rintro ⟨-, h1⟩; have := of_decide_eq_true h1; omega)
    | (intro h1
       exact ⟨⟨by decide, decide_eq_true (by omega)⟩, decide_eq_true (by omega)⟩)

/- `corr_tac` with `execMInst` replaced by the closed forms (the amount's range from the
encoder's check). -/
attribute [-csimp_rules] execMInst in
attribute [local csimp_rules] execMInst_ushr32 execMInst_ushr64 in
set_option maxHeartbeats 4000000 in
theorem corr_fpuRRI (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : FPUOpRI) (d n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .fpuRRI op (r.getD 0 .xzr) (r.getD 1 .xzr)) := by
  by_cases hk : ushrImmOk op.amount op.lane = true
  · rw [ushrImmOk_iff] at hk
    obtain ⟨h0, h1⟩ := hk
    cases op <;> simp only [FPUOpRI.amount, FPUOpRI.lane] at h0 h1 <;> corr_tac
  · intro regs s w t' _ _ _ _ hex _
    simp [execMInst_fpuRRI_none (Bool.eq_false_iff.mpr hk)] at hex

/- `corr_tac` with `execMInst` replaced by the closed forms (both runs; the amount's range from
the encoder's check, the tie `rd = ri` from `AllocOk.reuse`). -/
attribute [-csimp_rules] execMInst in
attribute [local csimp_rules] execMInst_sli32 execMInst_sli64 in
set_option maxHeartbeats 4000000 in
theorem corr_fpuRRIMod (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : FPUOpRIMod)
    (d i n : Nat) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reuse 1⟩, ⟨i, .float, .use, .early, .reg⟩,
      ⟨n, .float, .use, .early, .reg⟩]
      (fun r => .fpuRRIMod op (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr)) := by
  by_cases hk : sliImmOk op.amount op.lane = true
  · rw [sliImmOk_iff] at hk
    cases op <;> simp only [FPUOpRIMod.amount, FPUOpRIMod.lane] at hk <;> corr_tac
  · intro regs s w t' _ _ _ _ hex _
    simp [execMInst_fpuRRIMod_none (Bool.eq_false_iff.mpr hk)] at hex

end Backend.Proof
