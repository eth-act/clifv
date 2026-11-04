import FV.Backend.Proof.RegallocSlots
import FV.Backend.Proof.RegallocMem
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.RegallocMemAddr
import FV.E2E.ExecReads
import FV.E2E.Statement

/-!
# The callee-save pushes and pops on the machine (#549, #479)

Cranelift's `gen_clobber_save`/`gen_clobber_restore` (`prologueLines`/`epilogueLines`): the
saved registers are pushed below fp/lr with pre-indexed `str`/`stp` (`str d`/`stp d` for
v8–v15) and popped with post-indexed `ldr`/`ldp`. `pushLines_ok`: the pushes of one register
class lower `sp` by `pushBytes`, write only below the old `sp`, and leave register `rs[i]`'s
low 64 bits at `sp_new + 8 i`; `popLines_ok`: the pops read them back (the upper half of a
`v` register cleared) and raise `sp` by `pushBytes`.
-/

open Backend E2E

namespace Backend.Proof

/-! ## Exec lemmas -/

theorem add_neg16 (x : BitVec 64) : x + 18446744073709551600#64 = x - 16#64 := by bv_omega

theorem imm12_bv {i : Imm12} (hi : i.bits < 4096) :
    (if i.shift12 = false then 0#52 ++ BitVec.ofNat 12 i.bits
      else (0#52 ++ BitVec.ofNat 12 i.bits) <<< 12) = BitVec.ofNat 64 i.value := by
  apply BitVec.eq_of_toNat_eq
  have e : (0#52 ++ BitVec.ofNat 12 i.bits).toNat = i.bits := by
    rw [BitVec.toNat_append]; simp; omega
  cases h : i.shift12 <;> simp [Imm12.value, h, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, e] <;> omega

theorem extend_uxtx0 (x : BitVec 64) :
    Arm.extend_reg x (Arm.decode_reg_extend ExtendOp.uxtx.bits) 0 = x := by
  have e : Arm.decode_reg_extend ExtendOp.uxtx.bits = .UXTX := rfl
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
  exact x.isLt

theorem exec_stp_fplr (env : Env) (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.stp Reg.fp Reg.lr (.spPreIndexed (-16))).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.w (.GPR 31#5) (spOf s - 16#64)
          (Arm.write_mem_bytes 16 (spOf s - 16#64) (xreg 30 s ++ xreg 29 s) s)) := by
  refine ⟨_, by simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl, ?_⟩
  have hal' := spAligned hal
  simp [csimp_rules, Arm.LDST.exec_reg_pair_pre_indexed, Arm.LDST.exec_reg_pair_common,
    Arm.LDST.reg_pair_operation, Arm.LDST.reg_pair_constrain_unpredictable, Arm.ldst_read,
    Arm.CheckSPAlignment, hal', xreg, Arm.BitVec.lsb, add_neg16]

theorem exec_ldp_fplr (env : Env) (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.ldp Reg.fp Reg.lr (.spPostIndexed 16)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.w (.GPR 31#5) (spOf s + 16#64)
          (Arm.w (.GPR 30#5) ((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 64 64)
            (Arm.w (.GPR 29#5) ((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 0 64) s))) := by
  refine ⟨_, by simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl, ?_⟩
  have hal' := spAligned hal
  simp [csimp_rules, Arm.LDST.exec_reg_pair_post_indexed, Arm.LDST.exec_reg_pair_common,
    Arm.LDST.reg_pair_operation, Arm.LDST.reg_pair_constrain_unpredictable, Arm.ldst_write,
    Arm.CheckSPAlignment, hal', Arm.BitVec.lsb]

theorem exec_mov_fp_sp (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.mov true Reg.fp .sp).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 29#5) (spOf s) (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, Reg.fp, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_add]

theorem exec_sub_sp_imm (env : Env) (i : Imm12) (hi : i.bits < 4096) (s : Arm.ArmState) :
    ∃ a, (Insn.aluImm12 .sub true .sp .sp i).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 31#5) (spOf s - BitVec.ofNat 64 i.value)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, hi, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_sub_neg, imm12_bv hi]

theorem exec_add_sp_imm (env : Env) (i : Imm12) (hi : i.bits < 4096) (s : Arm.ArmState) :
    ∃ a, (Insn.aluImm12 .add true .sp .sp i).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 31#5) (spOf s + BitVec.ofNat 64 i.value)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, hi, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_add, imm12_bv hi]

theorem exec_sub_sp_x16uxtx (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.aluRRRExtend .sub true .sp .sp (.x 16) .uxtx).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 31#5) (spOf s - xreg 16 s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_sub_neg, extend_uxtx0, xreg]

theorem exec_add_sp_x16uxtx (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.aluRRRExtend .add true .sp .sp (.x 16) .uxtx).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 31#5) (spOf s + xreg 16 s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_add, extend_uxtx0, xreg]

theorem exec_ret (env : Env) (s : Arm.ArmState) :
    ∃ a, Insn.ret.toArmInst env = .ok a ∧ Arm.exec_inst a s = Arm.w .PC (xreg 30 s) s := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.BR.exec_uncond_branch_reg, xreg]

/-! ## Runs of the prologue and the epilogue -/

theorem checkSP_iff (s : Arm.ArmState) : Arm.CheckSPAlignment s ↔ (spOf s).toNat % 16 = 0 := by
  simp only [Arm.CheckSPAlignment, Arm.read_gpr, Arm.Aligned, spOf, BitVec.setWidth_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.extractLsb'_toNat] using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.extractLsb'_toNat] using h

theorem frame_imm12 {v : Nat} {i : Imm12} (h : Imm12.ofNat? v = some i) (hv : v < 2 ^ 64) :
    i.value = v ∧ i.bits < 4096 := by
  unfold Imm12.ofNat? mask64 at h
  rw [Nat.mod_eq_of_lt hv] at h
  simp only at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · split at h
    · cases h
      rename_i h1
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      simp only [Imm12.value, ite_true]
      omega
    · cases h

theorem steps_one {env : Env} {i : Insn} {t : Option Clif.TrapCode} {s : Arm.ArmState}
    {ai : Arm.ArmInst} (ha : i.toArmInst env = .ok ai)
    (hpc : Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64)
    (he : Arm.r .ERR (Arm.exec_inst ai s) = Arm.r .ERR s)
    (hp : (Arm.exec_inst ai s).program = s.program) :
    StepsOk env [.ins i t] s (Arm.exec_inst ai s) :=
  steps_cons ha hpc he hp rfl

/-- The `sp` adjustment runs: `sp ± size`, only the pc, `sp` and `x16` change. -/
theorem spAdj_ok (env : Env) (sub : Bool) {size : Nat} (hs : size < 2 ^ 64) (s : Arm.ArmState) :
    ∃ s', StepsOk env (spAdjLines sub size) s s' ∧
      spOf s' = (if sub then spOf s - BitVec.ofNat 64 size else spOf s + BitVec.ofNat 64 size) ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → Arm.r f s' = Arm.r f s) ∧
      s'.mem = s.mem := by
  unfold spAdjLines
  by_cases h0 : size = 0
  · subst h0
    refine ⟨s, rfl, by cases sub <;> simp, fun _ _ _ _ => rfl, rfl⟩
  simp only [show (size == 0) = false by simpa using h0, Bool.false_eq_true, ite_false]
  cases hi : Imm12.ofNat? size with
  | some i =>
    obtain ⟨hv, hb⟩ := frame_imm12 hi hs
    cases sub
    · obtain ⟨a, ha, he⟩ := exec_add_sp_imm env i hb s
      refine ⟨_, steps_one ha ?_ ?_ ?_, ?_, fun f h1 h2 _ => ?_, ?_⟩ <;>
        simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program,
          Arm.ArmState.mem_w_eq_mem, *]
    · obtain ⟨a, ha, he⟩ := exec_sub_sp_imm env i hb s
      refine ⟨_, steps_one ha ?_ ?_ ?_, ?_, fun f h1 h2 _ => ?_, ?_⟩ <;>
        simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program,
          Arm.ArmState.mem_w_eq_mem, *]
  | none =>
    have hL := steps_loadConst64 env (n := 16) (by omega) size s
    generalize hs1 : pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) size).length))
      (BitVec.ofNat 64 size) = s1 at hL
    have hf1 := pcx_facts s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) size).length))
      (BitVec.ofNat 64 size)
    rw [hs1] at hf1
    have hsp1 : spOf s1 = spOf s := by
      rw [← hs1]; simp [pcx, spOf, Arm.r_of_w_different]
    have ho1 : ∀ f, f ≠ .PC → f ≠ .GPR 16#5 → Arm.r f s1 = Arm.r f s := by
      intro f h1 h2; rw [← hs1]; simp [pcx, Arm.r_of_w_different, h1, h2]
    have hm1 : s1.mem = s.mem := by rw [← hs1]; simp [pcx, Arm.ArmState.mem_w_eq_mem]
    have hx16 : xreg 16 s1 = BitVec.ofNat 64 size := hf1.2.2.2
    cases sub
    · obtain ⟨a, ha, he⟩ := exec_add_sp_x16uxtx { env with pc := env.pc + 4 * (loadConst64 (.x 16) size).length } s1
      refine ⟨_, StepsOk.append hL (steps_one ha ?_ ?_ ?_), ?_, fun f h1 h2 h3 => ?_, ?_⟩
      · simp [he, Arm.r_of_w_same, Arm.r_of_w_different]
      · simp [he, Arm.r_of_w_different]
      · simp [he, Arm.w_program]
      · simp [he, spOf, Arm.r_of_w_same, hx16]; simpa [spOf] using congrArg (· + BitVec.ofNat 64 size) hsp1
      · simp [he, Arm.r_of_w_different, h1, h2, ho1 f h1 h3]
      · simp [he, Arm.ArmState.mem_w_eq_mem, hm1]
    · obtain ⟨a, ha, he⟩ := exec_sub_sp_x16uxtx { env with pc := env.pc + 4 * (loadConst64 (.x 16) size).length } s1
      refine ⟨_, StepsOk.append hL (steps_one ha ?_ ?_ ?_), ?_, fun f h1 h2 h3 => ?_, ?_⟩
      · simp [he, Arm.r_of_w_same, Arm.r_of_w_different]
      · simp [he, Arm.r_of_w_different]
      · simp [he, Arm.w_program]
      · simp [he, spOf, Arm.r_of_w_same, hx16]; simpa [spOf] using congrArg (· - BitVec.ofNat 64 size) hsp1
      · simp [he, Arm.r_of_w_different, h1, h2, ho1 f h1 h3]
      · simp [he, Arm.ArmState.mem_w_eq_mem, hm1]


theorem add_neg16p (x : BitVec 64) : x + 18446744073709551600#64 = x - 16#64 := by bv_omega

theorem write16_cast (a x y : BitVec 64) (h : 64 + 64 = 16 * 8) (s : Arm.ArmState) :
    Arm.write_mem_bytes 16 a (BitVec.cast h (x ++ y)) s = Arm.write_mem_bytes 16 a (x ++ y) s := by
  congr 1

/-- The state after a pre-indexed push of `n` bytes `v` (`sp -= 16`, then the store at `sp`). -/
def pushSt (s : Arm.ArmState) (n : Nat) (v : BitVec (n * 8)) : Arm.ArmState :=
  Arm.w .PC (Arm.r .PC s + 4#64)
    (Arm.w (.GPR 31#5) (spOf s - 16#64) (Arm.write_mem_bytes n (spOf s - 16#64) v s))

theorem exec_push_x (env : Env) {n : Nat} (hn : n < 29) (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.store .store64 (.x n) (.spPreIndexed (-16))).toArmInst env = .ok a ∧
      Arm.exec_inst a s = pushSt s 8 (Arm.r (.GPR (rnum n)) s) := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
      Reg.encZR, show n ≤ 30 by omega, rnum, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  simp [pushSt, Arm.exec_inst, Arm.LDST.exec_reg_imm_pre_indexed, Arm.LDST.exec_reg_imm_common,
    Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
    Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
    rnum_ne31 hn, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, hal', spOf,
    add_neg16p, Arm.write_gpr, rnum, show BitVec.ofNat 5 n ≠ 31#5 from rnum_ne31 hn]
  rfl

theorem exec_push_xx (env : Env) {a b : Nat} (ha : a < 29) (hb : b < 29) (s : Arm.ArmState)
    (hal : Arm.CheckSPAlignment s) :
    ∃ i, (Insn.stp (.x a) (.x b) (.spPreIndexed (-16))).toArmInst env = .ok i ∧
      Arm.exec_inst i s = pushSt s 16 (Arm.r (.GPR (rnum b)) s ++ Arm.r (.GPR (rnum a)) s) := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields,
      Reg.encZR, show a ≤ 30 by omega, show b ≤ 30 by omega, rnum, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  dsimp only [Arm.exec_inst, Arm.LDST.exec_reg_pair_pre_indexed, Arm.LDST.exec_reg_pair_common,
    Arm.LDST.reg_pair_operation]
  simp [pushSt, csimp_rules,
    Arm.LDST.reg_pair_constrain_unpredictable, Arm.ldst_read,
    Arm.CheckSPAlignment, hal', Arm.BitVec.lsb, add_neg16p, Arm.read_gpr_zr, Arm.read_gpr,
    show BitVec.ofNat 5 a ≠ 31#5 from rnum_ne31 ha, show BitVec.ofNat 5 b ≠ 31#5 from rnum_ne31 hb,
    Arm.read_pc, Arm.write_pc, Arm.write_gpr, spOf, rnum]
  refine congrArg (Arm.w .PC _) (congrArg (Arm.w (.GPR 31#5) _)
    (congrArg (fun v => Arm.write_mem_bytes 16 _ v s) ?_))
  apply BitVec.eq_of_toNat_eq
  exact BitVec.toNat_cast rfl _

theorem exec_push_d (env : Env) {n : Nat} (hn : n < 32) (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.fpuStore .size64 (.v n) (.spPreIndexed (-16))).toArmInst env = .ok a ∧
      Arm.exec_inst a s = pushSt s 8 ((Arm.r (.SFP (rnum n)) s).setWidth 64) := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpLdstSize,
      Reg.encV, show n ≤ 31 by omega, rnum, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  simp [pushSt, Arm.exec_inst, Arm.LDST.exec_reg_imm_pre_indexed, Arm.LDST.exec_reg_imm_common,
    Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
    Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_sfp, Arm.read_gpr,
    Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, hal', spOf,
    add_neg16p, Arm.write_gpr, show Arm.LDST.supported_simd_reg_imm 3#2 0#2 = true by decide, rnum]
  rfl

theorem exec_push_dd (env : Env) {a b : Nat} (ha : a < 32) (hb : b < 32) (s : Arm.ArmState)
    (hal : Arm.CheckSPAlignment s) :
    ∃ i, (Insn.fpuStoreP .size64 (.v a) (.v b) (.spPreIndexed (-16))).toArmInst env = .ok i ∧
      Arm.exec_inst i s = pushSt s 16 ((Arm.r (.SFP (rnum b)) s).setWidth 64 ++
        (Arm.r (.SFP (rnum a)) s).setWidth 64) := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpOpc,
      ScalarSize.bytes, Reg.encV, show a ≤ 31 by omega, show b ≤ 31 by omega, rnum, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  simp [pushSt, csimp_rules, Arm.exec_inst, Arm.LDST.exec_reg_pair_pre_indexed, Arm.LDST.exec_reg_pair_common,
    Arm.LDST.reg_pair_operation, Arm.LDST.reg_pair_constrain_unpredictable, Arm.ldst_read,
    Arm.CheckSPAlignment, hal', Arm.BitVec.lsb, add_neg16p, Arm.read_sfp, Arm.read_gpr,
    Arm.read_pc, Arm.write_pc, Arm.write_gpr, spOf, rnum]
  rfl


/-- The state after a post-indexed pop (`sp += 16`) of 8 bytes into GPR `n`. -/
def popXSt (s : Arm.ArmState) (n : Nat) : Arm.ArmState :=
  Arm.w .PC (Arm.r .PC s + 4#64) (Arm.w (.GPR 31#5) (spOf s + 16#64)
    (Arm.w (.GPR (rnum n)) (Arm.read_mem_bytes 8 (spOf s) s) s))

theorem exec_pop_x (env : Env) {n : Nat} (hn : n < 29) (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.load .uload64 (.x n) (.spPostIndexed 16)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = popXSt s n := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
      Reg.encZR, show n ≤ 30 by omega, rnum, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  dsimp only [Arm.exec_inst, Arm.LDST.exec_reg_imm_post_indexed, Arm.LDST.exec_reg_imm_common,
    Arm.LDST.reg_imm_operation]
  simp [popXSt, Arm.LDST.Reg_offset.value,
    Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_write, Arm.write_gpr_zr, Arm.read_gpr,
    Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, hal', spOf,
    Arm.write_gpr, rnum, show BitVec.ofNat 5 n ≠ 31#5 from rnum_ne31 hn]
  refine congrArg (Arm.w .PC _) (congrArg (Arm.w (.GPR 31#5) _)
    (congrArg (fun v => Arm.w (.GPR (BitVec.ofNat 5 n)) v s) ?_))
  apply BitVec.eq_of_toNat_eq
  exact BitVec.toNat_cast rfl _

/-- The state after a post-indexed pop of 16 bytes into GPRs `a` (low) and `b` (high). -/
def popXXSt (s : Arm.ArmState) (a b : Nat) : Arm.ArmState :=
  Arm.w .PC (Arm.r .PC s + 4#64) (Arm.w (.GPR 31#5) (spOf s + 16#64)
    (Arm.w (.GPR (rnum b)) ((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 64 64)
      (Arm.w (.GPR (rnum a)) ((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 0 64) s)))

theorem exec_pop_xx (env : Env) {a b : Nat} (ha : a < 29) (hb : b < 29) (hab : a ≠ b)
    (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ i, (Insn.ldp (.x a) (.x b) (.spPostIndexed 16)).toArmInst env = .ok i ∧
      Arm.exec_inst i s = popXXSt s a b := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm,
      Reg.encZR, show a ≤ 30 by omega, show b ≤ 30 by omega, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  have hab' : BitVec.ofNat 5 a ≠ BitVec.ofNat 5 b := fun e => hab (by
    have := congrArg BitVec.toNat e; simp at this; omega)
  dsimp only [Arm.exec_inst, Arm.LDST.exec_reg_pair_post_indexed, Arm.LDST.exec_reg_pair_common,
    Arm.LDST.reg_pair_operation]
  simp [popXXSt, csimp_rules,
    Arm.LDST.reg_pair_constrain_unpredictable, Arm.ldst_write,
    Arm.CheckSPAlignment, hal', Arm.BitVec.lsb, Arm.write_gpr_zr, Arm.read_gpr,
    show BitVec.ofNat 5 a ≠ 31#5 from rnum_ne31 ha, show BitVec.ofNat 5 b ≠ 31#5 from rnum_ne31 hb,
    Arm.read_pc, Arm.write_pc, Arm.write_gpr, spOf, rnum, hab']

/-- The state after a post-indexed pop of 8 bytes into `d n` (the upper 64 bits cleared). -/
def popDSt (s : Arm.ArmState) (n : Nat) : Arm.ArmState :=
  Arm.w .PC (Arm.r .PC s + 4#64) (Arm.w (.GPR 31#5) (spOf s + 16#64)
    (Arm.w (.SFP (rnum n)) ((Arm.read_mem_bytes 8 (spOf s) s).setWidth 128) s))

theorem exec_pop_d (env : Env) {n : Nat} (hn : n < 32) (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.fpuLoad .size64 (.v n) (.spPostIndexed 16)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = popDSt s n := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpLdstSize,
      Reg.encV, show n ≤ 31 by omega, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  dsimp only [Arm.exec_inst, Arm.LDST.exec_reg_imm_post_indexed, Arm.LDST.exec_reg_imm_common,
    Arm.LDST.reg_imm_operation]
  simp [popDSt, Arm.LDST.Reg_offset.value,
    Arm.LDST.reg_imm_constrain_unpredictable, Arm.write_sfp, Arm.read_gpr,
    Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, hal', spOf,
    Arm.write_gpr, rnum, show Arm.LDST.supported_simd_reg_imm 3#2 1#2 = true by decide]
  refine congrArg (Arm.w .PC _) (congrArg (Arm.w (.GPR 31#5) _)
    (congrArg (fun v => Arm.w (.SFP (BitVec.ofNat 5 n)) (BitVec.setWidth 128 v) s) ?_))
  apply BitVec.eq_of_toNat_eq
  exact BitVec.toNat_cast rfl _

/-- The state after a post-indexed pop of 16 bytes into `d a` (low) and `d b` (high). -/
def popDDSt (s : Arm.ArmState) (a b : Nat) : Arm.ArmState :=
  Arm.w .PC (Arm.r .PC s + 4#64) (Arm.w (.GPR 31#5) (spOf s + 16#64)
    (Arm.w (.SFP (rnum b)) (((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 64 64).setWidth 128)
      (Arm.w (.SFP (rnum a)) (((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 0 64).setWidth 128) s)))

theorem exec_pop_dd (env : Env) {a b : Nat} (ha : a < 32) (hb : b < 32) (hab : a ≠ b)
    (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ i, (Insn.fpuLoadP .size64 (.v a) (.v b) (.spPostIndexed 16)).toArmInst env = .ok i ∧
      Arm.exec_inst i s = popDDSt s a b := by
  refine ⟨_, by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Insn.armFields.fpOpc,
      ScalarSize.bytes, Reg.encV, show a ≤ 31 by omega, show b ≤ 31 by omega, sField]; rfl, ?_⟩
  have hal' := spAligned hal
  have hab' : BitVec.ofNat 5 a ≠ BitVec.ofNat 5 b := fun e => hab (by
    have := congrArg BitVec.toNat e; simp at this; omega)
  dsimp only [Arm.exec_inst, Arm.LDST.exec_reg_pair_post_indexed, Arm.LDST.exec_reg_pair_common,
    Arm.LDST.reg_pair_operation]
  simp [popDDSt, csimp_rules,
    Arm.LDST.reg_pair_constrain_unpredictable, Arm.ldst_write,
    Arm.CheckSPAlignment, hal', Arm.BitVec.lsb, Arm.write_sfp, Arm.read_gpr,
    Arm.read_pc, Arm.write_pc, Arm.write_gpr, spOf, rnum, hab']


/-! ## Bytes -/

/-- The low 8 bytes of a 16-byte read. -/
theorem read8_low (a : BitVec 64) (s : Arm.ArmState) :
    Arm.read_mem_bytes 8 a s = (Arm.read_mem_bytes 16 a s).setWidth 64 := by
  simp only [Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, Arm.Memory.getLsbD_read_bytes (by decide),
    Arm.Memory.getLsbD_read_bytes (by decide)]
  simp [hi, show i < 128 by omega]

/-- The two halves of a 16-byte read. -/
theorem read16_split {a : BitVec 64} {s : Arm.ArmState} {x y : BitVec 64}
    (h : Arm.read_mem_bytes 16 a s = x ++ y) :
    Arm.read_mem_bytes 8 a s = y ∧ Arm.read_mem_bytes 8 (a + 8#64) s = x := by
  refine ⟨by
    rw [read8_low, h]; apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]; simp [hi], ?_⟩
  simp only [Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes] at h ⊢
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (·.getLsbD (i + 64)) h
  simp only [Arm.Memory.getLsbD_read_bytes (show 16 ≤ 2 ^ 64 by decide),
    BitVec.getLsbD_append] at hb
  rw [Arm.Memory.getLsbD_read_bytes (by decide)]
  have h1 : (i + 64) / 8 = i / 8 + 8 := by omega
  have h2 : (i + 64) % 8 = i % 8 := by omega
  rw [h1, h2] at hb
  simp only [show i + 64 < 16 * 8 by omega, decide_true, Bool.true_and,
    show ¬ i + 64 < 64 by omega, ite_false, Nat.add_sub_cancel] at hb
  simp only [show i < 8 * 8 by omega, decide_true, Bool.true_and]
  rw [← hb, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 8)]


theorem add_ofNat_ne {B : BitVec 64} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) :
    B + BitVec.ofNat 64 x ≠ B + BitVec.ofNat 64 y := by
  intro e
  have := congrArg BitVec.toNat ((BitVec.add_right_inj B).mp e)
  simp [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  exact h this

theorem add_ofNat_add (B : BitVec 64) (x y : Nat) :
    B + BitVec.ofNat 64 x + BitVec.ofNat 64 y = B + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- A read of `n` bytes from `s` at `a`, where `s` agrees on `[a, a + n)` with a write of `v`
there, is `v`. -/
theorem read_of_agree {s t : Arm.ArmState} {n : Nat} {a : BitVec 64} {v : BitVec (n * 8)}
    (hn : n ≤ 2 ^ 64)
    (h : ∀ k < n, s.mem (a + BitVec.ofNat 64 k) = (Arm.write_mem_bytes n a v t).mem (a + BitVec.ofNat 64 k)) :
    Arm.read_mem_bytes n a s = v := by
  rw [read_mem_bytes_congr n a h, Arm.read_mem_bytes_of_write_mem_bytes_same hn]

theorem pushSt_mem (s : Arm.ArmState) (n : Nat) (v : BitVec (n * 8)) :
    (pushSt s n v).mem = (Arm.write_mem_bytes n (spOf s - 16#64) v s).mem := by
  simp [pushSt, Arm.ArmState.mem_w_eq_mem]

theorem pushSt_facts (s : Arm.ArmState) (n : Nat) (v : BitVec (n * 8)) :
    Arm.r .PC (pushSt s n v) = Arm.r .PC s + 4#64 ∧ Arm.r .ERR (pushSt s n v) = Arm.r .ERR s ∧
      (pushSt s n v).program = s.program ∧ spOf (pushSt s n v) = spOf s - 16#64 ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f (pushSt s n v) = Arm.r f s := by
  simp only [pushSt, spOf]
  refine ⟨by simp [Arm.r_of_w_same], by simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes],
    by simp [Arm.w_program, Arm.write_mem_bytes_program], by simp [Arm.r_of_w_same, Arm.r_of_w_different],
    fun f h1 h2 => by simp [Arm.r_of_w_different, h1, h2, Arm.r_of_write_mem_bytes]⟩

/-! ## Registers of the pushes -/

/-- The 8 bytes the pushes store for a register (the low 64 bits of a `v` register). -/
def slotVal (s : Arm.ArmState) : Reg → BitVec 64
  | .x n => Arm.r (.GPR (rnum n)) s
  | .v n => (Arm.r (.SFP (rnum n)) s).setWidth 64
  | _ => 0

/-- A register the pushes of class `int` handle. -/
def PushReg (int : Bool) : Reg → Prop
  | .x n => int = true ∧ n < 29
  | .v n => int = false ∧ n < 32
  | _ => False

theorem slotVal_congr {s t : Arm.ArmState} {r : Reg} (h : ∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f t = Arm.r f s)
    (hr : PushReg int r) : slotVal t r = slotVal s r := by
  cases r with
  | x n => simp only [slotVal]; exact h _ (by simp) (fun e => rnum_ne31 hr.2 (Arm.StateField.GPR.inj e))
  | v n => simp only [slotVal]; rw [h _ (by simp) (by simp)]
  | _ => rfl

/-- The push of one register (`str`/`str d`). -/
theorem exec_push1 (env : Env) {int : Bool} {r : Reg} (hr : PushReg int r) (s : Arm.ArmState)
    (hal : Arm.CheckSPAlignment s) :
    ∃ a, (if int then Insn.store .store64 r (.spPreIndexed (-16))
        else Insn.fpuStore .size64 r (.spPreIndexed (-16))).toArmInst env = .ok a ∧
      Arm.exec_inst a s = pushSt s 8 (slotVal s r) := by
  cases r with
  | x n => obtain ⟨rfl, hn⟩ := hr; exact exec_push_x env hn s hal
  | v n => obtain ⟨rfl, hn⟩ := hr; exact exec_push_d env hn s hal
  | _ => exact hr.elim

/-- The push of a pair (`stp`/`stp d`). -/
theorem exec_push2 (env : Env) {int : Bool} {a b : Reg} (ha : PushReg int a) (hb : PushReg int b)
    (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ i, (if int then Insn.stp a b (.spPreIndexed (-16))
        else Insn.fpuStoreP .size64 a b (.spPreIndexed (-16))).toArmInst env = .ok i ∧
      Arm.exec_inst i s = pushSt s 16 (slotVal s b ++ slotVal s a) := by
  cases a with
  | x n =>
    cases b with
    | x m => obtain ⟨rfl, hn⟩ := ha; exact exec_push_xx env hn hb.2 s hal
    | v m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | _ => exact hb.elim
  | v n =>
    cases b with
    | x m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | v m => obtain ⟨rfl, hn⟩ := ha; exact exec_push_dd env hn hb.2 s hal
    | _ => exact hb.elim
  | _ => exact ha.elim

/-! ## `pairsOf` -/

theorem pairsOf_cons2 (a b : Reg) (rs : List Reg) :
    pairsOf (a :: b :: rs) = ((a, b) :: (pairsOf rs).1, (pairsOf rs).2) := rfl

theorem pairsOf_len : ∀ rs : List Reg,
    2 * (pairsOf rs).1.length + (if (pairsOf rs).2.isSome then 1 else 0) = rs.length
  | [] => rfl
  | [_] => rfl
  | a :: b :: rs => by
    rw [pairsOf_cons2]; simp only [List.length_cons]; have := pairsOf_len rs; omega

/-- Where register `rs[i]` sits in the pairs: pair `i / 2`, or the odd last one. -/
theorem pairsOf_get : ∀ (rs : List Reg) (i : Nat) (r : Reg), rs[i]? = some r →
    (∃ a b, (pairsOf rs).1[i / 2]? = some (a, b) ∧ (if i % 2 = 0 then a else b) = r) ∨
      ((pairsOf rs).2 = some r ∧ i = 2 * (pairsOf rs).1.length)
  | [], _, _, h => by simp at h
  | [x], i, r, h => by
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact .inr ⟨by rw [← h]; rfl, rfl⟩
    · simp at h
  | a :: b :: rs, i, r, h => by
    rw [pairsOf_cons2]
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact .inl ⟨a, b, rfl, by simpa using h⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
      exact .inl ⟨a, b, rfl, by simpa using h⟩
    · simp only [List.getElem?_cons_succ] at h
      rcases pairsOf_get rs i r h with ⟨a', b', h1, h2⟩ | ⟨h1, h2⟩
      · refine .inl ⟨a', b', ?_, ?_⟩
        · rw [show (i + 1 + 1) / 2 = i / 2 + 1 by omega]; simpa using h1
        · rw [show (i + 1 + 1) % 2 = i % 2 by omega]; exact h2
      · exact .inr ⟨h1, by simp only [List.length_cons]; omega⟩

theorem pairsOf_mem : ∀ (rs : List Reg),
    (∀ p ∈ (pairsOf rs).1, p.1 ∈ rs ∧ p.2 ∈ rs) ∧ (∀ r, (pairsOf rs).2 = some r → r ∈ rs)
  | [] => ⟨by simp [pairsOf], by simp [pairsOf]⟩
  | [x] => ⟨by simp [pairsOf], by simp [pairsOf]⟩
  | a :: b :: rs => by
    rw [pairsOf_cons2]
    obtain ⟨h1, h2⟩ := pairsOf_mem rs
    refine ⟨fun p hp => ?_, fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h2 r hr))⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · simp
    · obtain ⟨x, y⟩ := h1 p hp
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ x), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ y)⟩

theorem pairsOf_ne : ∀ (rs : List Reg), rs.Nodup → ∀ p ∈ (pairsOf rs).1, p.1 ≠ p.2
  | [], _ => by simp [pairsOf]
  | [x], _ => by simp [pairsOf]
  | a :: b :: rs, hnd => by
    rw [pairsOf_cons2]
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · intro e; simp only at e; subst e; simp at hnd
    · exact pairsOf_ne rs (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).2 p hp

theorem pushBytes_eq (rs : List Reg) :
    pushBytes rs.length = 16 * (pairsOf rs).1.length + (if (pairsOf rs).2.isSome then 16 else 0) := by
  have := pairsOf_len rs
  unfold pushBytes
  rcases h : (pairsOf rs).2 with _ | r <;> simp only [h, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ite_false, ite_true] at this ⊢ <;> omega

/-! ## The pushes -/

/-- The line of one pair push. -/
def pushLine2 (int : Bool) (p : Reg × Reg) : Line :=
  .ins (if int then .stp p.1 p.2 (.spPreIndexed (-16)) else .fpuStoreP .size64 p.1 p.2 (.spPreIndexed (-16)))

theorem pushLines_eq (int : Bool) (rs : List Reg) :
    pushLines int rs = (match (pairsOf rs).2 with
      | some r => [.ins (if int then .store .store64 r (.spPreIndexed (-16))
          else .fpuStore .size64 r (.spPreIndexed (-16)))]
      | none => []) ++ (pairsOf rs).1.reverse.map (pushLine2 int) := rfl

theorem checkSP_of {s : Arm.ArmState} (h : (spOf s).toNat % 16 = 0) : Arm.CheckSPAlignment s := by
  simp only [Arm.CheckSPAlignment, Arm.read_gpr, Arm.Aligned, spOf, BitVec.setWidth_eq] at h ⊢
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.extractLsb'_toNat] using h

theorem sub16_mod {x : BitVec 64} (h : x.toNat % 16 = 0) : (x - 16#64).toNat % 16 = 0 := by
  rw [BitVec.toNat_sub]; have := x.isLt; simp; omega

theorem add16_sub (B : BitVec 64) (m : Nat) :
    B + BitVec.ofNat 64 (16 * (m + 1)) - 16#64 = B + BitVec.ofNat 64 (16 * m) := by
  rw [show 16 * (m + 1) = 16 * m + 16 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem aligned_add {B : BitVec 64} (hB : B.toNat % 16 = 0) (m : Nat) :
    (B + BitVec.ofNat 64 (16 * m)).toNat % 16 = 0 := by
  have h16 : (16 : Nat) ∣ 2 ^ 64 := ⟨2 ^ 60, rfl⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ h16, Nat.add_mod,
    Nat.mod_mod_of_dvd _ h16]
  omega

/-- The memory of a push at base `B` (`sp = B + 16`) differs from the state before it only at
`[B, B + 16)`. -/
theorem pushSt_mem_outside {s : Arm.ArmState} {n : Nat} {v : BitVec (n * 8)} {B : BitVec 64}
    (hsp : spOf s - 16#64 = B) (hn : n ≤ 16) {a : BitVec 64} (ha : ∀ k < 16, a ≠ B + BitVec.ofNat 64 k) :
    (pushSt s n v).mem a = s.mem a := by
  rw [pushSt_mem, Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
  exact write_bytes_outside n _ _ _ (fun k hk e => ha k (by omega) (by rw [← hsp]; exact e))

/-- **The pair pushes** run from the highest pair down: from `sp = B + 16 len`, pair `j` lands
at `B + 16 j`. -/
theorem pushPairs_ok (env : Env) (int : Bool) : ∀ (ps : List (Reg × Reg)) (s : Arm.ArmState)
    (B : BitVec 64), (∀ p ∈ ps, PushReg int p.1 ∧ PushReg int p.2) → 16 * ps.length < 2 ^ 64 →
    B.toNat % 16 = 0 → spOf s = B + BitVec.ofNat 64 (16 * ps.length) →
    ∃ s', StepsOk env (ps.reverse.map (pushLine2 int)) s s' ∧ spOf s' = B ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f s' = Arm.r f s) ∧
      Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program ∧
      (∀ a, (∀ k < 16 * ps.length, a ≠ B + BitVec.ofNat 64 k) → s'.mem a = s.mem a) ∧
      (∀ j a b, ps[j]? = some (a, b) →
        Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (16 * j)) s' = slotVal s a ∧
        Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (16 * j + 8)) s' = slotVal s b)
  | [], s, B, _, _, _, hsp => ⟨s, rfl, by simpa using hsp, fun _ _ _ => rfl, rfl, rfl,
      fun _ _ => rfl, by simp⟩
  | p :: ps, s, B, hps, hlen, hB, hsp => by
    simp only [List.length_cons] at hlen hsp ⊢
    have hsp' : spOf s = (B + 16#64) + BitVec.ofNat 64 (16 * ps.length) := by
      rw [hsp, show 16 * (ps.length + 1) = 16 + 16 * ps.length by omega, BitVec.ofNat_add,
        BitVec.add_assoc]
    obtain ⟨s1, h1, hsp1, hr1, he1, hp1, hm1, hv1⟩ :=
      pushPairs_ok env int ps s (B + 16#64) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (by omega)
        (by simpa using aligned_add hB 1) hsp'
    have hB1 : spOf s1 - 16#64 = B := by rw [hsp1]; exact BitVec.add_sub_cancel _ _
    have hal1 : Arm.CheckSPAlignment s1 := checkSP_of (by rw [hsp1]; simpa using aligned_add hB 1)
    obtain ⟨i, hi, he⟩ := exec_push2 { env with pc := env.pc + 4 * (ps.reverse.map (pushLine2 int)).length }
      (hps p (by simp)).1 (hps p (by simp)).2 s1 hal1
    obtain ⟨f1, f2, f3, f4, f5⟩ := pushSt_facts s1 16 (slotVal s1 p.2 ++ slotVal s1 p.1)
    have hreg : ∀ r, PushReg int r → slotVal s1 r = slotVal s r := fun r hr => slotVal_congr hr1 hr
    refine ⟨Arm.exec_inst i s1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.reverse_cons, List.map_append]
      refine StepsOk.append h1 ?_
      simp only [List.map_cons, List.map_nil, pushLine2]
      refine steps_cons hi ?_ ?_ ?_ rfl <;> rw [he]
      · exact f1
      · exact f2
      · exact f3
    · rw [he, f4, hB1]
    · intro f h1' h2'; rw [he, f5 f h1' h2', hr1 f h1' h2']
    · rw [he, f2, he1]
    · rw [he, f3, hp1]
    · intro a ha
      rw [he, pushSt_mem_outside hB1 (Nat.le_refl _) (fun k hk => ha k (by omega))]
      apply hm1
      intro k hk e
      apply ha (16 + k) (by omega)
      rw [e, show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
    · intro j a b hj
      rcases j with _ | j
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        have hrd : Arm.read_mem_bytes 16 B (Arm.exec_inst i s1) = slotVal s1 b ++ slotVal s1 a := by
          rw [he, ← hB1]
          exact read_of_agree (by decide) (fun k _ => by rw [pushSt_mem])
        obtain ⟨r1, r2⟩ := read16_split hrd
        refine ⟨by simpa using r1.trans (hreg _ (hps (a, b) (by simp)).1), ?_⟩
        rw [← r2.trans (hreg _ (hps (a, b) (by simp)).2)]
      · simp only [List.getElem?_cons_succ] at hj
        obtain ⟨v1, v2⟩ := hv1 j a b hj
        have key : ∀ o, o + 8 ≤ 16 → ∀ (v : BitVec 64),
            Arm.read_mem_bytes 8 (B + 16#64 + BitVec.ofNat 64 (16 * j + o)) s1 = v →
            Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (16 * (j + 1) + o)) (Arm.exec_inst i s1) = v := by
          intro o ho v hv
          rw [← hv, show B + 16#64 + BitVec.ofNat 64 (16 * j + o) = B + BitVec.ofNat 64 (16 * (j + 1) + o) by
            rw [show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; congr 2; omega]
          apply read_mem_bytes_congr
          intro k hk
          rw [he, pushSt_mem_outside hB1 (Nat.le_refl _) (fun k' hk' e => ?_)]
          rw [add_ofNat_add] at e
          have hlt : j < ps.length := (List.getElem?_eq_some_iff.1 hj).1
          exact add_ofNat_ne (by omega) (by omega) (by omega) e
        exact ⟨key 0 (by omega) _ (by simpa using v1), key 8 (by omega) _ v2⟩

/-- **The pushes of one register class**: from `sp = B + pushBytes`, register `rs[i]`'s low 64
bits land at `B + 8 i`; only `[B, B + pushBytes)` is written. -/
theorem pushLines_ok (env : Env) (int : Bool) (rs : List Reg) (s : Arm.ArmState) (B : BitVec 64)
    (hrs : ∀ r ∈ rs, PushReg int r) (hlen : rs.length ≤ 64) (hB : B.toNat % 16 = 0)
    (hsp : spOf s = B + BitVec.ofNat 64 (pushBytes rs.length)) :
    ∃ s', StepsOk env (pushLines int rs) s s' ∧ spOf s' = B ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f s' = Arm.r f s) ∧
      Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program ∧
      (∀ a, (∀ k < pushBytes rs.length, a ≠ B + BitVec.ofNat 64 k) → s'.mem a = s.mem a) ∧
      (∀ i r, rs[i]? = some r → Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (8 * i)) s' = slotVal s r) := by
  have hl := pairsOf_len rs
  have hpb := pushBytes_eq rs
  obtain ⟨hmP, hmO⟩ := pairsOf_mem rs
  have hpv : ∀ p ∈ (pairsOf rs).1, PushReg int p.1 ∧ PushReg int p.2 :=
    fun p hp => ⟨hrs _ (hmP p hp).1, hrs _ (hmP p hp).2⟩
  have hPl : 16 * (pairsOf rs).1.length < 2 ^ 64 := by split at hl <;> omega
  -- the slot of `rs[i]` in the pairs
  have hslot : ∀ (t : Arm.ArmState) i r, rs[i]? = some r →
      (∀ j a b, (pairsOf rs).1[j]? = some (a, b) →
        Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (16 * j)) t = slotVal s a ∧
        Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (16 * j + 8)) t = slotVal s b) →
      ((pairsOf rs).2 = some r → i = 2 * (pairsOf rs).1.length →
        Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (8 * i)) t = slotVal s r) →
      Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (8 * i)) t = slotVal s r := by
    intro t i r hi hP hO
    rcases pairsOf_get rs i r hi with ⟨a, b, h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨v1, v2⟩ := hP _ a b h1
      by_cases h0 : i % 2 = 0
      · rw [if_pos h0] at h2; subst h2
        rw [show 8 * i = 16 * (i / 2) by omega]; exact v1
      · rw [if_neg h0] at h2; subst h2
        rw [show 8 * i = 16 * (i / 2) + 8 by omega]; exact v2
    · exact hO h1 h2
  rw [pushLines_eq]
  rcases ho : (pairsOf rs).2 with _ | r0
  · simp only [ho, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hpb
    rw [hpb] at hsp
    obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := pushPairs_ok env int _ s B hpv hPl hB hsp
    refine ⟨s', by simpa using h1, h2, h3, h4, h5, fun a ha => h6 a (fun k hk => ha k (by omega)),
      fun i r hi => hslot s' i r hi h7 (fun h => by rw [ho] at h; cases h)⟩
  · simp only [ho, Option.isSome_some, ite_true] at hpb
    rw [hpb] at hsp
    have hr0 : PushReg int r0 := hrs _ (hmO r0 ho)
    have hal : Arm.CheckSPAlignment s := checkSP_of (by
      rw [hsp, show 16 * (pairsOf rs).1.length + 16 = 16 * ((pairsOf rs).1.length + 1) by omega]
      exact aligned_add hB _)
    obtain ⟨i0, hi0, he0⟩ := exec_push1 env hr0 s hal
    obtain ⟨f1, f2, f3, f4, f5⟩ := pushSt_facts s 8 (slotVal s r0)
    have hsp1 : spOf (Arm.exec_inst i0 s) = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length) := by
      rw [he0, f4, hsp, show 16 * (pairsOf rs).1.length + 16 = 16 * ((pairsOf rs).1.length + 1) by omega]
      exact add16_sub _ _
    obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := pushPairs_ok _ int _ _ B hpv hPl hB hsp1
    have hT : spOf s - 16#64 = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length) := by
      rw [← hsp1, he0, f4]
    refine ⟨s', steps_cons hi0 (by rw [he0]; exact f1) (by rw [he0]; exact f2) (by rw [he0]; exact f3) h1,
      h2, fun f g1 g2 => by rw [h3 f g1 g2, he0, f5 f g1 g2], by rw [h4, he0, f2],
      by rw [h5, he0, f3], fun a ha => ?_, fun i r hi => hslot s' i r hi
        (fun j a b hj => by
          obtain ⟨v1, v2⟩ := h7 j a b hj
          rw [he0] at v1 v2
          exact ⟨v1.trans (slotVal_congr f5 (hpv _ (List.mem_of_getElem? hj)).1),
            v2.trans (slotVal_congr f5 (hpv _ (List.mem_of_getElem? hj)).2)⟩)
        (fun h hi2 => ?_)⟩
    · rw [h6 a (fun k hk => ha k (by omega)), he0]
      exact pushSt_mem_outside hT (by omega) (fun k hk e => ha (16 * (pairsOf rs).1.length + k)
        (by omega) (by rw [e, add_ofNat_add]))
    · rw [ho] at h; cases h
      rw [hi2, show 8 * (2 * (pairsOf rs).1.length) = 16 * (pairsOf rs).1.length by omega]
      apply read_of_agree (t := s) (by decide)
      intro k hk
      rw [h6 _ (fun k' hk' e => add_ofNat_ne (by omega) (by omega) (by omega)
        ((add_ofNat_add _ _ _).symm.trans e)), he0, pushSt_mem, hT]

/-! ## The pops -/

/-- A 16-byte read is the 8 bytes above over the 8 bytes below. -/
theorem read16_eq (a : BitVec 64) (s : Arm.ArmState) :
    Arm.read_mem_bytes 16 a s = Arm.read_mem_bytes 8 (a + 8#64) s ++ Arm.read_mem_bytes 8 a s := by
  have h : Arm.read_mem_bytes 16 a s = (Arm.read_mem_bytes 16 a s).extractLsb' 64 64 ++
      (Arm.read_mem_bytes 16 a s).extractLsb' 0 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases h : i < 64
    · simp [h]
    · simp only [h, ite_false]
      rw [show 64 + (i - 64) = i by omega, show decide (i - 64 < 64) = true by
        simp only [decide_eq_true_eq]; omega, Bool.true_and]
  obtain ⟨h1, h2⟩ := read16_split h
  rw [h, h1, h2]

theorem read16_lo (a : BitVec 64) (s : Arm.ArmState) :
    (Arm.read_mem_bytes 16 a s).extractLsb' 0 64 = Arm.read_mem_bytes 8 a s := by
  rw [read16_eq, BitVec.extractLsb'_append_eq_right]

theorem read16_hi (a : BitVec 64) (s : Arm.ArmState) :
    (Arm.read_mem_bytes 16 a s).extractLsb' 64 64 = Arm.read_mem_bytes 8 (a + 8#64) s := by
  rw [read16_eq, BitVec.extractLsb'_append_eq_left]

/-- The value a pop leaves in register `r` from the 8 bytes `v` (a `v` register gets them
zero-extended). -/
def PopVal (t : Arm.ArmState) : Reg → BitVec 64 → Prop
  | .x n, v => Arm.r (.GPR (rnum n)) t = v
  | .v n, v => Arm.r (.SFP (rnum n)) t = v.setWidth 128
  | _, _ => True

/-- `PopVal` survives writes of other fields. -/
theorem popVal_congr {t t' : Arm.ArmState} {r : Reg} {v : BitVec 64}
    (h : ∀ f, r.field = some f → Arm.r f t' = Arm.r f t) (hv : PopVal t r v) : PopVal t' r v := by
  cases r <;> simp only [PopVal, Reg.field] at h hv ⊢ <;> first | trivial | rw [h _ rfl]; exact hv

/-- The pop of one register (`ldr`/`ldr d`). -/
theorem exec_pop1 (env : Env) {int : Bool} {r : Reg} (hr : PushReg int r) (s : Arm.ArmState)
    (hal : Arm.CheckSPAlignment s) :
    ∃ a, (if int then Insn.load .uload64 r (.spPostIndexed 16)
        else Insn.fpuLoad .size64 r (.spPostIndexed 16)).toArmInst env = .ok a ∧
      Arm.r .PC (Arm.exec_inst a s) = Arm.r .PC s + 4#64 ∧
      Arm.r .ERR (Arm.exec_inst a s) = Arm.r .ERR s ∧ (Arm.exec_inst a s).program = s.program ∧
      spOf (Arm.exec_inst a s) = spOf s + 16#64 ∧ (Arm.exec_inst a s).mem = s.mem ∧
      PopVal (Arm.exec_inst a s) r (Arm.read_mem_bytes 8 (spOf s) s) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 31#5 → r.field ≠ some f → Arm.r f (Arm.exec_inst a s) = Arm.r f s := by
  cases r with
  | x n =>
    obtain ⟨rfl, hn⟩ := hr
    obtain ⟨a, ha, he⟩ := exec_pop_x env hn s hal
    refine ⟨a, ha, ?_⟩
    rw [he]
    have h31 : Arm.StateField.GPR (rnum n) ≠ .GPR 31#5 := fun e => rnum_ne31 hn (Arm.StateField.GPR.inj e)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun f g1 g2 g3 => ?_⟩
    rotate_left 6
    · simp only [Reg.field, ne_eq, Option.some.injEq] at g3
      simp only [popXSt]
      rw [Arm.r_of_w_different g1, Arm.r_of_w_different g2, Arm.r_of_w_different (Ne.symm g3)]
    all_goals simp [popXSt, spOf, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program,
        Arm.ArmState.mem_w_eq_mem, PopVal, h31]
  | v n =>
    obtain ⟨rfl, hn⟩ := hr
    obtain ⟨a, ha, he⟩ := exec_pop_d env hn s hal
    refine ⟨a, ha, ?_⟩
    rw [he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun f g1 g2 g3 => ?_⟩
    rotate_left 6
    · simp only [Reg.field, ne_eq, Option.some.injEq] at g3
      simp only [popDSt]
      rw [Arm.r_of_w_different g1, Arm.r_of_w_different g2, Arm.r_of_w_different (Ne.symm g3)]
    all_goals simp [popDSt, spOf, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program,
        Arm.ArmState.mem_w_eq_mem, PopVal]
  | _ => exact hr.elim

/-- The pop of a pair (`ldp`/`ldp d`). -/
theorem exec_pop2 (env : Env) {int : Bool} {a b : Reg} (ha : PushReg int a) (hb : PushReg int b)
    (hab : a ≠ b) (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    ∃ i, (if int then Insn.ldp a b (.spPostIndexed 16)
        else Insn.fpuLoadP .size64 a b (.spPostIndexed 16)).toArmInst env = .ok i ∧
      Arm.r .PC (Arm.exec_inst i s) = Arm.r .PC s + 4#64 ∧
      Arm.r .ERR (Arm.exec_inst i s) = Arm.r .ERR s ∧ (Arm.exec_inst i s).program = s.program ∧
      spOf (Arm.exec_inst i s) = spOf s + 16#64 ∧ (Arm.exec_inst i s).mem = s.mem ∧
      PopVal (Arm.exec_inst i s) a (Arm.read_mem_bytes 8 (spOf s) s) ∧
      PopVal (Arm.exec_inst i s) b (Arm.read_mem_bytes 8 (spOf s + 8#64) s) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 31#5 → a.field ≠ some f → b.field ≠ some f →
        Arm.r f (Arm.exec_inst i s) = Arm.r f s := by
  cases a with
  | x n =>
    cases b with
    | x m =>
      obtain ⟨rfl, hn⟩ := ha
      have hnm : n ≠ m := fun e => hab (by rw [e])
      obtain ⟨i, hi, he⟩ := exec_pop_xx env hn hb.2 hnm s hal
      refine ⟨i, hi, ?_⟩
      rw [he]
      have h31 : Arm.StateField.GPR (rnum n) ≠ .GPR 31#5 := fun e => rnum_ne31 hn (Arm.StateField.GPR.inj e)
      have h31' : Arm.StateField.GPR (rnum m) ≠ .GPR 31#5 := fun e => rnum_ne31 hb.2 (Arm.StateField.GPR.inj e)
      have hnm' : Arm.StateField.GPR (rnum n) ≠ .GPR (rnum m) := fun e =>
        hnm (by have := congrArg BitVec.toNat (Arm.StateField.GPR.inj e)
                rwa [rnum_toNat (by omega), rnum_toNat (by have := hb.2; omega)] at this)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun f g1 g2 g3 g4 => ?_⟩
      rotate_left 7
      · simp only [Reg.field, ne_eq, Option.some.injEq] at g3 g4
        simp only [popXXSt]
        rw [Arm.r_of_w_different g1, Arm.r_of_w_different g2, Arm.r_of_w_different (Ne.symm g4),
          Arm.r_of_w_different (Ne.symm g3)]
      all_goals simp [popXXSt, spOf, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program,
          Arm.ArmState.mem_w_eq_mem, PopVal, h31, h31', hnm', Ne.symm hnm', read16_lo, read16_hi]
    | v m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | _ => exact hb.elim
  | v n =>
    cases b with
    | x m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | v m =>
      obtain ⟨rfl, hn⟩ := ha
      have hnm : n ≠ m := fun e => hab (by rw [e])
      obtain ⟨i, hi, he⟩ := exec_pop_dd env hn hb.2 hnm s hal
      refine ⟨i, hi, ?_⟩
      rw [he]
      have hnm' : Arm.StateField.SFP (rnum n) ≠ .SFP (rnum m) := fun e =>
        hnm (by have := congrArg BitVec.toNat (Arm.StateField.SFP.inj e)
                rwa [rnum_toNat hn, rnum_toNat hb.2] at this)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun f g1 g2 g3 g4 => ?_⟩
      rotate_left 7
      · simp only [Reg.field, ne_eq, Option.some.injEq] at g3 g4
        simp only [popDDSt]
        rw [Arm.r_of_w_different g1, Arm.r_of_w_different g2, Arm.r_of_w_different (Ne.symm g4),
          Arm.r_of_w_different (Ne.symm g3)]
      all_goals simp [popDDSt, spOf, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program,
          Arm.ArmState.mem_w_eq_mem, PopVal, hnm', Ne.symm hnm', read16_lo, read16_hi]
    | _ => exact hb.elim
  | _ => exact ha.elim

theorem pairsOf_flat : ∀ rs : List Reg,
    ((pairsOf rs).1.flatMap fun p => [p.1, p.2]) ++ (pairsOf rs).2.toList = rs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rs => by
    rw [pairsOf_cons2]; simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    rw [pairsOf_flat rs]

theorem field_inj {int : Bool} {r r' : Reg} (hr : PushReg int r) (hr' : PushReg int r') {f : Arm.StateField}
    (h : r.field = some f) (h' : r'.field = some f) : r = r' := by
  cases r with
  | x n =>
    cases r' with
    | x m =>
      simp only [Reg.field, Option.some.injEq] at h h'
      have := congrArg BitVec.toNat (Arm.StateField.GPR.inj (h.trans h'.symm))
      rw [rnum_toNat (by have := hr.2; omega), rnum_toNat (by have := hr'.2; omega)] at this
      rw [this]
    | v m => simp only [Reg.field, Option.some.injEq] at h h'; subst h; cases h'
    | _ => exact hr'.elim
  | v n =>
    cases r' with
    | x m => simp only [Reg.field, Option.some.injEq] at h h'; subst h; cases h'
    | v m =>
      simp only [Reg.field, Option.some.injEq] at h h'
      have := congrArg BitVec.toNat (Arm.StateField.SFP.inj (h.trans h'.symm))
      rw [rnum_toNat hr.2, rnum_toNat hr'.2] at this
      rw [this]
    | _ => exact hr'.elim
  | _ => exact hr.elim

theorem field_ne_pc_sp {int : Bool} {r : Reg} (hr : PushReg int r) {f : Arm.StateField}
    (h : r.field = some f) : f ≠ .PC ∧ f ≠ .GPR 31#5 := by
  cases r <;> simp only [Reg.field, Option.some.injEq, PushReg] at h hr <;> subst h
  · exact ⟨by simp, fun e => rnum_ne31 hr.2 (Arm.StateField.GPR.inj e)⟩
  · exact ⟨by simp, by simp⟩
  all_goals exact hr.elim

/-- The line of one pair pop. -/
def popLine2 (int : Bool) (p : Reg × Reg) : Line :=
  .ins (if int then .ldp p.1 p.2 (.spPostIndexed 16) else .fpuLoadP .size64 p.1 p.2 (.spPostIndexed 16))

theorem popLines_eq (int : Bool) (rs : List Reg) :
    popLines int rs = (pairsOf rs).1.map (popLine2 int) ++ (match (pairsOf rs).2 with
      | some r => [.ins (if int then .load .uload64 r (.spPostIndexed 16)
          else .fpuLoad .size64 r (.spPostIndexed 16))]
      | none => []) := rfl

theorem read_of_mem_eq {s t : Arm.ArmState} (h : s.mem = t.mem) (n : Nat) (a : BitVec 64) :
    Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a t :=
  read_mem_bytes_congr n a (fun k _ => by rw [h])

/-- **The pair pops** run from the lowest pair up: pair `j` is read from `B + 16 j`. -/
theorem popPairs_ok (env : Env) (int : Bool) : ∀ (ps : List (Reg × Reg)) (s : Arm.ArmState)
    (B : BitVec 64), (∀ p ∈ ps, PushReg int p.1 ∧ PushReg int p.2) →
    (ps.flatMap fun p => [p.1, p.2]).Nodup → B.toNat % 16 = 0 → spOf s = B →
    ∃ s', StepsOk env (ps.map (popLine2 int)) s s' ∧ spOf s' = B + BitVec.ofNat 64 (16 * ps.length) ∧
      s'.mem = s.mem ∧ Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → (∀ p ∈ ps, p.1.field ≠ some f ∧ p.2.field ≠ some f) →
        Arm.r f s' = Arm.r f s) ∧
      (∀ j a b, ps[j]? = some (a, b) →
        PopVal s' a (Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (16 * j)) s) ∧
        PopVal s' b (Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (16 * j + 8)) s))
  | [], s, B, _, _, _, hsp => ⟨s, rfl, by simpa using hsp, rfl, rfl, rfl, fun _ _ _ _ => rfl, by simp⟩
  | p :: ps, s, B, hps, hnd, hB, hsp => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    obtain ⟨⟨hne, hn1⟩, hn2, hnd⟩ := hnd
    have hp := hps p (by simp)
    obtain ⟨i, hi, f1, f2, f3, f4, f5, v1, v2, fo⟩ :=
      exec_pop2 env hp.1 hp.2 hne s (checkSP_of (by rw [hsp]; exact hB))
    obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := popPairs_ok
      { env with pc := env.pc + 4 } int ps (Arm.exec_inst i s) (B + 16#64)
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hnd (by simpa using aligned_add hB 1)
      (by rw [f4, hsp])
    have hnotin : ∀ r, (r = p.1 ∨ r = p.2) → ∀ f, r.field = some f →
        ∀ q ∈ ps, q.1.field ≠ some f ∧ q.2.field ≠ some f := by
      intro r hr f hf q hq
      have hq' := hps q (List.mem_cons_of_mem _ hq)
      have hm1 : q.1 ∈ ps.flatMap fun p => [p.1, p.2] := List.mem_flatMap.2 ⟨q, hq, by simp⟩
      have hm2 : q.2 ∈ ps.flatMap fun p => [p.1, p.2] := List.mem_flatMap.2 ⟨q, hq, by simp⟩
      rcases hr with rfl | rfl
      · refine ⟨fun e => hn1 ((field_inj hq'.1 hp.1 e hf) ▸ hm1),
          fun e => hn1 ((field_inj hq'.2 hp.1 e hf) ▸ hm2)⟩
      · refine ⟨fun e => hn2 ((field_inj hq'.1 hp.2 e hf) ▸ hm1),
          fun e => hn2 ((field_inj hq'.2 hp.2 e hf) ▸ hm2)⟩
    refine ⟨s', steps_cons hi f1 f2 f3 h1, ?_, by rw [h3, f5], by rw [h4, f2], by rw [h5, f3],
      fun f g1 g2 g3 => ?_, fun j a b hj => ?_⟩
    · rw [h2, show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
      simp only [List.length_cons]; congr 2; omega
    · rw [h6 f g1 g2 (fun q hq => g3 q (List.mem_cons_of_mem _ hq))]
      exact fo f g1 g2 (g3 p (by simp)).1 (g3 p (by simp)).2
    · rcases j with _ | j
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        refine ⟨popVal_congr (fun f hf => ?_) (by rw [hsp] at v1; simpa using v1),
          popVal_congr (fun f hf => ?_) (by rw [hsp] at v2; simpa using v2)⟩
        · obtain ⟨g1, g2⟩ := field_ne_pc_sp hp.1 hf
          exact h6 f g1 g2 (hnotin _ (.inl rfl) f hf)
        · obtain ⟨g1, g2⟩ := field_ne_pc_sp hp.2 hf
          exact h6 f g1 g2 (hnotin _ (.inr rfl) f hf)
      · simp only [List.getElem?_cons_succ] at hj
        obtain ⟨w1, w2⟩ := h7 j a b hj
        rw [read_of_mem_eq f5] at w1 w2
        have e1 : B + 16#64 + BitVec.ofNat 64 (16 * j) = B + BitVec.ofNat 64 (16 * (j + 1)) := by
          rw [show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; congr 2; omega
        have e2 : B + 16#64 + BitVec.ofNat 64 (16 * j + 8) = B + BitVec.ofNat 64 (16 * (j + 1) + 8) := by
          rw [show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; congr 2; omega
        rw [e1] at w1; rw [e2] at w2
        exact ⟨w1, w2⟩

/-- **The pops of one register class**: from `sp = B`, register `rs[i]` gets the 8 bytes at
`B + 8 i`; `sp` rises by `pushBytes`, memory is unchanged, and only the registers of `rs`
(besides the pc and `sp`) change. -/
theorem popLines_ok (env : Env) (int : Bool) (rs : List Reg) (s : Arm.ArmState) (B : BitVec 64)
    (hrs : ∀ r ∈ rs, PushReg int r) (hnd : rs.Nodup) (hB : B.toNat % 16 = 0) (hsp : spOf s = B) :
    ∃ s', StepsOk env (popLines int rs) s s' ∧ spOf s' = B + BitVec.ofNat 64 (pushBytes rs.length) ∧
      s'.mem = s.mem ∧ Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → (∀ r ∈ rs, r.field ≠ some f) → Arm.r f s' = Arm.r f s) ∧
      (∀ i r, rs[i]? = some r → PopVal s' r (Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (8 * i)) s)) := by
  have hl := pairsOf_len rs
  have hpb := pushBytes_eq rs
  have hfl := pairsOf_flat rs
  obtain ⟨hmP, hmO⟩ := pairsOf_mem rs
  have hpv : ∀ p ∈ (pairsOf rs).1, PushReg int p.1 ∧ PushReg int p.2 :=
    fun p hp => ⟨hrs _ (hmP p hp).1, hrs _ (hmP p hp).2⟩
  have hndP : ((pairsOf rs).1.flatMap fun p => [p.1, p.2]).Nodup := by
    rw [← hfl] at hnd; exact (List.nodup_append.1 hnd).1
  obtain ⟨s1, h1, h2, h3, h4, h5, h6, h7⟩ := popPairs_ok env int _ s B hpv hndP hB hsp
  have hmemP : ∀ p ∈ (pairsOf rs).1, p.1 ∈ rs ∧ p.2 ∈ rs := hmP
  -- the pairs' values
  have hpair : ∀ (t : Arm.ArmState), (∀ f, f ≠ .PC → f ≠ .GPR 31#5 →
        (∀ r, (pairsOf rs).2 = some r → r.field ≠ some f) → Arm.r f t = Arm.r f s1) →
      ∀ i r, rs[i]? = some r → (pairsOf rs).2 ≠ some r ∨ i ≠ 2 * (pairsOf rs).1.length →
        PopVal t r (Arm.read_mem_bytes 8 (B + BitVec.ofNat 64 (8 * i)) s) := by
    intro t ht i r hi hno
    rcases pairsOf_get rs i r hi with ⟨a, b, g1, g2⟩ | ⟨g1, g2⟩
    · obtain ⟨w1, w2⟩ := h7 _ a b g1
      have hab := hpv _ (List.mem_of_getElem? g1)
      have hnotodd : ∀ x, (x = a ∨ x = b) → ∀ f, x.field = some f → ∀ r', (pairsOf rs).2 = some r' →
          r'.field ≠ some f := by
        intro x hx f hf r' ho e
        have hx' : PushReg int x := by rcases hx with rfl | rfl; exact hab.1; exact hab.2
        have := field_inj (hrs _ (hmO r' ho)) hx' e hf
        subst this
        rw [← hfl] at hnd
        have hmx : r' ∈ (pairsOf rs).1.flatMap fun p => [p.1, p.2] :=
          List.mem_flatMap.2 ⟨(a, b), List.mem_of_getElem? g1, by rcases hx with rfl | rfl <;> simp⟩
        exact (List.nodup_append.1 hnd).2.2 _ hmx _ (by simp [ho]) rfl
      by_cases h0 : i % 2 = 0
      · rw [if_pos h0] at g2; subst g2
        rw [show 8 * i = 16 * (i / 2) by omega]
        exact popVal_congr (fun f hf => by
          obtain ⟨c1, c2⟩ := field_ne_pc_sp hab.1 hf
          exact ht f c1 c2 (hnotodd _ (.inl rfl) f hf)) w1
      · rw [if_neg h0] at g2; subst g2
        rw [show 8 * i = 16 * (i / 2) + 8 by omega]
        exact popVal_congr (fun f hf => by
          obtain ⟨c1, c2⟩ := field_ne_pc_sp hab.2 hf
          exact ht f c1 c2 (hnotodd _ (.inr rfl) f hf)) w2
    · rcases hno with h | h
      · exact absurd g1 h
      · exact absurd g2 h
  rw [popLines_eq]
  rcases ho : (pairsOf rs).2 with _ | r0
  · simp only [ho, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hpb
    refine ⟨s1, by simpa using h1, by rw [h2, hpb], h3, h4, h5, fun f g1 g2 g3 => ?_,
      fun i r hi => hpair s1 (fun _ _ _ _ => rfl) i r hi (.inl (by rw [ho]; simp))⟩
    exact h6 f g1 g2 (fun p hp => ⟨g3 _ (hmP p hp).1, g3 _ (hmP p hp).2⟩)
  · simp only [ho, Option.isSome_some, ite_true] at hpb
    have hr0 : PushReg int r0 := hrs _ (hmO r0 ho)
    have hal1 : Arm.CheckSPAlignment s1 := checkSP_of (by rw [h2]; exact aligned_add hB _)
    obtain ⟨i0, hi0, f1, f2, f3, f4, f5, v0, fo⟩ :=
      exec_pop1 { env with pc := env.pc + 4 * ((pairsOf rs).1.map (popLine2 int)).length } hr0 s1 hal1
    refine ⟨Arm.exec_inst i0 s1, StepsOk.append h1 (steps_cons hi0 f1 f2 f3 rfl), ?_, by rw [f5, h3],
      by rw [f2, h4], by rw [f3, h5], fun f g1 g2 g3 => ?_, fun i r hi => ?_⟩
    · rw [f4, h2, hpb, show (16#64) = BitVec.ofNat 64 16 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [fo f g1 g2 (g3 r0 (hmO r0 ho)), h6 f g1 g2 (fun p hp => ⟨g3 _ (hmP p hp).1, g3 _ (hmP p hp).2⟩)]
    · by_cases hodd : r = r0 ∧ i = 2 * (pairsOf rs).1.length
      · obtain ⟨rfl, rfl⟩ := hodd
        rw [h2, read_of_mem_eq h3] at v0
        rw [show 8 * (2 * (pairsOf rs).1.length) = 16 * (pairsOf rs).1.length by omega]
        exact v0
      · refine hpair _ (fun f g1 g2 g3 => fo f g1 g2 (g3 r0 ho)) i r hi ?_
        rw [ho]
        by_cases h : r = r0
        · exact .inr (fun e => hodd ⟨h, e⟩)
        · exact .inl (fun e => h (Option.some.inj e).symm)

/-! ## The reads of the pops -/

theorem memReads_pop1 {env : Env} {int : Bool} {r : Reg} (hr : PushReg int r) {a : Arm.ArmInst}
    (h : (if int then Insn.load .uload64 r (.spPostIndexed 16)
        else Insn.fpuLoad .size64 r (.spPostIndexed 16)).toArmInst env = .ok a) (s : Arm.ArmState) :
    E2E.ExecBytes.MemReads a s = [(spOf s, 8)] := by
  cases r with
  | x n =>
    obtain ⟨rfl, hn⟩ := hr
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
      Reg.encZR, show n ≤ 30 by omega, sField] at h
    subst h
    simp (config := {decide := true}) [E2E.ExecBytes.MemReads, E2E.ExecFrame.RegImm.reads, E2E.ExecFrame.RegImm.ofPost,
      E2E.ExecFrame.RegImm.memop, E2E.ExecFrame.RegImm.addr, E2E.ExecFrame.RegImm.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr]
  | v n =>
    obtain ⟨rfl, hn⟩ := hr
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpLdstSize,
      Reg.encV, show n ≤ 31 by omega, sField] at h
    subst h
    simp (config := {decide := true}) [E2E.ExecBytes.MemReads, E2E.ExecFrame.RegImm.reads, E2E.ExecFrame.RegImm.ofPost,
      E2E.ExecFrame.RegImm.memop, E2E.ExecFrame.RegImm.addr, E2E.ExecFrame.RegImm.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr]
  | _ => exact hr.elim

theorem memReads_pop2 {env : Env} {int : Bool} {a b : Reg} (ha : PushReg int a) (hb : PushReg int b)
    {i : Arm.ArmInst}
    (h : (if int then Insn.ldp a b (.spPostIndexed 16)
        else Insn.fpuLoadP .size64 a b (.spPostIndexed 16)).toArmInst env = .ok i) (s : Arm.ArmState) :
    E2E.ExecBytes.MemReads i s = [(spOf s, 16)] := by
  cases a with
  | x n =>
    cases b with
    | x m =>
      obtain ⟨rfl, hn⟩ := ha
      have hm := hb.2
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm,
        Reg.encZR, show n ≤ 30 by omega, show m ≤ 30 by omega, sField] at h
      subst h
      simp (config := {decide := true}) [E2E.ExecBytes.MemReads, E2E.ExecFrame.RegPair.reads, E2E.ExecFrame.RegPair.mk,
        E2E.ExecFrame.RegPair.addr, E2E.ExecFrame.RegPair.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr]
    | v m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | _ => exact hb.elim
  | v n =>
    cases b with
    | x m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | v m =>
      obtain ⟨rfl, hn⟩ := ha
      have hm := hb.2
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Insn.armFields.fpOpc,
        ScalarSize.bytes, Reg.encV, show n ≤ 31 by omega, show m ≤ 31 by omega, sField] at h
      subst h
      simp (config := {decide := true}) [E2E.ExecBytes.MemReads, E2E.ExecFrame.RegPair.reads, E2E.ExecFrame.RegPair.mk,
        E2E.ExecFrame.RegPair.addr, E2E.ExecFrame.RegPair.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr]
    | _ => exact hb.elim
  | _ => exact ha.elim

theorem linesReads_app {env : Env} {A B : List Line} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (hA : LinesReads env A s P)
    (hB : ∀ s1, execLines env A s = some s1 → LinesReads { env with pc := env.pc + 4 * A.length } B s1 P) :
    LinesReads env (A ++ B) s P := by
  intro k x t hk s1 hs1 env' a ha p hp i hi
  rcases Nat.lt_or_ge k A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    rw [List.take_append_of_le_length (by omega)] at hs1
    exact hA k x t hk s1 hs1 env' a ha p hp i hi
  · rw [List.getElem?_append_right hge] at hk
    rw [List.take_append, List.take_of_length_le hge, execLines_append] at hs1
    cases h1 : execLines env A s with
    | none => rw [h1] at hs1; cases hs1
    | some sA =>
      rw [h1] at hs1
      exact hB sA h1 _ x t hk s1 hs1 env' a ha p hp i hi

theorem execLines_steps {env : Env} {ls : List Line} {s s' s1 : Arm.ArmState} (h : StepsOk env ls s s')
    (h1 : execLines env ls s = some s1) : s1 = s' := by
  rw [h.exec] at h1; exact (Option.some.inj h1).symm

/-- The pair pops read `[sp, sp + 16 len)`. -/
theorem popPairs_reads (env : Env) (int : Bool) {P : BitVec 64 → Prop} : ∀ (ps : List (Reg × Reg))
    (s : Arm.ArmState), (∀ p ∈ ps, PushReg int p.1 ∧ PushReg int p.2 ∧ p.1 ≠ p.2) →
    (spOf s).toNat % 16 = 0 →
    (∀ k < 16 * ps.length, P (spOf s + BitVec.ofNat 64 k)) →
    LinesReads env (ps.map (popLine2 int)) s P
  | [], _, _, _, _ => fun k _ _ hk => by simp at hk
  | p :: ps, s, hps, hal, hP => by
    have hp := hps p (by simp)
    obtain ⟨i, hi, f1, -, -, f4, -⟩ := exec_pop2 env hp.1 hp.2.1 hp.2.2 s (checkSP_of hal)
    have hl : (popLine2 int p :: ps.map (popLine2 int)) = [popLine2 int p] ++ ps.map (popLine2 int) := rfl
    simp only [List.map_cons]
    rw [hl]
    refine linesReads_app (linesReads_cons (fun _ _ h => by simp at h) fun env' a ha q hq k hk => ?_)
      fun s1 hs1 => ?_
    · rw [memReads_pop2 hp.1 hp.2.1 ha] at hq
      simp only [List.mem_singleton] at hq; subst hq
      exact hP k (by simp only [List.length_cons] at *; omega)
    · have e : s1 = Arm.exec_inst i s := by
        simp only [popLine2, execLines, hi, f1, ite_true] at hs1; exact (Option.some.inj hs1).symm
      subst e
      refine popPairs_reads _ int ps _ (fun q hq => hps q (List.mem_cons_of_mem _ hq))
        (by rw [f4]; simpa using aligned_add (B := spOf s) hal 1) (fun k hk => ?_)
      rw [f4, show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
      exact hP _ (by simp only [List.length_cons]; omega)

/-- The pops of one register class read `[sp, sp + pushBytes)`. -/
theorem popLines_reads (env : Env) (int : Bool) (rs : List Reg) (s : Arm.ArmState)
    (hrs : ∀ r ∈ rs, PushReg int r) (hnd : rs.Nodup) (hal : (spOf s).toNat % 16 = 0)
    {P : BitVec 64 → Prop} (hP : ∀ k < pushBytes rs.length, P (spOf s + BitVec.ofNat 64 k)) :
    LinesReads env (popLines int rs) s P := by
  have hpb := pushBytes_eq rs
  have hfl := pairsOf_flat rs
  obtain ⟨hmP, hmO⟩ := pairsOf_mem rs
  have hpv : ∀ p ∈ (pairsOf rs).1, PushReg int p.1 ∧ PushReg int p.2 :=
    fun p hp => ⟨hrs _ (hmP p hp).1, hrs _ (hmP p hp).2⟩
  have hndP : ((pairsOf rs).1.flatMap fun p => [p.1, p.2]).Nodup := by
    rw [← hfl] at hnd; exact (List.nodup_append.1 hnd).1
  obtain ⟨s1, h1, h2, -⟩ := popPairs_ok env int _ s (spOf s) hpv hndP hal rfl
  rw [popLines_eq]
  refine linesReads_app (popPairs_reads env int _ s (fun p hp => ⟨(hpv p hp).1, (hpv p hp).2,
    pairsOf_ne rs hnd p hp⟩) hal (fun k hk => hP k (by split at hpb <;> omega))) fun s2 hs2 => ?_
  obtain rfl := execLines_steps h1 hs2
  rcases ho : (pairsOf rs).2 with _ | r0
  · intro k _ _ hk; simp at hk
  · refine linesReads_cons (fun _ _ h => by simp at h) fun env' a ha q hq k hk => ?_
    rw [memReads_pop1 (hrs _ (hmO r0 ho)) ha] at hq
    simp only [List.mem_singleton] at hq; subst hq
    simp only [ho, Option.isSome_some, ite_true] at hpb
    rw [h2, add_ofNat_add]
    exact hP _ (by simp at hk; omega)

/-! ## The saves of a frame -/

theorem RegClass.beq_eq_true' (a b : RegClass) : instBEqRegClass.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem Reg.beq_eq_true' (a b : Reg) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> simp [BEq.beq, instBEqReg.beq, RegClass.beq_eq_true']

/-- `Reg`'s derived `BEq` is lawful (`clobberOff` uses `List.idxOf`). -/
instance : LawfulBEq Reg where
  eq_of_beq h := (Reg.beq_eq_true' _ _).1 h
  rfl := (Reg.beq_eq_true' _ _).2 rfl

theorem getElem?_idxOf' {l : List Reg} {r : Reg} (h : r ∈ l) : l[l.idxOf r]? = some r := by
  have hl := List.idxOf_lt_length_of_mem h
  rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]

/-- The saves of a frame: callee-saved registers, each once (`saveShapeOk`). -/
def SavesOk (saves : List Reg) : Prop := (∀ r ∈ saves, r ∈ calleeSaved) ∧ saves.Nodup

theorem calleeSaved_cases {r : Reg} (h : r ∈ calleeSaved) :
    (∃ n, r = .x n ∧ 19 ≤ n ∧ n < 29) ∨ (∃ n, r = .v n ∧ 8 ≤ n ∧ n < 16) := by
  simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact .inl ⟨19 + i, rfl, by omega, by omega⟩
  · exact .inr ⟨8 + i, rfl, by omega, by omega⟩

theorem SavesOk.int {saves : List Reg} (h : SavesOk saves) : ∀ r ∈ savesInt saves, PushReg true r := by
  intro r hr
  simp only [savesInt, List.mem_filter] at hr
  rcases calleeSaved_cases (h.1 r hr.1) with ⟨n, rfl, -, hn⟩ | ⟨n, rfl, -⟩
  · exact ⟨rfl, hn⟩
  · simp at hr

theorem SavesOk.float {saves : List Reg} (h : SavesOk saves) : ∀ r ∈ savesFloat saves, PushReg false r := by
  intro r hr
  simp only [savesFloat, List.mem_filter] at hr
  rcases calleeSaved_cases (h.1 r hr.1) with ⟨n, rfl, -⟩ | ⟨n, rfl, -, hn⟩
  · simp at hr
  · exact ⟨rfl, by omega⟩

theorem SavesOk.length {saves : List Reg} (h : SavesOk saves) : saves.length ≤ 18 :=
  Nat.le_trans (h.2.length_le_of_subset h.1) (by decide)

theorem SavesOk.intLen {saves : List Reg} (h : SavesOk saves) : (savesInt saves).length ≤ 18 :=
  Nat.le_trans (List.length_filter_le _ _) h.length

theorem SavesOk.floatLen {saves : List Reg} (h : SavesOk saves) : (savesFloat saves).length ≤ 18 :=
  Nat.le_trans (List.length_filter_le _ _) h.length

theorem pushBytes_mod (n : Nat) : pushBytes n % 16 = 0 := by unfold pushBytes; omega

theorem clobberBytes_mod (saves : List Reg) : clobberBytes saves % 16 = 0 := by
  unfold clobberBytes; have := pushBytes_mod (savesInt saves).length
  have := pushBytes_mod (savesFloat saves).length; omega

theorem SavesOk.clobber_le {saves : List Reg} (h : SavesOk saves) : clobberBytes saves ≤ 1000 := by
  have := h.intLen; have := h.floatLen; unfold clobberBytes pushBytes; omega

/-- A saved register is an int or a float save, at its index. -/
theorem saves_mem {saves : List Reg} (hsv : SavesOk saves) {r : Reg} (h : r ∈ saves) :
    (∃ n, r = .x n ∧ (savesInt saves)[(savesInt saves).idxOf r]? = some r ∧
      clobberOff saves r = pushBytes (savesFloat saves).length + 8 * (savesInt saves).idxOf r) ∨
    (∃ n, r = .v n ∧ (savesFloat saves)[(savesFloat saves).idxOf r]? = some r ∧
      clobberOff saves r = 8 * (savesFloat saves).idxOf r) := by
  rcases calleeSaved_cases (hsv.1 r h) with ⟨n, rfl, -⟩ | ⟨n, rfl, -⟩
  · have hm : Reg.x n ∈ savesInt saves := List.mem_filter.2 ⟨h, rfl⟩
    exact .inl ⟨n, rfl, getElem?_idxOf' hm, rfl⟩
  · have hm : Reg.v n ∈ savesFloat saves := List.mem_filter.2 ⟨h, rfl⟩
    exact .inr ⟨n, rfl, getElem?_idxOf' hm, rfl⟩

theorem aligned_sub {x : BitVec 64} (hx : x.toNat % 16 = 0) {n : Nat} (hn : n % 16 = 0) (hn' : n < 2 ^ 64) :
    (x - BitVec.ofNat 64 n).toNat % 16 = 0 := by
  have h16 : (16 : Nat) ∣ 2 ^ 64 := ⟨2 ^ 60, rfl⟩
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn', Nat.mod_mod_of_dvd _ h16]
  have := x.isLt
  omega

/-! ## The stack probes (#581) -/

theorem exec_stur_wzr_sp (env : Env) (s : Arm.ArmState) (halign : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.store .store32 .xzr (.unscaled .sp 0)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w .PC (Arm.r .PC s + 4#64) (Arm.write_mem_bytes 4 (spOf s) 0#32 s) := by
  have halign' := spAligned halign
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp (config := {decide := true}) [csimp_rules, StoreOp.fields, Arm.LDST.exec_reg_unscaled_imm,
    Arm.LDST.exec_reg_unscaled_imm_gpr,
    Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
    Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
    Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, halign', spOf]

/-- `n` zero bytes written at `a`: the byte at `b` is zero when `b` is among them. -/
theorem write_bytes_zero_at : ∀ (n : Nat) (a : BitVec 64) (m : Arm.Memory) (b : BitVec 64),
    Arm.Memory.write_bytes n a 0#(n * 8) m b = if (b - a).toNat < n then 0#8 else m b
  | 0, a, m, b => by simp [Arm.Memory.write_bytes]
  | n + 1, a, m, b => by
    rw [Arm.Memory.write_bytes_succ]
    simp only
    have hz : BitVec.setWidth (n * 8) ((0#((n + 1) * 8)) >>> 8) = 0#(n * 8) := by simp
    have hb : BitVec.extractLsb' 0 8 (0#((n + 1) * 8)) = 0#8 := by simp
    rw [hz, hb, write_bytes_zero_at n (a + 1#64)]
    by_cases hba : b = a
    · subst hba
      simp [Arm.Memory.write, Arm.write_store]
    · have hne : (b - a).toNat ≠ 0 := fun h => hba (by
        have := BitVec.eq_of_toNat_eq (x := b - a) (y := 0#64) (by simpa using h); bv_omega)
      have e : (b - a).toNat = (b - (a + 1#64)).toNat + 1 := by
        have : b - (a + 1#64) = (b - a) - 1#64 := by bv_omega
        rw [this, BitVec.toNat_sub_of_le (x := b - a) (y := 1#64)
          (by rw [BitVec.le_def]; exact Nat.one_le_iff_ne_zero.mpr hne),
          show (1#64).toNat = 1 from rfl]
        omega
      simp only [Arm.Memory.write, Arm.write_store, hba, ite_false, e]
      by_cases hl : (b - (a + 1#64)).toNat < n <;> simp [hl]

/-- The first of `k + 1` probes below `base` is at `base - 4096`, the others are `k` probes below
`base - 4096`. -/
theorem probeHitB_succ (k : Nat) (base a : BitVec 64) :
    probeHitB (k + 1) base a =
      (decide ((a - (base - 4096#64)).toNat < 4) || probeHitB k (base - 4096#64) a) := by
  have hr : ∀ i, base - 4096#64 - BitVec.ofNat 64 (4096 * (i + 1)) =
      base - BitVec.ofNat 64 (4096 * (i + 1 + 1)) := fun i => by
    rw [show 4096 * (i + 1 + 1) = 4096 + 4096 * (i + 1) by omega, BitVec.ofNat_add]; bv_omega
  simp only [probeHitB, hr, List.range_succ_eq_map, List.any_cons, List.any_map,
    Function.comp_def]

/-- The steps of `k` unrolled probes: `sp` lowered by `4096·k`, the 4 bytes at
`sp - 4096·(i + 1)` zeroed for `i < k`, nothing else but the pc changed. -/
theorem probeSteps_ok : ∀ (k : Nat) (env : Env) (s : Arm.ArmState), (spOf s).toNat % 16 = 0 →
    ∃ s', StepsOk env (probeSteps k) s s' ∧ spOf s' = spOf s - BitVec.ofNat 64 (4096 * k) ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f s' = Arm.r f s) ∧
      (∀ a, s'.mem a = if probeHitB k (spOf s) a then 0#8 else s.mem a)
  | 0, env, s, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun a => by simp [probeHitB]⟩
  | k + 1, env, s, hal => by
    obtain ⟨a1, ha1, he1⟩ := exec_sub_sp_imm env ⟨1, true⟩ (by decide) s
    generalize hs1 : Arm.exec_inst a1 s = s1 at he1
    have hsp1 : spOf s1 = spOf s - 4096#64 := by
      rw [he1]; simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different, Imm12.value]
    have hal1 : (spOf s1).toNat % 16 = 0 := by
      rw [hsp1]; exact aligned_sub hal (n := 4096) (by decide) (by decide)
    obtain ⟨a2, ha2, he2⟩ := exec_stur_wzr_sp { env with pc := env.pc + 4 } s1 (checkSP_of hal1)
    generalize hs2 : Arm.exec_inst a2 s1 = s2 at he2
    have hsp2 : spOf s2 = spOf s - 4096#64 := by
      rw [he2]; simp only [spOf] at hsp1 ⊢
      simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes, hsp1]
    have hal2 : (spOf s2).toNat % 16 = 0 := by rw [hsp2, ← hsp1]; exact hal1
    obtain ⟨s3, h3, hsp3, ho3, hm3⟩ := probeSteps_ok k { env with pc := env.pc + 4 + 4 } s2 hal2
    refine ⟨s3, ?_, ?_, fun f h1 h2 => ?_, fun a => ?_⟩
    · show StepsOk env (.ins _ none :: .ins _ none :: probeSteps k) s s3
      refine steps_cons ha1 (by rw [hs1, he1]; simp [Arm.r_of_w_same, Arm.r_of_w_different])
        (by rw [hs1, he1]; simp [Arm.r_of_w_different]) (by rw [hs1, he1]; simp [Arm.w_program]) ?_
      rw [hs1]
      refine steps_cons ha2 (by rw [hs2, he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different, Arm.r_of_write_mem_bytes])
        (by rw [hs2, he2]; simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes])
        (by rw [hs2, he2]; simp [Arm.w_program, Arm.write_mem_bytes_program]) ?_
      rw [hs2]; exact h3
    · rw [hsp3, hsp2]
      rw [show 4096 * (k + 1) = 4096 + 4096 * k by omega, BitVec.ofNat_add]
      bv_omega
    · rw [ho3 f h1 h2, he2, Arm.r_of_w_different h1, Arm.r_of_write_mem_bytes, he1,
        Arm.r_of_w_different h2, Arm.r_of_w_different h1]
    · rw [hm3 a, hsp2, he2]
      have hmem2 : (Arm.w .PC (Arm.r .PC s1 + 4#64) (Arm.write_mem_bytes 4 (spOf s1) 0#32 s1)).mem a =
          if (a - (spOf s - 4096#64)).toNat < 4 then 0#8 else s.mem a := by
        rw [Arm.ArmState.mem_w_eq_mem, Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
        simp only
        rw [show (0#32 : BitVec 32) = 0#(4 * 8) from rfl, write_bytes_zero_at, hsp1, he1]
        simp [Arm.ArmState.mem_w_eq_mem]
      rw [hmem2, probeHitB_succ]
      cases hk : probeHitB k (spOf s - 4096#64) a <;>
        by_cases h0 : (a - (spOf s - 4096#64)).toNat < 4 <;>
        simp only [h0, hk, decide_true, decide_false, Bool.false_or, Bool.true_or, Bool.or_true,
          Bool.or_false, Bool.false_eq_true, ite_true, ite_false]

/-- The unrolled `probeLines total` (`probeCount total ≤ 3`) runs: `sp` unchanged, the probed
bytes zeroed (`probeHitB`), nothing else but the pc changed. -/
theorem probeLines_ok (env : Env) (total : Nat) (h3 : probeCount total ≤ 3) (s : Arm.ArmState)
    (hal : (spOf s).toNat % 16 = 0) :
    ∃ s', StepsOk env (probeLines total) s s' ∧ spOf s' = spOf s ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f s' = Arm.r f s) ∧
      (∀ a, s'.mem a = if probeHitB (probeCount total) (spOf s) a then 0#8 else s.mem a) := by
  unfold probeLines
  simp only
  by_cases h0 : probeCount total = 0
  · simp only [h0, beq_self_eq_true, ite_true]
    exact ⟨s, rfl, rfl, fun _ _ _ => rfl, fun a => by simp [probeHitB]⟩
  simp only [show (probeCount total == 0) = false by simpa using h0, Bool.false_eq_true, ite_false,
    h3, ite_true]
  have hn : probeCount total ≤ 3 := h3
  obtain ⟨s1, h1, hsp1, ho1, hm1⟩ := probeSteps_ok (probeCount total) env s hal
  obtain ⟨a2, ha2, he2⟩ := exec_add_sp_imm
    { env with pc := env.pc + 4 * (probeSteps (probeCount total)).length } ⟨probeCount total, true⟩
    (by show probeCount total < 4096; omega) s1
  refine ⟨_, StepsOk.append h1 (steps_one ha2 ?_ ?_ ?_), ?_, fun f g1 g2 => ?_, fun a => ?_⟩
  · simp [he2, Arm.r_of_w_same, Arm.r_of_w_different]
  · simp [he2, Arm.r_of_w_different]
  · simp [he2, Arm.w_program]
  · rw [he2]; simp only [spOf] at hsp1 ⊢
    simp only [Arm.r_of_w_same, Arm.r_of_w_different (show Arm.StateField.GPR 31#5 ≠ .PC by simp), hsp1,
      Imm12.value, ite_true]
    rw [show probeCount total * 4096 = 4096 * probeCount total from Nat.mul_comm _ _]
    exact BitVec.sub_add_cancel _ _
  · rw [he2, Arm.r_of_w_different g2, Arm.r_of_w_different g1, ho1 f g1 g2]
  · rw [he2, Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem, hm1 a]

/-! ### The stack-probe loop (#581: probed stacks of 16 KiB and more) -/

theorem exec_sub_x16_4096 (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.aluImm12 .sub true (.x 16) (.x 16) ⟨1, true⟩).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 16#5) (xreg 16 s - 4096#64) (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  have hi := imm12_bv (i := ⟨1, true⟩) (by decide)
  simp only [Imm12.value, ite_true] at hi
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_sub_neg, hi, xreg]

theorem exec_str_wzr_sp_x16 (env : Env) (s : Arm.ArmState) (halign : Arm.CheckSPAlignment s) :
    ∃ a, (Insn.store .store32 .xzr (.regReg .sp (.x 16))).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w .PC (Arm.r .PC s + 4#64) (Arm.write_mem_bytes 4 (spOf s + xreg 16 s) 0#32 s) := by
  have halign' := spAligned halign
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp (config := {decide := true}) [csimp_rules, StoreOp.fields, Arm.LDST.exec_reg_reg_offset,
    Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
    Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
    Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, halign', spOf, xreg,
    extend_uxtx0]

theorem exec_cmn_x16_x17 (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.aluRRR .addS true .xzr (.x 16) (.x 17)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.write_pstate (Arm.AddWithCarry (xreg 16 s) (xreg 17 s) 0#1).2
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, xreg]

theorem exec_bgt_back (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.bcondRel .gt (-12)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w .PC (if Arm.ConditionHolds Cond.gt.bits s then Arm.r .PC s - 12#64
        else Arm.r .PC s + 4#64) s := by
  refine ⟨_, by simp [Insn.toArmInst, Insn.armFields, Functor.map, Except.map, pure, Except.pure]; rfl, ?_⟩
  simp [Arm.ArmInst.norm, Arm.exec_inst, Arm.BR.exec_cond_branch_imm, Arm.write_pc, Arm.read_pc,
    Arm.BR.Cond_branch_imm_inst.branch_taken_pc, Backend.signExtend_append_zero, Cond.bits]
  split <;> simp_all
  bv_omega

/-- `x16` after `m` iterations of the probe loop: `-4096·m`. -/
abbrev loopOff (m : Nat) : BitVec 64 := 0#64 - BitVec.ofNat 64 (4096 * m)

/-- The flags of the loop's `cmn x16, x17` in iteration `m ≥ 1` (`x16 = -4096·m`,
`x17 = total`): the sum `total - 4096·m` does not overflow. -/
theorem cmn_flags {m total : Nat} (hm : 0 < m) (hm' : 4096 * m < 2 ^ 33) (ht : total < 2 ^ 32) :
    (Arm.AddWithCarry (loopOff m) (BitVec.ofNat 64 total) 0#1).2 =
      if 4096 * m ≤ total then Arm.make_pstate 0#1 (if 4096 * m = total then 1#1 else 0#1) 1#1 0#1
      else Arm.make_pstate 1#1 0#1 0#1 0#1 := by
  have hr := Arm.fst_AddWithCarry_eq_add (loopOff m) (BitVec.ofNat 64 total)
  simp only [Arm.AddWithCarry, Arm.make_pstate] at hr ⊢
  rw [hr]
  split
  · rename_i hle
    simp only [Arm.PState.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [Arm.BitVec.lsb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      bv_omega
    · split <;> split <;> bv_omega
    · split <;> bv_omega
    · rw [if_pos]
      rw [← BitVec.toInt_inj, BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_add,
        BitVec.toInt_add, BitVec.toInt_signExtend_of_le (by decide),
        BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_add]
      simp only [BitVec.toInt_eq_toNat_cond, Int.bmod_def, BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp only [Nat.reduceSub, Nat.reducePow, Nat.reduceAdd] at *
      repeat' split
      all_goals omega
  · rename_i hlt
    simp only [Arm.PState.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [Arm.BitVec.lsb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      bv_omega
    · split <;> bv_omega
    · split <;> bv_omega
    · rw [if_pos]
      rw [← BitVec.toInt_inj, BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_add,
        BitVec.toInt_add, BitVec.toInt_signExtend_of_le (by decide),
        BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_add]
      simp only [BitVec.toInt_eq_toNat_cond, Int.bmod_def, BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp only [Nat.reduceSub, Nat.reducePow, Nat.reduceAdd] at *
      repeat' split
      all_goals omega

/-- The branch of the loop's last instruction: `b.gt` holds after the `cmn` of iteration `m ≥ 1`
iff `4096·m < total`. -/
theorem cmn_gt {m total : Nat} (hm : 0 < m) (hm' : 4096 * m < 2 ^ 33) (ht : total < 2 ^ 32)
    (w : Arm.ArmState) :
    Arm.ConditionHolds Cond.gt.bits (Arm.write_pstate (Arm.AddWithCarry (loopOff m) (BitVec.ofNat 64 total) 0#1).2 w) =
      decide (4096 * m < total) := by
  rw [conditionHolds_write_pstate, cmn_flags hm hm' ht]
  split <;> split <;> simp [condOn, Cond.bits, Arm.make_pstate] <;> omega

/-- The flags after the last iteration (`4096·m ≥ total > 4096·(m - 1)`) are `loopFlag total`. -/
theorem cmn_last {m total : Nat} (hm : 0 < m) (hm' : 4096 * m < 2 ^ 33) (ht : total < 2 ^ 32)
    (hge : total ≤ 4096 * m) (hlt : 4096 * (m - 1) < total) (w : Arm.ArmState) (fl : Arm.PFlag) :
    Arm.r (.FLAG fl) (Arm.write_pstate (Arm.AddWithCarry (loopOff m) (BitVec.ofNat 64 total) 0#1).2 w) =
      loopFlag total fl := by
  rw [cmn_flags hm hm' ht]
  have hmod : (total % 4096 = 0) ↔ 4096 * m = total := by omega
  cases fl <;> by_cases h : total % 4096 = 0 <;>
    simp [Arm.write_pstate, Arm.make_pstate, loopFlag, Arm.r_of_w_same, Arm.r_of_w_different, h] <;>
    split <;> simp_all <;> omega

/-- The first three lines of the loop body (`sub`, `str`, `cmn`); then the `b.gt`. -/
theorem probeLoopBody_eq :
    probeLoopBody = probeLoopBody.take 3 ++ [.ins (.bcondRel .gt (-12))] := rfl

/-- **`r` iterations of the stack-probe loop** (`probeLoopBody`, placed at `env.pc`) from `s`,
the `m`-th one first: each starts with `sp = S` and `x16 = -4096·m` (`loopOff`), runs the `sub`,
`str` and `cmn` straight-line, then the `b.gt`, which jumps back to the `sub` while iterations
remain and falls through after the last. -/
def LoopRuns (env : Env) (S : BitVec 64) : Nat → Nat → Arm.ArmState → Arm.ArmState → Prop
  | _, 0, s, s' => s' = s
  | m, r + 1, s, s' => spOf s = S ∧ xreg 16 s = loopOff m ∧ ∃ s3 ab,
      StepsOk env (probeLoopBody.take 3) s s3 ∧
      (Insn.bcondRel .gt (-12)).toArmInst { env with pc := env.pc + 12 } = .ok ab ∧
      Arm.r .ERR (Arm.exec_inst ab s3) = Arm.r .ERR s3 ∧ (Arm.exec_inst ab s3).program = s3.program ∧
      Arm.r .PC (Arm.exec_inst ab s3) = (if r = 0 then Arm.r .PC s + 16#64 else Arm.r .PC s) ∧
      LoopRuns env S (m + 1) r (Arm.exec_inst ab s3) s'

theorem LoopRuns.err : ∀ {env : Env} {S : BitVec 64} {m r : Nat} {s s' : Arm.ArmState},
    LoopRuns env S m r s s' → Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program
  | _, _, _, 0, _, _, h => by simp only [LoopRuns] at h; subst h; exact ⟨rfl, rfl⟩
  | _, _, _, _ + 1, _, _, h => by
    obtain ⟨-, -, s3, ab, h3, -, he, hp, -, h⟩ := h
    obtain ⟨e1, p1⟩ := LoopRuns.err h
    obtain ⟨e3, p3⟩ := h3.err
    exact ⟨e1.trans (he.trans e3), p1.trans (hp.trans p3)⟩

/-- A straight-line run is determined by its start (`execLines`). -/
theorem StepsOk.det {env : Env} {ls : List Line} {s s1 s2 : Arm.ArmState}
    (h1 : StepsOk env ls s s1) (h2 : StepsOk env ls s s2) : s1 = s2 :=
  Option.some.inj (h1.exec.symm.trans h2.exec)

/-- The loop's run is determined by its start. -/
theorem LoopRuns.det : ∀ {env : Env} {S : BitVec 64} {m r : Nat} {s s1 s2 : Arm.ArmState},
    LoopRuns env S m r s s1 → LoopRuns env S m r s s2 → s1 = s2
  | _, _, _, 0, _, _, _, h1, h2 => by simp only [LoopRuns] at h1 h2; rw [h1, h2]
  | _, _, _, _ + 1, _, _, _, h1, h2 => by
    obtain ⟨-, -, t1, b1, h31, hb1, -, -, -, h1⟩ := h1
    obtain ⟨-, -, t2, b2, h32, hb2, -, -, -, h2⟩ := h2
    obtain rfl := StepsOk.det h31 h32
    rw [hb1, Except.ok.injEq] at hb2
    subst hb2
    exact LoopRuns.det h1 h2

/-- **The stack-probe loop runs** (`probeLoopBody`) from iteration `m` with `r ≥ 1` iterations
left (`m + r = ⌈total / 4096⌉`, `x16 = -4096·m`, `x17 = total`, an aligned `sp`): `x16` ends at
`-4096·(m + r)`, the flags at `loopFlag total`, the 4 bytes at `sp - 4096·i` zeroed for
`m < i ≤ m + r`; the pc ends after the loop; nothing else changes. -/
theorem probeLoop_ok (env : Env) {total : Nat} (hlo : 16384 ≤ total) (hhi : total < 2 ^ 32) :
    ∀ (r m : Nat) (s : Arm.ArmState), m + r = (total + 4095) / 4096 → 0 < r →
      (spOf s).toNat % 16 = 0 → xreg 16 s = loopOff m → xreg 17 s = BitVec.ofNat 64 total →
      ∃ s', LoopRuns env (spOf s) m r s s' ∧ spOf s' = spOf s ∧ xreg 16 s' = loopOff (m + r) ∧
        xreg 17 s' = BitVec.ofNat 64 total ∧ (∀ fl, Arm.r (.FLAG fl) s' = loopFlag total fl) ∧
        Arm.r .PC s' = Arm.r .PC s + 16#64 ∧
        (∀ f, f ≠ .PC → f ≠ .GPR 16#5 → (∀ fl, f ≠ .FLAG fl) → Arm.r f s' = Arm.r f s) ∧
        (∀ a, s'.mem a = if probeHitB r (spOf s - BitVec.ofNat 64 (4096 * m)) a then 0#8 else s.mem a)
  | 0, _, _, _, h0, _, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | r + 1, m, s, hmr, _, hal, h16, h17 => by
    have hn : (total + 4095) / 4096 ≤ 2 ^ 20 := by omega
    -- `sub x16, x16, #4096`
    obtain ⟨a1, ha1, he1⟩ := exec_sub_x16_4096 env s
    generalize hs1 : Arm.exec_inst a1 s = s1 at he1
    have hsp1 : spOf s1 = spOf s := by rw [he1]; simp [spOf, Arm.r_of_w_different]
    have hx1 : xreg 16 s1 = loopOff (m + 1) := by
      rw [he1]; simp only [xreg, Arm.r_of_w_same]
      simp only [xreg] at h16; rw [h16]
      rw [show 4096 * (m + 1) = 4096 * m + 4096 by omega, BitVec.ofNat_add]; bv_omega
    -- `str wzr, [sp, x16]`
    obtain ⟨a2, ha2, he2⟩ := exec_str_wzr_sp_x16 { env with pc := env.pc + 4 } s1
      (checkSP_of (by rw [hsp1]; exact hal))
    generalize hs2 : Arm.exec_inst a2 s1 = s2 at he2
    -- `cmn x16, x17`
    obtain ⟨a3, ha3, he3⟩ := exec_cmn_x16_x17 { env with pc := env.pc + 4 + 4 } s2
    generalize hs3 : Arm.exec_inst a3 s2 = s3 at he3
    have hx2 : xreg 16 s2 = loopOff (m + 1) := by
      rw [he2]; simp only [xreg] at hx1 ⊢; simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes, hx1]
    have hx17 : xreg 17 s2 = BitVec.ofNat 64 total := by
      rw [he2, he1]; simp only [xreg] at h17 ⊢
      simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes, h17]
    rw [hx2, hx17] at he3
    have hm1 : 4096 * (m + 1) < 2 ^ 33 := by omega
    -- `b.gt` back to the `sub`
    obtain ⟨a4, ha4, he4⟩ := exec_bgt_back { env with pc := env.pc + 12 } s3
    have hgt : Arm.ConditionHolds Cond.gt.bits s3 = decide (0 < r) := by
      rw [he3, cmn_gt (by omega) hm1 hhi]
      simp only [decide_eq_decide]; omega
    have hpc3 : Arm.r .PC s3 = Arm.r .PC s + 12#64 := by
      rw [he3, he2, he1]
      simp [Arm.write_pstate, Arm.r_of_w_same, Arm.r_of_w_different, Arm.r_of_write_mem_bytes]
      bv_omega
    have hsp3 : spOf s3 = spOf s := by
      rw [he3, he2]; simp only [spOf] at hsp1 ⊢
      simp [Arm.write_pstate, Arm.r_of_w_different, Arm.r_of_write_mem_bytes, hsp1]
    have hmem3 : ∀ a, s3.mem a = if (a - (spOf s - BitVec.ofNat 64 (4096 * (m + 1)))).toNat < 4
        then 0#8 else s.mem a := by
      intro a
      rw [he3]
      simp only [Arm.write_pstate, Arm.ArmState.mem_w_eq_mem]
      rw [he2, Arm.ArmState.mem_w_eq_mem, Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
      simp only
      rw [show (0#32 : BitVec 32) = 0#(4 * 8) from rfl, write_bytes_zero_at, hsp1, hx1, he1]
      simp only [Arm.ArmState.mem_w_eq_mem]
      congr 3
      rw [show 4096 * (m + 1) = 4096 * m + 4096 by omega]
      bv_omega
    have hf3 : ∀ f, f ≠ .PC → f ≠ .GPR 16#5 → (∀ fl, f ≠ .FLAG fl) → Arm.r f s3 = Arm.r f s := by
      intro f g1 g2 g3
      rw [he3, he2, he1]
      simp only [Arm.write_pstate]
      rw [Arm.r_of_w_different (g3 _), Arm.r_of_w_different (g3 _), Arm.r_of_w_different (g3 _),
        Arm.r_of_w_different (g3 _), Arm.r_of_w_different g1, Arm.r_of_w_different g1,
        Arm.r_of_write_mem_bytes, Arm.r_of_w_different g2, Arm.r_of_w_different g1]
    have hsteps : StepsOk env (probeLoopBody.take 3) s s3 := by
      show StepsOk env [.ins _ none, .ins _ none, .ins _ none] s s3
      refine steps_cons ha1 (by rw [hs1, he1]; simp [Arm.r_of_w_same, Arm.r_of_w_different])
        (by rw [hs1, he1]; simp [Arm.r_of_w_different]) (by rw [hs1, he1]; simp [Arm.w_program]) ?_
      rw [hs1]
      refine steps_cons ha2 (by rw [hs2, he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different, Arm.r_of_write_mem_bytes])
        (by rw [hs2, he2]; simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes])
        (by rw [hs2, he2]; simp [Arm.w_program, Arm.write_mem_bytes_program]) ?_
      rw [hs2]
      refine steps_one ha3 (by rw [hs3, he3]; simp [Arm.write_pstate, Arm.r_of_w_same, Arm.r_of_w_different])
        (by rw [hs3, he3]; simp [Arm.write_pstate, Arm.r_of_w_different])
        (by rw [hs3, he3]; simp [Arm.write_pstate, Arm.w_program])
    generalize hs4 : Arm.exec_inst a4 s3 = s4 at he4
    have he4' : Arm.r .ERR (Arm.exec_inst a4 s3) = Arm.r .ERR s3 ∧
        (Arm.exec_inst a4 s3).program = s3.program := by
      rw [hs4, he4]; simp [Arm.r_of_w_different, Arm.w_program]
    have hf4 : ∀ f, f ≠ .PC → Arm.r f s4 = Arm.r f s3 := fun f g => by rw [he4, Arm.r_of_w_different g]
    have hm4 : s4.mem = s3.mem := by rw [he4, Arm.ArmState.mem_w_eq_mem]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · -- the last iteration: the `b.gt` falls through
      have hpc4 : Arm.r .PC s4 = Arm.r .PC s + 16#64 := by
        rw [he4, hgt]; simp [Arm.r_of_w_same, hpc3]; bv_omega
      refine ⟨s4, ⟨rfl, h16, s3, a4, hsteps, ha4, he4'.1, he4'.2, by rw [hs4, hpc4, if_pos rfl], hs4.symm⟩,
        ?_, ?_, ?_, ?_, hpc4,
        fun f g1 g2 g3 => by rw [hf4 f g1, hf3 f g1 g2 g3], fun a => ?_⟩
      · rw [show spOf s4 = spOf s3 from hf4 _ (by simp), hsp3]
      · show Arm.r _ s4 = _; rw [hf4 _ (by simp), he3]
        simp [Arm.write_pstate, Arm.r_of_w_different, Arm.r_of_w_same, hx2]
      · show Arm.r _ s4 = _; rw [hf4 _ (by simp), he3]
        simp [Arm.write_pstate, Arm.r_of_w_different, Arm.r_of_w_same]
        simpa [xreg] using hx17
      · intro fl
        rw [hf4 _ (by simp), he3]
        exact cmn_last (by omega) hm1 hhi (by omega) (by omega) _ fl
      · rw [hm4, hmem3 a]
        simp only [probeHitB, List.range_one, List.any_cons, List.any_nil, Bool.or_false]
        rw [show spOf s - BitVec.ofNat 64 (4096 * m) - BitVec.ofNat 64 (4096 * (0 + 1)) =
          spOf s - BitVec.ofNat 64 (4096 * (m + 1)) by
            rw [show 4096 * (m + 1) = 4096 * m + 4096 by omega, BitVec.ofNat_add]; bv_omega]
        by_cases h : (a - (spOf s - BitVec.ofNat 64 (4096 * (m + 1)))).toNat < 4 <;> simp [h]
    · -- more iterations: the `b.gt` jumps back to the `sub`
      have hpc4 : Arm.r .PC s4 = Arm.r .PC s := by
        rw [he4, hgt]; simp [Arm.r_of_w_same, hpc3, hr]
      have hal4 : (spOf s4).toNat % 16 = 0 := by
        rw [show spOf s4 = spOf s3 from hf4 _ (by simp), hsp3]; exact hal
      have h16' : xreg 16 s4 = loopOff (m + 1) := by
        show Arm.r _ s4 = _; rw [hf4 _ (by simp), he3]
        simp [Arm.write_pstate, Arm.r_of_w_different, Arm.r_of_w_same, hx2]
      have h17' : xreg 17 s4 = BitVec.ofNat 64 total := by
        show Arm.r _ s4 = _; rw [hf4 _ (by simp), he3]
        simp [Arm.write_pstate, Arm.r_of_w_different, Arm.r_of_w_same]
        simpa [xreg] using hx17
      have hsp4 : spOf s4 = spOf s := by rw [show spOf s4 = spOf s3 from hf4 _ (by simp), hsp3]
      obtain ⟨s', hL, hsp', hx16', hx17', hfl', hpc', hf', hm'⟩ :=
        probeLoop_ok env hlo hhi r (m + 1) s4 (by omega) hr hal4 h16' h17'
      rw [hsp4] at hL
      refine ⟨s', ⟨rfl, h16, s3, a4, hsteps, ha4, he4'.1, he4'.2, by rw [hs4, hpc4]; simp [Nat.pos_iff_ne_zero.mp hr], by
        rw [hs4]; exact hL⟩, ?_, by rw [hx16']; congr 2; omega, hx17', hfl', ?_, ?_, fun a => ?_⟩
      · rw [hsp', show spOf s4 = spOf s3 from hf4 _ (by simp), hsp3]
      · rw [hpc', hpc4]
      · intro f g1 g2 g3; rw [hf' f g1 g2 g3, hf4 f g1, hf3 f g1 g2 g3]
      · rw [hm' a, show spOf s4 = spOf s3 from hf4 _ (by simp), hsp3, hm4, hmem3 a, probeHitB_succ]
        rw [show spOf s - BitVec.ofNat 64 (4096 * m) - 4096#64 = spOf s - BitVec.ofNat 64 (4096 * (m + 1)) by
          rw [show 4096 * (m + 1) = 4096 * m + 4096 by omega, BitVec.ofNat_add]; bv_omega]
        cases hk : probeHitB r (spOf s - BitVec.ofNat 64 (4096 * (m + 1))) a <;>
          by_cases h0 : (a - (spOf s - BitVec.ofNat 64 (4096 * (m + 1)))).toNat < 4 <;>
          simp [h0, hk]

/-- The probes zero nothing in `[base - c, base + 16)` for `c ≤ 4000` (the clobber area and the
fp/lr slot above it): every probe is at least 4096 bytes below `base`. -/
theorem probeHitB_top {n c k : Nat} {base : BitVec 64} (hc : c ≤ 4000) (hk : k < c + 16)
    (hn : 4096 * n < 2 ^ 63) :
    probeHitB n base (base - BitVec.ofNat 64 c + BitVec.ofNat 64 k) = false := by
  simp only [probeHitB, List.any_eq_false, List.mem_range, decide_eq_true_eq]
  intro i hi
  have hi' : 4096 * (i + 1) ≤ 4096 * n := Nat.mul_le_mul_left 4096 hi
  have e : (base - BitVec.ofNat 64 c + BitVec.ofNat 64 k - (base - BitVec.ofNat 64 (4096 * (i + 1)))).toNat =
      4096 * (i + 1) + k - c := by
    have h1 : (4096 * (i + 1)) % 2 ^ 64 = 4096 * (i + 1) := Nat.mod_eq_of_lt (by omega)
    have h2 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
    have h3 : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
    bv_omega
  rw [e]; omega

theorem probeHitB_sub16 (n : Nat) (sp a : BitVec 64) :
    probeHitB n (sp - 16#64) a = probeHitN n sp a := rfl

theorem StepsOk.pc : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState}, StepsOk env ls s s' →
    Arm.r .PC s' = Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length)
  | _, [], _, _, h => by simp only [StepsOk] at h; subst h; simp
  | _, .ins i t :: ls, s, s', h => by
    obtain ⟨ai, -, hpc, -, -, h⟩ := h
    rw [StepsOk.pc h, hpc, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_cons]
    omega
  | _, .label _ :: _, _, _, h => h.elim
  | _, .word _ _ :: _, _, _, h => h.elim

/-! ### The stack probes as a phase of the prologue -/

/-- The probe lines that run straight-line: the unrolled probes, or the loop's constants
`x16 = 0`, `x17 = total`. -/
def probeHead (total : Nat) : List Line :=
  if probeLoop total then loadConst64 (.x 16) 0 ++ loadConst64 (.x 17) total else probeLines total

/-- The stack-probe loop's body when the probes are the loop (`probeLoopBody`), else nothing. -/
def probeLoopL (total : Nat) : List Line := if probeLoop total then probeLoopBody else []

/-- The iterations of the stack-probe loop (`probeCount`; none without the loop). -/
def loopIters (total : Nat) : Nat := if probeLoop total then probeCount total else 0

theorem probeLines_split (total : Nat) : probeLines total = probeHead total ++ probeLoopL total := by
  unfold probeLines probeHead probeLoopL probeLoop
  by_cases h : 3 < probeCount total
  · have h0 : (probeCount total == 0) = false := by simp; omega
    simp [h, h0, show ¬ probeCount total ≤ 3 by omega, probeLoopLines]
  · simp [h]

/-- The probe loop is the loop form: a probed stack in `[16 KiB, 4 GiB)`, `⌈total / 4096⌉` probes. -/
theorem probeLoop_facts {total : Nat} (hl : probeLoop total = true) :
    16384 ≤ total ∧ total < 2 ^ 32 ∧ probeCount total = (total + 4095) / 4096 := by
  have hc : 3 < probeCount total := by simpa [probeLoop] using hl
  unfold probeCount at hc ⊢
  split at hc
  · omega
  · rename_i h1
    split at hc
    · rename_i h2
      rw [if_neg h1, if_pos h2]
      exact ⟨by omega, h2, rfl⟩
    · omega

/-- **The stack probes' run** from `s`: the straight-line part (`probeHead`, which keeps `sp`),
then the loop's iterations (`LoopRuns` from iteration 0 at `sp = spOf s`, none without the
loop); `sp` ends as it started. -/
def ProbeRun (env : Env) (total : Nat) (s s' : Arm.ArmState) : Prop :=
  ∃ s1, StepsOk env (probeHead total) s s1 ∧ spOf s1 = spOf s ∧
    LoopRuns { env with pc := env.pc + 4 * (probeHead total).length } (spOf s) 0 (loopIters total) s1 s' ∧
    spOf s' = spOf s

theorem ProbeRun.err {env : Env} {total : Nat} {s s' : Arm.ArmState} (h : ProbeRun env total s s') :
    Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program := by
  obtain ⟨s1, h1, -, h2, -⟩ := h
  obtain ⟨e1, p1⟩ := h1.err
  obtain ⟨e2, p2⟩ := h2.err
  exact ⟨e2.trans e1, p2.trans p1⟩

theorem ProbeRun.det {env : Env} {total : Nat} {s s1 s2 : Arm.ArmState}
    (h1 : ProbeRun env total s s1) (h2 : ProbeRun env total s s2) : s1 = s2 := by
  obtain ⟨t1, hH1, -, hL1, -⟩ := h1
  obtain ⟨t2, hH2, -, hL2, -⟩ := h2
  obtain rfl := StepsOk.det hH1 hH2
  exact LoopRuns.det hL1 hL2

/-- **The stack probes run** (`probeLines`) from an aligned `sp`: `sp` unchanged, the probed bytes
zeroed (`probeHitB`), the flags those of the loop (`probeFlagT`), the pc after the probe lines;
besides, only x16 and x17 change (the loop's registers). -/
theorem probeRun_ok (env : Env) (total : Nat) (s : Arm.ArmState) (hal : (spOf s).toNat % 16 = 0) :
    ∃ s', ProbeRun env total s s' ∧ spOf s' = spOf s ∧
      Arm.r .PC s' = Arm.r .PC s + BitVec.ofNat 64 (4 * (probeLines total).length) ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 → (∀ fl, f ≠ .FLAG fl) →
        Arm.r f s' = Arm.r f s) ∧
      (∀ fl, Arm.r (.FLAG fl) s' = probeFlagT total s fl) ∧
      (∀ a, s'.mem a = if probeHitB (probeCount total) (spOf s) a then 0#8 else s.mem a) := by
  by_cases hl : probeLoop total = true
  · obtain ⟨hlo, hhi, hcnt⟩ := probeLoop_facts hl
    have hH : probeHead total = loadConst64 (.x 16) 0 ++ loadConst64 (.x 17) total := by
      simp [probeHead, hl]
    have hI : loopIters total = probeCount total := by simp [loopIters, hl]
    have hLL : probeLoopL total = probeLoopBody := by simp [probeLoopL, hl]
    -- `x16 = 0`, `x17 = total`
    have h1 := steps_loadConst64 env (n := 16) (by omega) 0 s
    generalize hs1 : pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) 0).length))
      (BitVec.ofNat 64 0) = s1 at h1
    have h2 := steps_loadConst64 { env with pc := env.pc + 4 * (loadConst64 (.x 16) 0).length }
      (n := 17) (by omega) total s1
    generalize hs2 : pcx s1 17 (Arm.r .PC s1 + BitVec.ofNat 64 (4 * (loadConst64 (.x 17) total).length))
      (BitVec.ofNat 64 total) = s2 at h2
    have hf2 : ∀ f, f ≠ .PC → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 → Arm.r f s2 = Arm.r f s := by
      intro f g1 g2 g3
      rw [← hs2, ← hs1]
      simp only [pcx]
      rw [Arm.r_of_w_different g1, Arm.r_of_w_different g3, Arm.r_of_w_different g1,
        Arm.r_of_w_different g2]
    have hm2 : s2.mem = s.mem := by rw [← hs2, ← hs1]; simp [pcx, Arm.ArmState.mem_w_eq_mem]
    have hsp2 : spOf s2 = spOf s := hf2 _ (by simp) (by simp) (by simp)
    have h16 : xreg 16 s2 = loopOff 0 := by
      show Arm.r _ s2 = _
      rw [← hs2, ← hs1]
      simp [pcx, Arm.r_of_w_different, Arm.r_of_w_same]
    have h17 : xreg 17 s2 = BitVec.ofNat 64 total := by
      show Arm.r _ s2 = _
      rw [← hs2]; simp [pcx, Arm.r_of_w_same]
    have hpc2 : Arm.r .PC s2 = Arm.r .PC s +
        BitVec.ofNat 64 (4 * ((loadConst64 (.x 16) 0).length + (loadConst64 (.x 17) total).length)) := by
      rw [← hs2, (pcx_facts _ _ _ _).1, ← hs1, (pcx_facts _ _ _ _).1, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    obtain ⟨s', hL, hsp', -, -, hfl', hpc', hf', hm'⟩ :=
      probeLoop_ok { env with pc := env.pc + 4 * (probeHead total).length } hlo hhi (probeCount total) 0 s2
        (by omega) (by omega) (by rw [hsp2]; exact hal) h16 h17
    rw [hsp2] at hL
    refine ⟨s', ⟨s2, by rw [hH]; exact StepsOk.append h1 h2, hsp2, by rw [hI]; exact hL, by rw [hsp', hsp2]⟩,
      by rw [hsp', hsp2], ?_, fun f g1 g2 g3 g4 g5 => ?_, fun fl => ?_, fun a => ?_⟩
    · rw [hpc', hpc2, probeLines_split, hH, hLL, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append, probeLoopBody,
        List.length_cons, List.length_nil]
      omega
    · rw [hf' f g1 g3 g5, hf2 f g1 g3 g4]
    · rw [hfl']; simp [probeFlagT, hl]
    · rw [hm' a, hsp2, hm2]; simp
  · have hl' : probeLoop total = false := by simpa using hl
    have h3 : probeCount total ≤ 3 := by simpa [probeLoop] using hl'
    have hH : probeHead total = probeLines total := by simp [probeHead, hl']
    have hI : loopIters total = 0 := by simp [loopIters, hl']
    obtain ⟨s', hP, hsp', hf', hm'⟩ := probeLines_ok env total h3 s hal
    refine ⟨s', ⟨s', by rw [hH]; exact hP, hsp', by rw [hI]; exact rfl, hsp'⟩, hsp', hP.pc,
      fun f g1 g2 _ _ _ => hf' f g1 g2,
      fun fl => ?_, hm'⟩
    rw [hf' _ (by simp) (by simp)]; simp [probeFlagT, hl']

/-! ## The prologue and the epilogue -/

theorem prologueLines_eq {calls : Bool} (saves : List Reg) (size : Nat) :
    prologueLines saves size calls = [.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))), .ins (.mov true Reg.fp .sp)] ++
      (probeLines (probeTotal size calls) ++ (pushLines true (savesInt saves) ++ (pushLines false (savesFloat saves) ++
        spAdjLines true (size - clobberBytes saves)))) := by
  simp only [prologueLines, List.append_assoc]

theorem epilogueLines_eq (saves : List Reg) (size : Nat) :
    epilogueLines saves size = (spAdjLines false (size - clobberBytes saves) ++
      (popLines false (savesFloat saves) ++ (popLines true (savesInt saves) ++
        [.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16))]))) ++ [.ins .ret] := by
  simp only [epilogueLines, List.append_assoc, List.cons_append, List.nil_append]

theorem frame_sp_eq (X C D : BitVec 64) :
    X - (BitVec.ofNat 64 16 + C) - D = X - 16#64 - (C + D) := by bv_omega

/-- The frame setup: `stp x29, x30, [sp, #-16]!; mov x29, sp`. -/
def fplrLines : List Line := [.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))), .ins (.mov true Reg.fp .sp)]

/-- The prologue's lines after the stack probes: the pushes and the `sp` adjustment. -/
def prologueTail (saves : List Reg) (size : Nat) : List Line :=
  pushLines true (savesInt saves) ++ (pushLines false (savesFloat saves) ++
    spAdjLines true (size - clobberBytes saves))

theorem prologueLines_split {calls : Bool} (saves : List Reg) (size : Nat) :
    prologueLines saves size calls = fplrLines ++ (probeHead (probeTotal size calls) ++
      (probeLoopL (probeTotal size calls) ++ prologueTail saves size)) := by
  rw [prologueLines_eq, probeLines_split, List.append_assoc]; rfl

/-- **The prologue's run** from `s` to `s'` (its `prologueSteps` instructions): the frame setup
(which lowers `sp` by 16), the stack probes (`ProbeRun`: the probe loop runs its body
`probeCount` times, #581), the pushes and the `sp` adjustment. Without the probe loop it is the
straight-line run of `prologueLines` (`ProRun.stepsOk`). -/
def ProRun (env : Env) (saves : List Reg) (size : Nat) (calls : Bool) (s s' : Arm.ArmState) : Prop :=
  ∃ s2 sP, StepsOk env fplrLines s s2 ∧ spOf s2 = spOf s - 16#64 ∧
    ProbeRun { env with pc := env.pc + 4 + 4 } (probeTotal size calls) s2 sP ∧
    StepsOk { env with pc := env.pc + 4 + 4 + 4 * (probeLines (probeTotal size calls)).length }
      (prologueTail saves size) sP s'

theorem ProRun.err {env : Env} {saves : List Reg} {size : Nat} {calls : Bool} {s s' : Arm.ArmState}
    (h : ProRun env saves size calls s s') : Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program := by
  obtain ⟨s2, sP, h1, -, h2, h3⟩ := h
  obtain ⟨e1, p1⟩ := h1.err
  obtain ⟨e2, p2⟩ := h2.err
  obtain ⟨e3, p3⟩ := h3.err
  exact ⟨e3.trans (e2.trans e1), p3.trans (p2.trans p1)⟩

theorem ProRun.det {env : Env} {saves : List Reg} {size : Nat} {calls : Bool} {s s1 s2 : Arm.ArmState}
    (h1 : ProRun env saves size calls s s1) (h2 : ProRun env saves size calls s s2) : s1 = s2 := by
  obtain ⟨t1, u1, hA1, -, hP1, hT1⟩ := h1
  obtain ⟨t2, u2, hA2, -, hP2, hT2⟩ := h2
  obtain rfl := StepsOk.det hA1 hA2
  obtain rfl := ProbeRun.det hP1 hP2
  exact StepsOk.det hT1 hT2

/-- Without the probe loop the prologue's run is straight-line. -/
theorem ProRun.stepsOk {env : Env} {saves : List Reg} {size : Nat} {calls : Bool} {s s' : Arm.ArmState}
    (hl : probeLoop (probeTotal size calls) = false) (h : ProRun env saves size calls s s') :
    StepsOk env (prologueLines saves size calls) s s' := by
  obtain ⟨s2, sP, h1, -, ⟨s1, hH, -, hL, -⟩, h3⟩ := h
  have hI : loopIters (probeTotal size calls) = 0 := by simp [loopIters, hl]
  rw [hI] at hL
  simp only [LoopRuns] at hL
  subst hL
  have hH' : probeHead (probeTotal size calls) = probeLines (probeTotal size calls) := by
    simp [probeHead, hl]
  rw [hH'] at hH
  rw [prologueLines_eq]
  exact StepsOk.append h1 (StepsOk.append hH h3)

/-- **The prologue runs** (Cranelift's frame setup, stack probes and clobber saves): fp/lr
pushed at `sp - 16`, `x29 = sp - 16`, the probes (`probeLines`) zero 4 bytes at
`sp - 16 - 4096·(i + 1)` for `i < probeCount` (`probeHitN`), the saved registers pushed below
fp/lr, `sp` lowered by `16 + size`; only the pc, `x29`, `sp`, `x16`, `x17` and the flags change
(the flags as the stack-probe loop leaves them, `probeFlagT`), memory only in
`[sp - 16 - clobberBytes, sp)`, where the fp/lr slot holds the entry x30:x29 and each saved
register's slot (`clobberOff`) its low 64 bits, and at the probed bytes, which are zero.
(#581: the former statement, a straight-line run (`StepsOk`) of the prologue's lines changing
only the pc, `x29`, `sp` and `x16`, memory only in `[sp - 16 - clobberBytes, sp)`, became false
with Cranelift's probes: a probe of a frame of at least 4 KiB writes 4096 bytes and more below
fp/lr, and for a probed stack of 16 KiB or more Cranelift's probe loop (`probeLoopBody`) jumps
back, sets `x17` and the flags; the run is `ProRun`, straight-line without the loop
(`ProRun.stepsOk`); `calls` is the new argument of `prologueLines`.) -/
theorem prologue_ok (env : Env) {saves : List Reg} {size : Nat} {calls : Bool} (hs : size < 2 ^ 64)
    (hsv : SavesOk saves) (hcb : clobberBytes saves ≤ size) (s : Arm.ArmState)
    (hal : (spOf s).toNat % 16 = 0) :
    ∃ s', ProRun env saves size calls s s' ∧
      spOf s' = spOf s - 16#64 - BitVec.ofNat 64 size ∧ xreg 29 s' = spOf s - 16#64 ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 →
        (∀ fl, f ≠ .FLAG fl) → Arm.r f s' = Arm.r f s) ∧
      (∀ fl, Arm.r (.FLAG fl) s' = probeFlagT (probeTotal size calls) s fl) ∧
      (∀ a, (∀ k < 16 + clobberBytes saves,
        a ≠ spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) + BitVec.ofNat 64 k) →
        s'.mem a = if probeHitN (probeCount (probeTotal size calls)) (spOf s) a then 0#8 else s.mem a) ∧
      Arm.read_mem_bytes 16 (spOf s - 16#64) s' = xreg 30 s ++ xreg 29 s ∧
      (∀ r ∈ saves, Arm.read_mem_bytes 8 (spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) +
        BitVec.ofNat 64 (clobberOff saves r)) s' = slotVal s r) := by
  have hcbm := clobberBytes_mod saves
  have hcbl := hsv.clobber_le
  have hpIm := pushBytes_mod (savesInt saves).length
  have hpFm := pushBytes_mod (savesFloat saves).length
  have hcbe : clobberBytes saves = pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length := rfl
  have hpIl : pushBytes (savesInt saves).length ≤ 1000 := by omega
  have hpFl : pushBytes (savesFloat saves).length ≤ 1000 := by omega
  generalize hn : probeCount (probeTotal size calls) = n
  have hn63 : 4096 * n < 2 ^ 63 := by have := probeCount_le (probeTotal size calls); omega
  -- the bases
  generalize hBF : spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) = BF
  have hBFa : BF.toNat % 16 = 0 := by rw [← hBF]; exact aligned_sub hal (by omega) (by omega)
  have hBIa : (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)).toNat % 16 = 0 := by
    rw [show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16) by omega]
    exact aligned_add hBFa _
  have hT16 : spOf s - 16#64 = BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
      BitVec.ofNat 64 (pushBytes (savesInt saves).length) := by
    rw [← hBF, hcbe, show 16 + (pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length) =
      16 + pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length by omega,
      BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  have hBF16 : BF = spOf s - 16#64 - BitVec.ofNat 64 (clobberBytes saves) := by
    rw [← hBF, BitVec.ofNat_add]; bv_omega
  -- fp/lr and `mov x29, sp`
  have hal0 : Arm.CheckSPAlignment s := checkSP_of hal
  obtain ⟨a1, ha1, he1⟩ := exec_stp_fplr env s hal0
  obtain ⟨a2, ha2, he2⟩ := exec_mov_fp_sp { env with pc := env.pc + 4 } (Arm.exec_inst a1 s)
  generalize hs1 : Arm.exec_inst a1 s = s1 at he2 ha2
  generalize hs2 : Arm.exec_inst a2 s1 = s2
  have hsp1 : spOf s1 = spOf s - 16#64 := by
    rw [← hs1, he1]; simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different]
  have ho1 : ∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f s1 = Arm.r f s := by
    intro f h1 h2; rw [← hs1, he1]; simp [Arm.r_of_w_different, h1, h2, Arm.r_of_write_mem_bytes]
  have hsp2 : spOf s2 = spOf s - 16#64 := by
    rw [← hs2, he2]; simp only [spOf] at hsp1 ⊢; simp [Arm.r_of_w_different, hsp1]
  have ho2 : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → Arm.r f s2 = Arm.r f s1 := by
    intro f h1 h2; rw [← hs2, he2]; simp [Arm.r_of_w_different, h1, h2]
  have hx29 : xreg 29 s2 = spOf s - 16#64 := by
    rw [← hs2, he2]; simp [xreg, Arm.r_of_w_same, hsp1]
  have hm2 : s2.mem = (Arm.write_mem_bytes 16 (spOf s - 16#64) (xreg 30 s ++ xreg 29 s) s).mem := by
    rw [← hs2, he2, ← hs1, he1]; simp [Arm.ArmState.mem_w_eq_mem]
  -- the stack probes
  have hal2 : (spOf s2).toNat % 16 = 0 := by rw [hsp2]; exact aligned_sub hal (by decide) (by decide)
  obtain ⟨sP, hP, hspP, -, hoP, hflP, hmP⟩ := probeRun_ok { env with pc := env.pc + 4 + 4 }
    (probeTotal size calls) s2 hal2
  rw [hn, hsp2] at hmP
  have hspP' : spOf sP = spOf s - 16#64 := by rw [hspP, hsp2]
  -- the probes zero nothing at the top of the frame
  have hnot : ∀ c k, c ≤ 4000 → k < c + 16 →
      probeHitB n (spOf s - 16#64) (spOf s - 16#64 - BitVec.ofNat 64 c + BitVec.ofNat 64 k) = false :=
    fun c k hc hk => probeHitB_top hc hk hn63
  -- the pushes
  obtain ⟨s3, h3, hsp3, ho3, he3, hp3, hm3, hv3⟩ := pushLines_ok
    { env with pc := env.pc + 4 + 4 + 4 * (probeLines (probeTotal size calls)).length } true
    (savesInt saves) sP (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)) hsv.int
    (by have := hsv.intLen; omega) hBIa (by rw [hspP', hT16])
  obtain ⟨s4, h4, hsp4, ho4, he4, hp4, hm4, hv4⟩ := pushLines_ok
    { env with pc := env.pc + 4 + 4 + 4 * (probeLines (probeTotal size calls)).length +
      4 * (pushLines true (savesInt saves)).length } false
    (savesFloat saves) s3 BF hsv.float (by have := hsv.floatLen; omega) hBFa hsp3
  obtain ⟨s5, h5, hsp5, ho5, hm5⟩ := spAdj_ok
    { env with pc := env.pc + 4 + 4 + 4 * (probeLines (probeTotal size calls)).length +
      4 * (pushLines true (savesInt saves)).length +
      4 * (pushLines false (savesFloat saves)).length } true (size := size - clobberBytes saves) (by omega) s4
  obtain ⟨he5, hp5⟩ := h5.err
  simp only [ite_true] at hsp5
  have hpb : ∀ n, n ≤ pushBytes n := fun n => by unfold pushBytes; omega
  -- the memory of `s5` against `sP` below fp/lr, and against `s` outside the frame top
  have hm5P : ∀ a, (∀ k < clobberBytes saves, a ≠ BF + BitVec.ofNat 64 k) → s5.mem a = sP.mem a := by
    intro a ha
    rw [hm5, hm4 a (fun k hk => ha k (by omega)), hm3 a (fun k hk e => ha
      (pushBytes (savesFloat saves).length + k) (by omega) (by rw [e, add_ofNat_add]))]
  have hm5I : ∀ k, k < pushBytes (savesInt saves).length → ∀ a,
      a = BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length + k) → s5.mem a = s3.mem a := by
    intro k hk a ha
    rw [hm5, hm4 a (fun k' hk' e => add_ofNat_ne (by omega) (by omega) (by omega) (ha.symm.trans e))]
  -- the fields of `sP` against `s`
  have hoP2 : ∀ f, f ≠ .PC → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 → (∀ fl, f ≠ .FLAG fl) →
      Arm.r f sP = Arm.r f s2 := hoP
  refine ⟨s5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨s2, sP, ?_, hsp2, hP, StepsOk.append h3 (StepsOk.append h4 h5)⟩
    show StepsOk env [.ins _ none, .ins _ none] s s2
    refine steps_cons ha1 (by rw [he1]; simp [Arm.r_of_w_same])
      (by rw [he1]; simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes])
      (by rw [he1]; simp [Arm.w_program, Arm.write_mem_bytes_program]) ?_
    rw [hs1]
    rw [← hs2]
    exact steps_one ha2 (by rw [he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different])
      (by rw [he2]; simp [Arm.r_of_w_different]) (by rw [he2]; simp [Arm.w_program])
  · rw [hsp5, hsp4, ← hBF]
    obtain ⟨d, rfl⟩ : ∃ d, size = clobberBytes saves + d := ⟨size - clobberBytes saves, by omega⟩
    rw [Nat.add_sub_cancel_left, BitVec.ofNat_add, BitVec.ofNat_add]
    exact frame_sp_eq _ _ _
  · rw [show xreg 29 s5 = xreg 29 s2 by
      simp only [xreg]
      rw [ho5 _ (by simp) (by decide) (by decide), ho4 _ (by simp) (by decide), ho3 _ (by simp) (by decide),
        hoP2 _ (by simp) (by decide) (by decide) (by decide) (by simp)]]
    exact hx29
  · intro f g1 g2 g3 g4 g5 g6
    rw [ho5 f g1 g3 g4, ho4 f g1 g3, ho3 f g1 g3, hoP2 f g1 g3 g4 g5 g6, ho2 f g1 g2, ho1 f g1 g3]
  · intro fl
    rw [ho5 _ (by simp) (by simp) (by simp), ho4 _ (by simp) (by simp), ho3 _ (by simp) (by simp), hflP fl]
    simp only [probeFlagT]
    split
    · rfl
    · rw [ho2 _ (by simp) (by simp), ho1 _ (by simp) (by simp)]
  · intro a ha
    rw [hm5P a (fun k hk e => ha k (by omega) (by rw [← hBF] at e ⊢; exact e)), hmP a, probeHitB_sub16]
    by_cases hh : probeHitN n (spOf s) a = true
    · simp only [hh, ite_true]
    simp only [hh, Bool.false_eq_true, ite_false]
    rw [hm2, Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
    simp only
    refine write_bytes_outside 16 _ _ _ (fun k hk e => ha (clobberBytes saves + k) (by omega) ?_)
    rw [e, hT16, add_ofNat_add, add_ofNat_add, ← hBF]
    congr 2; unfold clobberBytes; omega
  · rw [hT16]
    apply read_of_agree (t := s) (by decide)
    intro k hk
    have haddr : BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
        BitVec.ofNat 64 (pushBytes (savesInt saves).length) + BitVec.ofNat 64 k =
        spOf s - 16#64 - BitVec.ofNat 64 0 + BitVec.ofNat 64 k := by
      rw [← hT16]; simp
    rw [hm5P _ (fun k' hk' e => add_ofNat_ne (by omega) (by omega) (by omega)
      ((show BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
          BitVec.ofNat 64 (pushBytes (savesInt saves).length) + BitVec.ofNat 64 k =
          BF + BitVec.ofNat 64 (clobberBytes saves + k) by
        rw [add_ofNat_add, add_ofNat_add]; congr 2; unfold clobberBytes; omega).symm.trans e)), hmP,
      haddr, hnot 0 k (by decide) (by omega), ← haddr, if_neg (by decide), hm2, ← hT16]
  · intro r hr
    have hreg : ∀ n, 19 ≤ n → n < 29 → Arm.r (.GPR (rnum n)) sP = Arm.r (.GPR (rnum n)) s := fun n h19 hn => by
      have h31 : Arm.StateField.GPR (rnum n) ≠ .GPR 31#5 := fun e => rnum_ne31 hn (Arm.StateField.GPR.inj e)
      have hne : ∀ m, m < 32 → m ≠ n → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 m) := fun m hm hmn e => by
        have := congrArg BitVec.toNat (Arm.StateField.GPR.inj e)
        rw [rnum_toNat (by omega)] at this; simp at this; omega
      rw [hoP2 _ (by simp) h31 (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp),
        ho2 _ (by simp) (hne 29 (by omega) (by omega)), ho1 _ (by simp) h31]
    rcases saves_mem hsv hr with ⟨n, rfl, hi, ho⟩ | ⟨n, rfl, hi, ho⟩
    · have hn : n < 29 := (hsv.int _ (List.mem_of_getElem? hi)).2
      have h19 : 19 ≤ n := by
        rcases calleeSaved_cases (hsv.1 _ hr) with ⟨m, e, hm, -⟩ | ⟨m, e, -⟩
        · cases e; exact hm
        · cases e
      have hil : (savesInt saves).idxOf (.x n) < (savesInt saves).length := (List.getElem?_eq_some_iff.1 hi).1
      have hv := hv3 _ _ hi
      rw [ho, ← add_ofNat_add]
      have e1 : Arm.read_mem_bytes 8 (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
          BitVec.ofNat 64 (8 * (savesInt saves).idxOf (.x n))) s5 =
          Arm.read_mem_bytes 8 (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
          BitVec.ofNat 64 (8 * (savesInt saves).idxOf (.x n))) s3 :=
        read_mem_bytes_congr 8 _ (fun k hk => hm5I (8 * (savesInt saves).idxOf (.x n) + k)
          (by have : 8 * (savesInt saves).length ≤ pushBytes (savesInt saves).length := by
                unfold pushBytes; omega
              omega) _
          (by rw [add_ofNat_add, add_ofNat_add]))
      rw [e1, hv]
      simp only [slotVal]
      exact hreg n h19 hn
    · have hv := hv4 _ _ hi
      rw [ho]
      rw [show Arm.read_mem_bytes 8 (BF + BitVec.ofNat 64 (8 * (savesFloat saves).idxOf (.v n))) s5 =
          Arm.read_mem_bytes 8 (BF + BitVec.ofNat 64 (8 * (savesFloat saves).idxOf (.v n))) s4 from
        read_of_mem_eq hm5 _ _, hv]
      simp only [slotVal]
      rw [ho3 _ (by simp) (by simp), hoP2 _ (by simp) (by simp) (by simp) (by simp) (by simp),
        ho2 _ (by simp) (by simp), ho1 _ (by simp) (by simp)]

/-- **The epilogue runs up to the `ret`** (Cranelift's clobber restore and frame teardown):
`sp` raised by `size - clobberBytes`, the saved registers popped (`PopVal`: each gets its slot,
a `v` register zero-extended), fp/lr loaded from the 16 bytes above, `sp` raised by 16 more;
only the pc, `x29`, `x30`, `sp`, `x16` and the saved registers change, memory unchanged. -/
theorem epilogue_ok (env : Env) {saves : List Reg} {size : Nat} (hs : size < 2 ^ 64)
    (hsv : SavesOk saves) (hcb : clobberBytes saves ≤ size) (s : Arm.ArmState)
    (hal : (spOf s + BitVec.ofNat 64 (size - clobberBytes saves)).toNat % 16 = 0) :
    ∃ s', StepsOk env (spAdjLines false (size - clobberBytes saves) ++
        (popLines false (savesFloat saves) ++ (popLines true (savesInt saves) ++
          [.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16))]))) s s' ∧
      spOf s' = spOf s + BitVec.ofNat 64 size + 16#64 ∧
      xreg 29 s' = (Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 size) s).extractLsb' 0 64 ∧
      xreg 30 s' = (Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 size) s).extractLsb' 64 64 ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 30#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
        (∀ r ∈ saves, r.field ≠ some f) → Arm.r f s' = Arm.r f s) ∧
      s'.mem = s.mem ∧
      ∀ r ∈ saves, PopVal s' r (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 (size - clobberBytes saves) +
        BitVec.ofNat 64 (clobberOff saves r)) s) := by
  have hcbm := clobberBytes_mod saves
  have hcbl := hsv.clobber_le
  have hpIm := pushBytes_mod (savesInt saves).length
  have hpFm := pushBytes_mod (savesFloat saves).length
  have hcbe : clobberBytes saves = pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length := rfl
  obtain ⟨s1, h1, hsp1, ho1, hm1⟩ := spAdj_ok env false (size := size - clobberBytes saves) (by omega) s
  simp only [Bool.false_eq_true, ite_false] at hsp1
  obtain ⟨he1, hp1⟩ := h1.err
  generalize hBF : spOf s + BitVec.ofNat 64 (size - clobberBytes saves) = BF at hsp1 hal
  obtain ⟨s2, h2, hsp2, hm2, he2, hp2, ho2, hv2⟩ := popLines_ok
    { env with pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length } false
    (savesFloat saves) s1 BF hsv.float (hsv.2.filter _) hal hsp1
  have hBIa : (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)).toNat % 16 = 0 := by
    rw [show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16) by omega]
    exact aligned_add hal _
  obtain ⟨s3, h3, hsp3, hm3, he3, hp3, ho3, hv3⟩ := popLines_ok
    { env with pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length +
      4 * (popLines false (savesFloat saves)).length } true
    (savesInt saves) s2 _ hsv.int (hsv.2.filter _) hBIa hsp2
  have hT16 : spOf s3 = spOf s + BitVec.ofNat 64 size := by
    rw [hsp3, ← hBF, add_ofNat_add, add_ofNat_add]; congr 2; omega
  have hal3 : Arm.CheckSPAlignment s3 := checkSP_of (by
    rw [hsp3, show pushBytes (savesInt saves).length = 16 * (pushBytes (savesInt saves).length / 16) by omega]
    exact aligned_add hBIa _)
  obtain ⟨a4, ha4, he4⟩ := exec_ldp_fplr
    { env with pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length +
      4 * (popLines false (savesFloat saves)).length + 4 * (popLines true (savesInt saves)).length } s3 hal3
  have hm31 : s3.mem = s.mem := by rw [hm3, hm2, hm1]
  have hm41 : (Arm.exec_inst a4 s3).mem = s.mem := by
    rw [he4]; simp [Arm.ArmState.mem_w_eq_mem, hm31]
  have hrd : Arm.read_mem_bytes 16 (spOf s3) s3 = Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 size) s := by
    rw [hT16]; exact read_of_mem_eq hm31 _ _
  have ho4 : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 30#5 → f ≠ .GPR 31#5 →
      Arm.r f (Arm.exec_inst a4 s3) = Arm.r f s3 := by
    intro f g1 g2 g3 g4; rw [he4]; simp [Arm.r_of_w_different, g1, g2, g3, g4]
  -- a saved register's field is none of the frame's
  have hfr : ∀ r ∈ saves, ∀ f, r.field = some f →
      f ≠ .PC ∧ f ≠ .GPR 29#5 ∧ f ≠ .GPR 30#5 ∧ f ≠ .GPR 31#5 ∧ f ≠ .GPR 16#5 := by
    intro r hr f hf
    rcases calleeSaved_cases (hsv.1 r hr) with ⟨n, rfl, h1, h2⟩ | ⟨n, rfl, -⟩ <;>
      simp only [Reg.field, Option.some.injEq] at hf <;> subst hf
    · refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> intro e <;>
        have := congrArg BitVec.toNat (Arm.StateField.GPR.inj e) <;>
        rw [rnum_toNat (by omega)] at this <;> simp at this <;> omega
    · exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨Arm.exec_inst a4 s3, StepsOk.append h1 (StepsOk.append h2 (StepsOk.append h3
      (steps_one ha4 (by rw [he4]; simp [Arm.r_of_w_same]) (by rw [he4]; simp [Arm.r_of_w_different])
        (by rw [he4]; simp [Arm.w_program])))), ?_, ?_, ?_, fun f g1 g2 g3 g4 g5 g6 => ?_, hm41, ?_⟩
  · rw [he4]; simp only [spOf] at hT16 ⊢; simp [Arm.r_of_w_same, hT16]
  · rw [he4]; simp [xreg, Arm.r_of_w_same, Arm.r_of_w_different, hrd]
  · rw [he4]; simp [xreg, Arm.r_of_w_same, Arm.r_of_w_different, hrd]
  · have gI : ∀ r ∈ savesInt saves, r.field ≠ some f := fun r hr => g6 r (List.mem_filter.1 hr).1
    have gF : ∀ r ∈ savesFloat saves, r.field ≠ some f := fun r hr => g6 r (List.mem_filter.1 hr).1
    rw [ho4 f g1 g2 g3 g4, ho3 f g1 g4 gI, ho2 f g1 g4 gF, ho1 f g1 g4 g5]
  · intro r hr
    have hkeep : ∀ (t : Arm.ArmState) (v : BitVec 64), PopVal t r v →
        (∀ f, r.field = some f → Arm.r f (Arm.exec_inst a4 s3) = Arm.r f t) →
        PopVal (Arm.exec_inst a4 s3) r v := fun t v hv h => popVal_congr h hv
    rcases saves_mem hsv hr with ⟨n, rfl, hi, ho⟩ | ⟨n, rfl, hi, ho⟩
    · have hv := hv3 _ _ hi
      refine hkeep s3 _ ?_ (fun f hf => ?_)
      · rw [ho, ← add_ofNat_add, ← read_of_mem_eq (show s2.mem = s.mem by rw [hm2, hm1])]
        exact hv
      · obtain ⟨g1, g2, g3, g4, -⟩ := hfr _ hr f hf
        exact ho4 f g1 g2 g3 g4
    · have hv := hv2 _ _ hi
      refine hkeep s2 _ ?_ (fun f hf => ?_)
      · rw [ho, ← read_of_mem_eq hm1]
        exact hv
      · obtain ⟨g1, g2, g3, g4, -⟩ := hfr _ hr f hf
        rw [ho4 f g1 g2 g3 g4, ho3 f g1 g4 (fun r' hr' e => by
          simp only [Reg.field, Option.some.injEq] at hf
          subst hf
          have := (hsv.int r' hr')
          cases r' <;> simp [Reg.field, PushReg] at e this)]

theorem spAdjLines_noLoads (sub : Bool) (size : Nat) :
    ∀ i t, Line.ins i t ∈ spAdjLines sub size → i.loads = false := by
  intro i t hln
  unfold spAdjLines at hln
  split at hln
  · simp at hln
  · split at hln
    · simp only [List.mem_singleton, Line.ins.injEq] at hln
      obtain ⟨rfl, -⟩ := hln; rfl
    · rw [List.mem_append] at hln
      rcases hln with hln | hln
      · exact loadConst64_noLoads _ _ _ _ hln
      · simp only [List.mem_singleton, Line.ins.injEq] at hln
        obtain ⟨rfl, -⟩ := hln; rfl




/-- The epilogue up to the `ret` reads `[sp + size - clobberBytes, sp + size + 16)`: the
clobber area and fp/lr. -/
theorem epilogue_reads (env : Env) {saves : List Reg} {size : Nat} (hs : size < 2 ^ 64)
    (hsv : SavesOk saves) (hcb : clobberBytes saves ≤ size) (s : Arm.ArmState)
    (hal : (spOf s + BitVec.ofNat 64 (size - clobberBytes saves)).toNat % 16 = 0) {P : BitVec 64 → Prop}
    (hP : ∀ k < clobberBytes saves + 16,
      P (spOf s + BitVec.ofNat 64 (size - clobberBytes saves) + BitVec.ofNat 64 k)) :
    LinesReads env (spAdjLines false (size - clobberBytes saves) ++
        (popLines false (savesFloat saves) ++ (popLines true (savesInt saves) ++
          [.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16))]))) s P := by
  have hcbm := clobberBytes_mod saves
  have hcbl := hsv.clobber_le
  have hpIm := pushBytes_mod (savesInt saves).length
  have hpFm := pushBytes_mod (savesFloat saves).length
  have hcbe : clobberBytes saves = pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length := rfl
  obtain ⟨s1, h1, hsp1, -, hm1⟩ := spAdj_ok env false (size := size - clobberBytes saves) (by omega) s
  simp only [Bool.false_eq_true, ite_false] at hsp1
  refine linesReads_app (linesReads_noLoads (spAdjLines_noLoads false _)) fun s1' hs1' => ?_
  rw [execLines_steps h1 hs1']
  have hal1 : (spOf s1).toNat % 16 = 0 := by rw [hsp1]; exact hal
  obtain ⟨s2, h2, hsp2, -⟩ := popLines_ok
    { env with pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length } false
    (savesFloat saves) s1 _ hsv.float (hsv.2.filter _) hal1 rfl
  refine linesReads_app (popLines_reads _ false _ s1 hsv.float (hsv.2.filter _) hal1 fun k hk => ?_)
    fun s2' hs2' => ?_
  · rw [hsp1]; exact hP k (by omega)
  rw [execLines_steps h2 hs2']
  have hal2 : (spOf s2).toNat % 16 = 0 := by
    rw [hsp2, show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16) by omega]
    exact aligned_add hal1 _
  obtain ⟨s3, h3, hsp3, -⟩ := popLines_ok _ true (savesInt saves) s2 _ hsv.int (hsv.2.filter _) hal2 rfl
  refine linesReads_app (popLines_reads _ true _ s2 hsv.int (hsv.2.filter _) hal2 fun k hk => ?_)
    fun s3' hs3' => ?_
  · rw [hsp2, hsp1, add_ofNat_add, add_ofNat_add]
    have := hP (pushBytes (savesFloat saves).length + k) (by omega)
    rwa [add_ofNat_add] at this
  rw [execLines_steps h3 hs3']
  refine linesReads_cons (fun _ _ h => by simp at h) fun env' a ha q hq k hk => ?_
  rw [memReads_ldp_fplr ha] at hq
  simp only [List.mem_singleton] at hq; subst hq
  rw [hsp3, hsp2, hsp1, add_ofNat_add, add_ofNat_add, add_ofNat_add]
  have := hP (pushBytes (savesFloat saves).length + pushBytes (savesInt saves).length + k) (by simp at hk; omega)
  rwa [add_ofNat_add, Nat.add_assoc (pushBytes _)] at this

/-! ## The shape of the frame lines -/

/-- The instructions of the pushes. -/
def PushIns (x : Insn) : Prop :=
  ∃ r r', x = .store .store64 r (.spPreIndexed (-16)) ∨ x = .stp r r' (.spPreIndexed (-16)) ∨
    x = .fpuStore .size64 r (.spPreIndexed (-16)) ∨ x = .fpuStoreP .size64 r r' (.spPreIndexed (-16))

/-- The instructions of the pops. -/
def PopIns (x : Insn) : Prop :=
  ∃ r r', x = .load .uload64 r (.spPostIndexed 16) ∨ x = .ldp r r' (.spPostIndexed 16) ∨
    x = .fpuLoad .size64 r (.spPostIndexed 16) ∨ x = .fpuLoadP .size64 r r' (.spPostIndexed 16)

theorem pushLines_mem {int : Bool} {rs : List Reg} {ln : Line} (h : ln ∈ pushLines int rs) :
    ∃ x, ln = .ins x none ∧ PushIns x := by
  rw [pushLines_eq, List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton] at h; subst h
      rename_i r _
      exact ⟨_, rfl, r, r, by cases int <;> simp⟩
    · simp at h
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
    exact ⟨_, rfl, p.1, p.2, by cases int <;> simp⟩

theorem popLines_mem {int : Bool} {rs : List Reg} {ln : Line} (h : ln ∈ popLines int rs) :
    ∃ x, ln = .ins x none ∧ PopIns x := by
  rw [popLines_eq, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
    exact ⟨_, rfl, p.1, p.2, by cases int <;> simp⟩
  · split at h
    · simp only [List.mem_singleton] at h; subst h
      rename_i r _
      exact ⟨_, rfl, r, r, by cases int <;> simp⟩
    · simp at h

end Backend.Proof

namespace E2E

theorem append_inj' {n m : Nat} {x x' : BitVec n} {y y' : BitVec m} (h : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun z => z.getLsbD (i + m)) h
    simpa [BitVec.getLsbD_append, show ¬ (i + m < m) by omega] using this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun z => z.getLsbD i) h
    simpa [BitVec.getLsbD_append, hi] using this

theorem read_mem_bytes_bytes : ∀ (n : Nat) (a : BitVec 64) (s t : Arm.ArmState),
    Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a t →
    ∀ k < n, s.mem (a + BitVec.ofNat 64 k) = t.mem (a + BitVec.ofNat 64 k)
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, a, s, t, h, k, hk => by
    simp only [Arm.read_mem_bytes] at h
    have h' := congrArg (BitVec.cast (by omega : (n + 1) * 8 = n * 8 + 8)) h
    simp only [BitVec.cast_cast, BitVec.cast_eq] at h'
    have hh := append_inj' h'
    cases k with
    | zero =>
      have := hh.2
      simpa [Arm.read_mem, Arm.read_store] using this
    | succ j =>
      have := read_mem_bytes_bytes n (a + 1#64) s t hh.1 j (by omega)
      rwa [BitVec.add_assoc, show (1#64 : BitVec 64) + BitVec.ofNat 64 j = BitVec.ofNat 64 (j + 1) by
        apply BitVec.eq_of_toNat_eq; simp; omega] at this

end E2E
