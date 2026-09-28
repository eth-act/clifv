import FV.E2E.RegLevelJT

/-!
# Prologue and epilogue on the machine (M6)
-/

namespace Backend.Proof

open Backend E2E

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

theorem exec_sub_sp_x16 (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.aluRRRExtend .sub true .sp .sp (.x 16) .uxtx).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 31#5) (spOf s - xreg 16 s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_sub_neg, extend_uxtx0, xreg]

theorem exec_add_sp_x16 (env : Env) (s : Arm.ArmState) :
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

/-- The frame allocation/deallocation `sub/add sp, sp, #size` (or via `x16` for large sizes). -/
def spAdjLines (sub : Bool) (size : Nat) : List Line :=
  if size == 0 then []
  else match Imm12.ofNat? size with
    | some i => [.ins (.aluImm12 (if sub then .sub else .add) true .sp .sp i)]
    | none => loadConst64 (.x 16) size ++
        [.ins (.aluRRRExtend (if sub then .sub else .add) true .sp .sp (.x 16) .uxtx)]

theorem prologueLines_eq (size : Nat) :
    prologueLines size = [.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))), .ins (.mov true Reg.fp .sp)] ++
      spAdjLines true size := by
  simp only [prologueLines, spAdjLines]; rfl

theorem epilogueLines_eq (size : Nat) :
    epilogueLines size = spAdjLines false size ++
      [.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)), .ins .ret] := by
  simp only [epilogueLines, spAdjLines]; rfl

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
    · obtain ⟨a, ha, he⟩ := exec_add_sp_x16 { env with pc := env.pc + 4 * (loadConst64 (.x 16) size).length } s1
      refine ⟨_, StepsOk.append hL (steps_one ha ?_ ?_ ?_), ?_, fun f h1 h2 h3 => ?_, ?_⟩
      · simp [he, Arm.r_of_w_same, Arm.r_of_w_different]
      · simp [he, Arm.r_of_w_different]
      · simp [he, Arm.w_program]
      · simp [he, spOf, Arm.r_of_w_same, hx16]; simpa [spOf] using congrArg (· + BitVec.ofNat 64 size) hsp1
      · simp [he, Arm.r_of_w_different, h1, h2, ho1 f h1 h3]
      · simp [he, Arm.ArmState.mem_w_eq_mem, hm1]
    · obtain ⟨a, ha, he⟩ := exec_sub_sp_x16 { env with pc := env.pc + 4 * (loadConst64 (.x 16) size).length } s1
      refine ⟨_, StepsOk.append hL (steps_one ha ?_ ?_ ?_), ?_, fun f h1 h2 h3 => ?_, ?_⟩
      · simp [he, Arm.r_of_w_same, Arm.r_of_w_different]
      · simp [he, Arm.r_of_w_different]
      · simp [he, Arm.w_program]
      · simp [he, spOf, Arm.r_of_w_same, hx16]; simpa [spOf] using congrArg (· - BitVec.ofNat 64 size) hsp1
      · simp [he, Arm.r_of_w_different, h1, h2, ho1 f h1 h3]
      · simp [he, Arm.ArmState.mem_w_eq_mem, hm1]

/-- **The prologue runs**: fp/lr pushed at `sp - 16`, `x29 = sp - 16`, `sp` lowered by
`16 + size`; only the pc, `x29`, `sp` and `x16` change, memory only at the fp/lr slot. -/
theorem prologue_ok (env : Env) {size : Nat} (hs : size < 2 ^ 64) (s : Arm.ArmState)
    (hal : Arm.CheckSPAlignment s) :
    ∃ s', StepsOk env (prologueLines size) s s' ∧
      spOf s' = spOf s - 16#64 - BitVec.ofNat 64 size ∧ xreg 29 s' = spOf s - 16#64 ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → Arm.r f s' = Arm.r f s) ∧
      s'.mem = (Arm.write_mem_bytes 16 (spOf s - 16#64) (xreg 30 s ++ xreg 29 s) s).mem := by
  obtain ⟨a1, ha1, he1⟩ := exec_stp_fplr env s hal
  obtain ⟨a2, ha2, he2⟩ := exec_mov_fp_sp { env with pc := env.pc + 4 } (Arm.exec_inst a1 s)
  obtain ⟨s3, h3, hsp3, ho3, hm3⟩ :=
    spAdj_ok { env with pc := env.pc + 4 + 4 } true hs (Arm.exec_inst a2 (Arm.exec_inst a1 s))
  have hsp1 : spOf (Arm.exec_inst a1 s) = spOf s - 16#64 := by
    rw [he1]; simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different]
  have ho1 : ∀ f, f ≠ .PC → f ≠ .GPR 31#5 → Arm.r f (Arm.exec_inst a1 s) = Arm.r f s := by
    intro f h1 h2; rw [he1]; simp [Arm.r_of_w_different, h1, h2, Arm.r_of_write_mem_bytes]
  have ho2 : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 →
      Arm.r f (Arm.exec_inst a2 (Arm.exec_inst a1 s)) = Arm.r f (Arm.exec_inst a1 s) := by
    intro f h1 h2; rw [he2]; simp [Arm.r_of_w_different, h1, h2]
  rw [prologueLines_eq]
  refine ⟨s3, steps_cons ha1 ?_ ?_ ?_ (steps_cons ha2 ?_ ?_ ?_ h3), ?_, ?_, ?_, ?_⟩
  · rw [he1]; simp [Arm.r_of_w_same]
  · rw [he1]; simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes]
  · rw [he1]; simp [Arm.w_program, Arm.write_mem_bytes_program]
  · rw [he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different]
  · rw [he2]; simp [Arm.r_of_w_different]
  · rw [he2]; simp [Arm.w_program]
  · rw [hsp3]; simp only [↓reduceIte]
    have : spOf (Arm.exec_inst a2 (Arm.exec_inst a1 s)) = spOf (Arm.exec_inst a1 s) :=
      ho2 _ (by simp) (by decide)
    rw [this, hsp1]
  · simp only [xreg]
    rw [ho3 _ (by simp) (by decide) (by decide), he2]
    simp [Arm.r_of_w_same, hsp1]
  · intro f h1 h2 h3 h4
    rw [ho3 f h1 h3 h4, ho2 f h1 h2, ho1 f h1 h3]
  · rw [hm3, he2, he1]; simp [Arm.ArmState.mem_w_eq_mem]

/-- **The epilogue runs up to the `ret`**: `sp` raised by `size`, fp/lr loaded from `sp`, `sp`
raised by 16; only the pc, `x29`, `x30`, `sp` and `x16` change, memory unchanged. -/
theorem epilogue_ok (env : Env) {size : Nat} (hs : size < 2 ^ 64) (s : Arm.ArmState)
    (hal : (spOf s + BitVec.ofNat 64 size).toNat % 16 = 0) :
    ∃ s', StepsOk env (spAdjLines false size ++ [.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16))]) s s' ∧
      spOf s' = spOf s + BitVec.ofNat 64 size + 16#64 ∧
      xreg 29 s' = (Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 size) s).extractLsb' 0 64 ∧
      xreg 30 s' = (Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 size) s).extractLsb' 64 64 ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 30#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
        Arm.r f s' = Arm.r f s) ∧
      s'.mem = s.mem := by
  obtain ⟨s1, h1, hsp1, ho1, hm1⟩ := spAdj_ok env false hs s
  simp only [Bool.false_eq_true, ite_false] at hsp1
  have hal1 : Arm.CheckSPAlignment s1 := (checkSP_iff s1).2 (by rw [hsp1]; exact hal)
  obtain ⟨a, ha, he⟩ :=
    exec_ldp_fplr { env with pc := env.pc + 4 * (spAdjLines false size).length } s1 hal1
  have hrd : Arm.read_mem_bytes 16 (spOf s1) s1 = Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 size) s := by
    rw [hsp1]; exact read_mem_bytes_congr _ _ (fun k _ => by rw [hm1])
  refine ⟨_, StepsOk.append h1 (steps_one ha ?_ ?_ ?_), ?_, ?_, ?_, ?_, ?_⟩
  · rw [he]; simp [Arm.r_of_w_same]
  · rw [he]; simp [Arm.r_of_w_different]
  · rw [he]; simp [Arm.w_program]
  · rw [he]; simp only [spOf, Arm.r_of_w_different (show Arm.StateField.GPR 31#5 ≠ .PC by simp),
      Arm.r_of_w_same]
    show spOf s1 + 16#64 = spOf s + BitVec.ofNat 64 size + 16#64
    rw [hsp1]
  · rw [he]; simp [xreg, Arm.r_of_w_same, Arm.r_of_w_different, hrd]
  · rw [he]; simp [xreg, Arm.r_of_w_same, Arm.r_of_w_different, hrd]
  · intro f f1 f2 f3 f4 f5
    rw [he]; simp [Arm.r_of_w_different, f1, f2, f3, f4]; exact ho1 f f1 f4 f5
  · rw [he]; simp [Arm.ArmState.mem_w_eq_mem, hm1]

end Backend.Proof
