import FV.E2E.RegLevelTrap
import FV.Backend.Proof.IselCtlTerm

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

/-! ## Machine facts about the frame lines -/

theorem stepsOk_interOk {env : Env} {ls : List Line} {s s' : Arm.ArmState} (h : StepsOk env ls s s')
    (herr : Arm.r .ERR s = .None) : InterOk env ls s := by
  intro k _ _ s1 h1
  obtain ⟨s2, h2⟩ := StepsOk.take k h
  rw [h2.exec] at h1
  cases h1
  obtain ⟨e1, e2⟩ := h2.err
  exact ⟨e1.trans herr, e2⟩

theorem movkLines_mem {n : Nat} : ∀ {ks : List (Nat × Nat)} {ln : Line}, ln ∈ movkLines n ks →
    ∃ c i, ln = .ins (.movk true (.x n) ⟨c, i⟩) none
  | [], _, h => by simp [movkLines] at h
  | (c, i) :: ks, ln, h => by
    simp only [movkLines, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨c, i, rfl⟩
    · exact movkLines_mem h

/-- The frame lines are plain, unhooked instruction lines. -/
theorem spAdjLines_ins (sub : Bool) (size : Nat) :
    ∀ ln ∈ spAdjLines sub size, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true := by
  intro ln hln
  unfold spAdjLines at hln
  split at hln
  · simp at hln
  · split at hln
    · simp only [List.mem_singleton] at hln
      subst hln; exact ⟨_, rfl, rfl, by cases sub <;> rfl⟩
    · rw [List.mem_append, loadConst64_eq] at hln
      rcases hln with hln | hln
      · simp only [List.mem_cons] at hln
        rcases hln with rfl | hln
        · exact ⟨_, rfl, rfl, rfl⟩
        · obtain ⟨c, i, rfl⟩ := movkLines_mem hln
          exact ⟨_, rfl, rfl, rfl⟩
      · simp only [List.mem_singleton] at hln
        subst hln; exact ⟨_, rfl, rfl, by cases sub <;> rfl⟩

theorem prologueLines_ins (size : Nat) :
    ∀ ln ∈ prologueLines size, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true := by
  intro ln hln
  rw [prologueLines_eq, List.mem_append] at hln
  rcases hln with hln | hln
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
    rcases hln with rfl | rfl <;> exact ⟨_, rfl, rfl, rfl⟩
  · exact spAdjLines_ins true size ln hln

/-- Straight-line lines at line `j` of the final code run as machine steps. -/
theorem iterN_steps {R : RL} (hR : R.Wf) {ls T : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hdrop : R.L.drop j = ls ++ T)
    (hins : ∀ ln ∈ ls, ∃ x, ln = .ins x none ∧ x.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h : StepsOk (R.envOf j) ls s s') :
    iterN R.step ls.length s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls.length) ∧
      ∀ i, 0 < i → i ≤ ls.length → R.Good (iterN R.step i s) := by
  have hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls, ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨x, e, -⟩ := hins ln h; exact ⟨x, none, e⟩
  have hrun := h.exec
  refine ⟨iterN_execLines hR.layout hR.lm hR.fit ls j s s' hat
      (fun i t hm => by obtain ⟨x, e, hh⟩ := hins _ hm; cases e; exact hh)
      hprog (by rw [hpc]; rfl) herr (stepsOk_interOk h herr) hrun, ?_,
    R.good_execLines hR hat (fun i t hm => by obtain ⟨x, e, hh⟩ := hins _ hm; cases e; exact hh)
      hprog hpc herr (stepsOk_interOk h herr) hrun⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop) hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-! ## The prologue on the machine: `Q` at the entry configuration -/

theorem noTrap_next {R : RL} {c2 : List AInst} {psm ps2 : PState} {ls2 : List Line} {b : Nat}
    (h2 : codeLinesE R.ctx R.af c2 psm = .ok (ls2, ps2)) :
    ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
  intro n e
  have hm := List.mem_of_getElem? e
  rcases List.mem_append.1 hm with hm | hm
  · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
  · simp only [nxtOf] at hm
    split at hm <;> simp at hm

/-- The entry block in the final lines: its label at line 0, then the prologue, then the
`fallthrough` of its items' lines. -/
theorem entry_block {R : RL} (hR : R.Wf) :
    ∃ vb items code ls ps1 ps2 T, R.vc.blocks[0]? = some vb ∧ R.rf.blocks[0]? = some items ∧
      itemsCode R.fr vb items.toList = .ok code ∧ codeLinesE R.ctx R.af code ps1 = .ok (ls, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L[0]? = some (.label (.block vb.label)) ∧
      R.L.drop 1 = prologueLines R.af.frameSize ++ (ftList (ls ++ nxtOf R.af 0) ++ T) := by
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  have h0 : 0 < R.vc.blocks.size := Nat.pos_of_ne_zero hc.nonempty
  obtain ⟨vb, hvb⟩ : ∃ vb, R.vc.blocks[0]? = some vb := ⟨_, Array.getElem?_eq_getElem h0⟩
  obtain ⟨items, hit⟩ : ∃ items, R.rf.blocks[0]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by rw [hc.size]; exact h0)⟩
  have hframe := lowerRFunc_frame hR.alloc
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, hcode, haf⟩ := hbl 0 vb items hvb hit
  obtain ⟨body, psF, hb, -, hblk⟩ := emit_block hR.emit
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨j0, lsA, ps1, ps2, T, hj0, hdrop, hls, htr, hj⟩ := hblk 0 _ _ haf
  obtain rfl := hj rfl
  simp only [ite_true] at hls
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  refine ⟨vb, items, code, ls2, ps1, ps2, T, hvb, hit, hcode, h2, htr, hj0, ?_⟩
  show List.drop (0 + 1) R.fa.lines.toList = _
  rw [hdrop, List.append_assoc, ftList_plain_append _ _
    (fun ln h => by obtain ⟨_, _, _, hp⟩ := prologueLines_ins _ ln h; exact hp) (noTrap_next h2), List.append_assoc]

theorem sp_sub16 (x : BitVec 64) (n : Nat) :
    x - 16#64 - BitVec.ofNat 64 n = x - BitVec.ofNat 64 (n + 16) := by
  rw [BitVec.ofNat_add]; bv_omega

/-- **After the prologue**: the machine is at the entry configuration of the allocated code
(store = the machine's locations, world = any body-entry world `w₀`), `AInv` holds, and every
field but the pc, x16, x29 and `sp` is as at entry. -/
theorem q_init {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, (∀ i, 0 < i → i < n → R.Good (iterN R.step i R.s0)) ∧
      Q R (iterN R.step n R.s0) (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      AInv R (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
        Arm.r f (iterN R.step n R.s0) = Arm.r f R.s0 := by
  have hframe := lowerRFunc_frame hR.alloc
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  have hal0 : Arm.CheckSPAlignment R.s0 := (checkSP_iff _).2 hent.spAligned
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, hsp', hfp', ho', hm'⟩ := prologue_ok (R.envOf 1) hs R.s0 hal0
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, hpc', hgood⟩ := iterN_steps hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  obtain ⟨herr', hprog'⟩ := hsteps.err
  refine ⟨(prologueLines R.af.frameSize).length, fun i h0 hi => hgood i h0 (Nat.le_of_lt hi), ?_⟩
  rw [hiter]
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hspB : spOf s' = R.spB := by
    rw [hsp', RL.spB, hdrop0]; exact sp_sub16 _ _
  -- the fp/lr slot
  have hslot : ∀ a, (∀ k < 16, a ≠ spv R.s0 - 16#64 + BitVec.ofNat 64 k) → s'.mem a = R.s0.mem a := by
    intro a ha
    rw [hm', Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
    exact write_bytes_outside 16 _ _ _ ha
  have hmemF : ∀ a, ¬ R.F a → s'.mem a = w₀.mem a := by
    intro a ha
    rw [hslot a (fun k hk e => ha (e ▸ RL.FK_F (fplr_inF hR hframe k hk))), hbe.mem a ha]
  have hcode' : ∀ a, CodeAddr R.s0 a → s'.mem a = R.s0.mem a := by
    intro a ha
    apply hslot
    intro k hk e
    have h2 := hst0.2 a ha
    rw [e] at h2
    have : spv R.s0 - 16#64 + BitVec.ofNat 64 k - (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)) =
        BitVec.ofNat 64 (R.af.frameSize + k) := by
      apply BitVec.eq_of_toNat_eq
      have := hst0.1
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := R.af.frameSize + 16) (by omega),
        Nat.mod_eq_of_lt (a := R.af.frameSize + k) (by omega)]
      simp only [spv] at *
      omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
    omega
  have hfield : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
      Arm.r f s' = Arm.r f R.s0 := ho'
  -- the kept addresses are not the fp/lr slot
  have hgk : ∀ a, R.G a → s'.mem a = R.s0.mem a := by
    intro a ha
    apply hslot
    intro k hk e
    apply hR.gfree a ha
    rw [e, hdrop0]
    have := hst0.1
    have hk64 : (spv R.s0 - 16#64 + BitVec.ofNat 64 k).toNat = (spv R.s0).toNat - 16 + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := (spv R.s0).isLt
      rw [Nat.mod_eq_of_lt (a := k) (by omega)]
      simp only [spv] at *
      omega
    simp only [StackBelow, hk64]
    constructor <;> omega
  refine ⟨?_, ?_, hfield⟩
  · have hitems : R.rf.blocks[0]! = items := by simp [getElem!_def, hit]
    simp only [MConf.init, hitems]
    refine ⟨1 + (prologueLines R.af.frameSize).length, vb, items, [], code, ls, ps1, ps2, T, hvb,
      hit, rfl, itemsChecked_block hR hvb hit, hcode, hls, htr, ?_, hpc', ?_⟩
    · rw [← List.drop_drop, hdrop, List.drop_left]
    · refine ⟨fun l _ _ => rfl, ⟨fun f hf => ?_, hmemF, ?_⟩, by rw [herr', hent.err], by rw [hprog', hent.program],
        hspB, ?_, fun _ => ?_, code_keep hR.prog0 hent.code hcode', hgk⟩
      · by_cases h29 : f = .GPR 29#5
        · subst h29
          have := hbe.fp
          simp only [hframe, ite_true, xreg] at this hfp'
          rw [hfp', this]; rfl
        by_cases h31 : f = .GPR 31#5
        · subst h31
          have := hbe.sp
          simp only [spv] at this
          rw [this]; exact hspB
        have h16 : f ≠ .GPR 16#5 := by rintro rfl; exact hf (by simp [Masked])
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        rw [hfield f hpc h29 h31 h16, hbe.other f hf h29 h31]
      · rw [hprog', hbe.program]
      · rw [checkSP_iff, hspB]
        simp only [RL.spB, hdrop0]
        have := hst0.1
        have ha := hent.spAligned
        have hm : (R.af.frameSize + 16) % 2 ^ 64 = R.af.frameSize + 16 := Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat, hm]; omega),
          BitVec.toNat_ofNat, hm]
        have : R.af.frameSize % 16 = 0 := by
          rw [(lowerRFunc_ok hR.alloc).1.1]; exact alignTo16_mod _
        omega
      · rw [← Arm.read_mem_bytes_of_write_mem_bytes_same (n := 16) (addr := spv R.s0 - 16#64)
          (v := xreg 30 R.s0 ++ xreg 29 R.s0) (s := R.s0) (by decide)]
        exact read_mem_bytes_congr _ _ (fun k _ => by rw [hm']; rfl)
  · intro _ _ r hr
    show regVal s' r = regVal w₀ r
    rw [hbe.args r hr]
    obtain ⟨vb', ds, hvb', hi', v, hv⟩ := hr
    have hr := ((ctlCheck_args (lowerRFunc_ok hR.alloc).2.2 hvb' hi').2.2 _ hv).2
    cases r with
    | x n =>
      simp only [Reg.isArgReg, decide_eq_true_eq] at hr
      have hne : ∀ m, 8 < m → m < 32 → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 m) :=
        fun m h1 h2 e => rnum_ne (a := n) (b := m) (by omega) h2 (by omega) (Arm.StateField.GPR.inj e)
      simp only [regVal]
      rw [hfield _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
        (hne 16 (by omega) (by omega))]
    | v n =>
      simp only [regVal]
      rw [hfield _ (by simp) (by simp) (by simp) (by simp)]
    | _ => simp [Reg.isArgReg] at hr

/-! ## The return on the machine -/

theorem ctlCheck_rets {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true) {b k : Nat}
    {vb : VBlock} {us : List (Reg × Reg)} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.rets us)) : ∃ ns, us = retPairs ns := by
  have h2 := ctlCheck_inst h hvb hi
  simp only [ctlInstOk, List.all_eq_true] at h2
  obtain ⟨ns, rfl, -⟩ := argPairs_of (fun p hp => isVregInt_iff (h2 p hp))
  exact ⟨ns, rfl⟩

theorem assign_rets {us : List (Reg × Reg)} {regs : Array Reg} {i' : MInst}
    (h : (MInst.rets us).assign regs = .ok i') : ∃ us', i' = .rets us' := by
  unfold MInst.assign at h
  simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure] at h
  generalize StateT.run _ 0 = X at h
  cases X with
  | error e => cases h
  | ok v =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      exact ⟨_, h.symm⟩

/-- The `j`-th use value of a `Rets` is the store's value of its `j`-th fixed register. -/
theorem rets_uses {ns : List (Nat × Reg)} {allocs : Array Loc} {m : Loc → CV}
    (hfix : ∀ p ∈ ((retOps ns).toArray.zip allocs).toList, ∀ r, p.1.con = .fixed r → p.2 = .reg r)
    (_hsz : (retOps ns).toArray.size = allocs.size) :
    ∀ (j : Nat) (v p : Reg) (x : CV), (retPairs ns)[j]? = some (v, p) →
      ((((retOps ns).toArray.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))[j]? = some x →
      x = m (.reg p) ∧ ∃ q ∈ ((retOps ns).toArray.zip allocs).toList, q.2 = .reg p := by
  intro j v p x hj hx
  have hu : ((retOps ns).toArray.zip allocs).toList.filter (·.1.isUse) =
      ((retOps ns).toArray.zip allocs).toList := by
    rw [List.filter_eq_self]
    intro q hq
    have := (List.of_mem_zip (by simpa using hq)).1
    simp only [retOps, List.mem_map] at this
    obtain ⟨_, -, e⟩ := this
    rw [← e]; rfl
  rw [hu] at hx
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hq' := hq
  simp only [Array.toList_zip, List.getElem?_zip_eq_some] at hq'
  obtain ⟨h1, -⟩ := hq'
  simp only [retPairs, retOps, List.getElem?_map, Option.map_eq_some_iff] at hj h1
  obtain ⟨q1, hq1, e1⟩ := hj
  obtain ⟨q2, hq2, e2⟩ := h1
  rw [hq1] at hq2; cases hq2
  simp only [Prod.mk.injEq] at e1
  obtain ⟨-, rfl⟩ := e1
  have e3 := hfix q (List.mem_of_getElem? hq) q1.2 (by rw [← e2])
  exact ⟨by rw [e3], q, List.mem_of_getElem? hq, e3⟩

theorem iterN_one_succ {S : Type} (f : S → S) (n : Nat) (s : S) :
    iterN f (n + 1) s = f (iterN f n s) := by
  rw [iterN_add]; rfl

/-- **The return on the machine**: from `Q` at a `Rets` item, the epilogue and `ret` reach the
return address with `sp` and x29 as at entry, the allocatable registers and the memory as at
the item, and the returned values in their fixed registers. -/
theorem ret_machine {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, (∀ i < n, R.Good (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0 ∧
      (∀ r, r.allocatable = true → regVal (iterN R.step n s) r = regVal s r) ∧
      (iterN R.step n s).mem = s.mem ∧
      (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f (iterN R.step n s) = Arm.r f s) ∧
      (iterN R.step n s).program = s.program ∧
      ∀ ops, (MInst.rets us).operands = .ok ops → ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) →
        ((((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)))[j]? = some x →
        regVal (iterN R.step n s) p = x := by
  have hframe := lowerRFunc_frame hR.alloc
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨us', rfl⟩ := assign_rets hasg
  obtain rfl : c1 = [.epilogueRet] := by
    rcases hc1' with ⟨-, -, h⟩ | ⟨_, h, -⟩ | ⟨_, -, h⟩
    · exact absurd rfl (h us')
    · cases h
    · exact h
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  rw [epilogueLines_eq] at hdrop
  have hpl : ∀ ln ∈ spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none, .ins .ret none], ln.plain = true := by
    intro ln hln
    rcases List.mem_append.1 hln with hln | hln
    · obtain ⟨_, _, _, hp⟩ := spAdjLines_ins false _ ln hln; exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
      rcases hln with rfl | rfl <;> rfl
  rw [ftList_plain_append _ _ hpl (noTrap_next h2)] at hdrop
  have hdrop' : R.L.drop j0 = (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]) ++
      (.ins .ret none :: (ftList (ls2 ++ nxtOf R.af b) ++ T)) := by
    rw [hdrop]; simp
  -- alignment of `sp + size` (= the fp/lr slot)
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hslot : spOf s + BitVec.ofNat 64 R.af.frameSize = spv R.s0 - 16#64 := by
    rw [hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hal : (spOf s + BitVec.ofNat 64 R.af.frameSize).toNat % 16 = 0 := by
    have h16 : 16 ≤ (spv R.s0).toNat := by have := hst0.1; omega
    rw [hslot, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h16)]
    have := hent.spAligned
    simp; omega
  obtain ⟨s1, hsteps, hsp1, hx29, hx30, ho1, hm1⟩ := epilogue_ok (R.envOf j0) hs s hal
  obtain ⟨hiter, hpc1, hgood⟩ := iterN_steps hR hdrop'
    (fun ln h => by
      rcases List.mem_append.1 h with h | h
      · obtain ⟨x, e, hh, -⟩ := spAdjLines_ins false _ ln h; exact ⟨x, e, hh⟩
      · simp only [List.mem_singleton] at h; exact ⟨_, h, rfl⟩)
    hst.prog hpc hst.err hsteps
  obtain ⟨herr1, hprog1⟩ := hsteps.err
  -- the `ret`
  have hj : R.fa.lines.toList[j0 + (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]? = some (Line.ins .ret none) := by
    have := congrArg (·[(spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl
    (by rw [hprog1, hst.prog]) hpc1 (by rw [herr1, hst.err])
  obtain ⟨a', ha', he'⟩ := exec_ret ⟨lineOffset R.fa.lines.toList (j0 + (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length), (R.lm[·]?)⟩ s1
  rw [ha] at ha'; cases ha'
  have hfin : iterN R.step ((spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length + 1) s = Arm.w .PC (xreg 30 s1) s1 := by
    rw [iterN_one_succ, hiter]; exact hstep.trans he'
  have hfplr := hst.fplr hframe
  rw [← hslot] at hfplr
  have hregs : ∀ r, r.allocatable = true → regVal (Arm.w .PC (xreg 30 s1) s1) r = regVal s r := by
    intro r hr
    rw [regVal_w (by rcases allocatable_cases hr with ⟨n, rfl, _⟩ | ⟨n, rfl, _⟩ <;> simp [Reg.field])]
    rcases allocatable_cases hr with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
    · have hne : ∀ q, q < 32 → q ≠ n → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 q) :=
        fun q h1 h2 e => rnum_ne (a := n) (b := q) (by omega) h1 (Ne.symm h2) (Arm.StateField.GPR.inj e)
      simp only [regVal]
      rw [ho1 _ (by simp) (hne 29 (by omega) (by omega)) (hne 30 (by omega) (by omega))
        (hne 31 (by omega) (by omega)) (hne 16 (by omega) (by omega))]
    · simp only [regVal]
      rw [ho1 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  refine ⟨(spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length + 1,
    fun i hi => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact RL.good_of_sp hst.sp
    · exact hgood i hi0 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hfin]
  · rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left, hent.lr]
  · rw [Arm.r_of_w_different (by simp), herr1, hst.err]
  · simp only [spv]
    rw [Arm.r_of_w_different (by simp)]
    show spOf s1 = spv R.s0
    rw [hsp1, hslot, BitVec.sub_add_cancel]
  · simp only [xreg]
    rw [Arm.r_of_w_different (by simp)]
    have := hx29
    simp only [xreg] at this
    rw [this, hfplr, BitVec.extractLsb'_append_eq_right]
    rfl
  · exact hregs
  · rw [Arm.ArmState.mem_w_eq_mem, hm1]
  · intro f hf h29 h31
    have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
    rw [Arm.r_of_w_different hpc]
    exact ho1 f hpc h29 (by rintro rfl; exact hf (by simp [Masked])) h31
      (by rintro rfl; exact hf (by simp [Masked]))
  · rw [Arm.w_program, hprog1]
  · intro ops' hops' j v p x hj hx
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_rets] at hops' hops
    cases hops'
    cases hops
    obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
    obtain ⟨rfl, q, hq, hq2⟩ := rets_uses (fun q hq r hr => (hloc q hq).2 r hr) hsz j v p x hj hx
    have hal : p.allocatable = true := by
      have := (hloc q hq).1
      rw [hq2] at this
      simp only [CheckCtx.locOk, Bool.and_eq_true] at this
      exact this.2
    rw [hregs p hal, hst.store (.reg p) (fun r e => by cases e; exact hal) trivial]
    rfl

end Backend.Proof
