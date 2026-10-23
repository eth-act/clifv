import FV.Backend.Proof.RegallocSlots
import FV.Backend.Proof.RegallocMem
import FV.Backend.Proof.IselCtlTerm

/-!
# The callee-save pushes and pops on the machine (#549, #479)

Cranelift's `gen_clobber_save`/`gen_clobber_restore` (`prologueLines`/`epilogueLines`): the
saved registers are pushed below fp/lr with pre-indexed `str`/`stp` (`str d`/`stp d` for
v8–v15) and popped with post-indexed `ldr`/`ldp`. `pushLines_ok`: the pushes of one register
class lower `sp` by `pushBytes`, write only below the old `sp`, and leave register `rs[i]`'s
low 64 bits at `sp_new + 8 i`; `popLines_ok`: the pops read them back (the upper half of a
`v` register cleared) and raise `sp` by `pushBytes`.
-/

open Backend

namespace Backend.Proof

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

end Backend.Proof
