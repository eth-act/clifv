import FV.Backend.Proof.RegallocTac
import FV.Backend.Proof.IselFamAluBBswap

/-!
# `Refines` for the covered forms (M6 proof)

On a covered form (`FormOk`) with an error-free world, `csem` is `straightSem`, the Arm run of
the canonical allocation. `ref_*`: for every `ispec` arm on such a form, that run gives the
`ispec` def values and control, and a world equal to `ispec`'s outside the masked registers.
`ss_tac` computes the canonical set-up (operands, canonical registers, placed uses), `csimp_rules`
the run; `ref_fin` matches the values (`BitVec` normalisation) and the worlds.
-/

namespace Backend.Proof

open Backend

theorem xzr_alloc : Reg.xzr.allocatable = false := by decide

/-- Unfold `straightSem` of a concrete form: operands, canonical registers, placed uses. -/
syntax "ss_tac" : tactic
macro_rules
  | `(tactic| ss_tac) => `(tactic| simp [straightSem, MInst.operands, MInst.visitOperands,
      MInst.assign, canonRegs, canonReg, canonBase, AccessOk, MInst.accesses, List.range_succ,
      OpSpec.def_, OpSpec.use, OpSpec.reuseDef, StateT.run, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, Except.bind, pure, StateT.pure,
      Except.pure, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, xzr_alloc])

theorem sw_up {n m k : Nat} (x : BitVec n) (h : n ≤ m) : (x.setWidth m).setWidth k = x.setWidth k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))]

theorem sw_down {n m k : Nat} (x : BitVec n) (h : k ≤ m) : (x.setWidth m).setWidth k = x.setWidth k :=
  BitVec.setWidth_setWidth_of_le x h

theorem amt32 (x : Nat) : (((x : Int).bmod 4294967296 % 32) % 64).toNat = x % 32 := by
  simp only [Int.bmod]; split <;> omega

theorem amt64 (x : Nat) : (((x : Int).bmod 18446744073709551616) % 64).toNat = x % 64 := by
  simp only [Int.bmod]; split <;> omega

theorem udiv_ite {n : Nat} (a b : BitVec n) : (if b = 0#n then 0#n else a / b) = a / b := by
  split <;> simp_all [BitVec.udiv_zero]

theorem sdiv_ite {n : Nat} (a b : BitVec n) : (if b = 0#n then 0#n else a.sdiv b) = a.sdiv b := by
  split <;> simp_all [BitVec.sdiv_zero]

theorem rot_mod32 (x : BitVec 32) (k : Nat) : x.rotateRight (k % 32) = x.rotateRight k := by
  rw [← BitVec.rotateRight_mod_eq_rotateRight (x := x) (r := k)]

theorem rot_mod64 (x : BitVec 64) (k : Nat) : x.rotateRight (k % 64) = x.rotateRight k := by
  rw [← BitVec.rotateRight_mod_eq_rotateRight (x := x) (r := k)]

theorem awc_sub {n : Nat} (x y : BitVec n) : (Arm.AddWithCarry x (~~~y) 1#1).fst = x - y := by
  rw [Arm.fst_AddWithCarry_eq_sub_neg, BitVec.not_not]

theorem imm12_enc {imm : Imm12} (h : imm.bits < 4096) :
    (if imm.shift12 = false then 0#52 ++ BitVec.ofNat 12 imm.bits
      else (0#52 ++ BitVec.ofNat 12 imm.bits) <<< 12) = BitVec.ofNat 64 imm.value := by
  obtain ⟨b, sh⟩ := imm
  have e : (0#52 ++ BitVec.ofNat 12 b).toNat = b % 4096 := by
    rw [BitVec.toNat_append]; simp
  cases sh <;> simp only [Imm12.value] at h ⊢ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_shiftLeft, e, Nat.shiftLeft_eq] <;> omega

theorem sw_ofNat {n k : Nat} (x : Nat) (h : k ≤ n) : (BitVec.ofNat n x).setWidth k = BitVec.ofNat k x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

theorem le_false {a b : Nat} (h : a < b) : (b ≤ a) = False := by
  simp only [eq_iff_iff, iff_false, Nat.not_le]; exact h

theorem se_le {n k : Nat} (x : BitVec n) (h : k ≤ n) : x.signExtend k = x.setWidth k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : i < n := by omega
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]; simp [hi, this]

theorem dsh_lsl : Arm.decode_shift ShiftOp.lsl.bits = .LSL := rfl
theorem dsh_lsr : Arm.decode_shift ShiftOp.lsr.bits = .LSR := rfl
theorem dsh_asr : Arm.decode_shift ShiftOp.asr.bits = .ASR := rfl
theorem dsh_ror : Arm.decode_shift ShiftOp.ror.bits = .ROR := rfl

theorem lsb5_of_lt {a : Nat} (h : a < 32) : Arm.BitVec.lsb (BitVec.ofNat 6 a) 5 = 0#1 := by
  apply BitVec.eq_of_toNat_eq
  simp [Arm.BitVec.lsb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
  omega

theorem and32_of_lt {a : Nat} (h : a < 32) : BitVec.ofNat 6 a &&& 32#6 = 0#6 :=
  (by decide : ∀ a < 32, BitVec.ofNat 6 a &&& 32#6 = 0#6) a h

theorem mod64_of_lt32 {a : Nat} (h : a < 32) : a % 64 = a := Nat.mod_eq_of_lt (by omega)

theorem mod_of_lt' {a b : Nat} (h : a < b) : a % b = a := Nat.mod_eq_of_lt h

theorem rv16 (x : BitVec 32) (h0 h1 h2 h3 h4) : Arm.rev_vector 32 16 8 x h0 h1 h2 h3 h4 = rev16w x := by
  simp [Arm.rev_vector, Arm.rev_elems, rev16w]
  bv_decide
theorem rv32 (x : BitVec 32) (h0 h1 h2 h3 h4) : Arm.rev_vector 32 32 8 x h0 h1 h2 h3 h4 = Clif.Sem.bswap x := by
  simp [Arm.rev_vector, Arm.rev_elems, bswap_32]
  bv_decide
theorem rv64 (x : BitVec 64) (h0 h1 h2 h3 h4) : Arm.rev_vector 64 64 8 x h0 h1 h2 h3 h4 = Clif.Sem.bswap x := by
  simp [Arm.rev_vector, Arm.rev_elems, bswap_64]
  bv_decide

theorem nzcv_n (f : NZCV) : Arm.BitVec.lsb (BitVec.ofNat 4 f.bits) 3 = BitVec.ofBool f.n := by
  obtain ⟨n, z, c, v⟩ := f; cases n <;> cases z <;> cases c <;> cases v <;> rfl
theorem nzcv_z (f : NZCV) : Arm.BitVec.lsb (BitVec.ofNat 4 f.bits) 2 = BitVec.ofBool f.z := by
  obtain ⟨n, z, c, v⟩ := f; cases n <;> cases z <;> cases c <;> cases v <;> rfl
theorem nzcv_c (f : NZCV) : Arm.BitVec.lsb (BitVec.ofNat 4 f.bits) 1 = BitVec.ofBool f.c := by
  obtain ⟨n, z, c, v⟩ := f; cases n <;> cases z <;> cases c <;> cases v <;> rfl
theorem nzcv_v (f : NZCV) : Arm.BitVec.lsb (BitVec.ofNat 4 f.bits) 0 = BitVec.ofBool f.v := by
  obtain ⟨n, z, c, v⟩ := f; cases n <;> cases z <;> cases c <;> cases v <;> rfl

theorem ofNat_sw16 {n bits : Nat} (hn : 16 < n) (h : bits < 65536) :
    BitVec.ofNat n bits = (BitVec.ofNat 16 bits).setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : bits < 2 ^ 16), Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le h (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hn))

theorem ext0 {n : Nat} (k : Nat) (x : BitVec n) : x.extractLsb' 0 k = x.setWidth k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem dre_uxtb : Arm.decode_reg_extend ExtendOp.uxtb.bits = .UXTB := rfl
theorem dre_uxth : Arm.decode_reg_extend ExtendOp.uxth.bits = .UXTH := rfl
theorem dre_uxtw : Arm.decode_reg_extend ExtendOp.uxtw.bits = .UXTW := rfl
theorem dre_uxtx : Arm.decode_reg_extend ExtendOp.uxtx.bits = .UXTX := rfl
theorem dre_sxtb : Arm.decode_reg_extend ExtendOp.sxtb.bits = .SXTB := rfl
theorem dre_sxth : Arm.decode_reg_extend ExtendOp.sxth.bits = .SXTH := rfl
theorem dre_sxtw : Arm.decode_reg_extend ExtendOp.sxtw.bits = .SXTW := rfl
theorem dre_sxtx : Arm.decode_reg_extend ExtendOp.sxtx.bits = .SXTX := rfl

/-- Close a `SameWorld F w'' w'` goal: peel the writes of the canonical run. -/
syntax "sw_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sw_fin) => `(tactic| (
    try simp only [Arm.write_pstate, opnd, lo64]
    try dsimp only [OperandSize.bits]
    repeat (first
        | exact SameWorld.refl F _
        | (refine SameWorld.w_both' ?_ ?_
           · first
               | rfl
               | (simp (disch := decide) [sw_up, sw_down, Arm.extend_reg, Arm.ExtendType.unsigned_len, dre_uxtb, dre_uxth, dre_uxtw, dre_uxtx, dre_sxtb,
      dre_sxth, dre_sxtw, dre_sxtx, ext0, Nat.min_def, se_le]; done)
               | (simp (disch := decide) [sw_up, sw_down, Arm.extend_reg, Arm.ExtendType.unsigned_len, dre_uxtb, dre_uxth, dre_uxtw, dre_uxtx, dre_sxtb,
      dre_sxth, dre_sxtw, dre_sxtx, ext0, Nat.min_def, se_le]; rfl))
        | (refine SameWorld.w_left ?_ ?_; · simp [Masked]))
    done))

/-- Close a def-values goal (`BitVec` normalisation). -/
syntax "val_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| val_fin) => `(tactic| (
    try simp only [defOut, resX, opnd, lo64, ofX, List.cons.injEq, and_true]
    all_goals try dsimp only [OperandSize.bits]
    all_goals simp (disch := decide) [Arm.fst_AddWithCarry_eq_add, awc_sub, sw_up,
      sw_down, BitVec.not_not, amt32, amt64, udiv_ite, sdiv_ite, rot_mod32, rot_mod64, mod64_of_lt32, mod_of_lt', rv16, rv32, rv64, *,
      Arm.extend_reg, Arm.ExtendType.unsigned_len, dre_uxtb, dre_uxth, dre_uxtw, dre_uxtx, dre_sxtb,
      dre_sxth, dre_sxtw, dre_sxtx, ext0, Nat.min_def, se_le]
    all_goals first
      | rfl
      | (apply BitVec.eq_of_getLsbD_eq; intro i hi; simp)))

syntax "ref_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ref_fin) => `(tactic| (
    first
      | refine ⟨_, ⟨?_, rfl, rfl⟩, ?_⟩
      | refine ⟨_, ⟨?_, rfl⟩, ?_⟩
      | refine ⟨_, ⟨rfl, rfl⟩, ?_⟩
      | refine ⟨_, rfl, ?_⟩
      | refine ⟨_, ⟨?_, rfl, ?_⟩, ?_⟩
      | skip
    all_goals (first | with_reducible rfl | sw_fin | val_fin)))


/-- The statement of a per-form `Refines` lemma. -/
def RefAt (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (us : List CV) : Prop :=
  ∀ (w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState) (ctl : Ctl),
    Arm.r .ERR w = .None → ispec i us w = some (outs, w', ctl) →
    ∃ w'', straightSem F ctx i us w = some (outs, w'', ctl) ∧ SameWorld F w'' w'

/-- The per-form proof after the intros: canonical set-up, both sides computed, matched. -/
syntax "ref_body" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ref_body) => `(tactic| (
    ss_tac
    all_goals (simp (config := {decide := true}) [ispec, rrrVal, aluVal, shiftVal, mulAddVal,
      aluShiftable, extendVal, movWideVal, movKVal, *] at h)
    all_goals (try simp only [awc_sub, Arm.fst_AddWithCarry_eq_add] at h)
    all_goals (try dsimp only [OperandSize.bits, opnd, lo64] at h)
    all_goals (revert h; try simp only [and_imp])
    all_goals intros
    all_goals subst_vars
    all_goals (try (exfalso; omega))
    all_goals (simp (config := {decide := true}) [csimp_rules, he, Arm.w_program, imm12_enc,
      sw_ofNat, le_false, ↓dsh_lsl, ↓dsh_lsr, ↓dsh_asr, ↓dsh_ror, lsb5_of_lt, and32_of_lt,
      mod64_of_lt32, mod_of_lt', nzcv_n, nzcv_z, nzcv_c, nzcv_v, Arm.reduceDecodeBitMasks, *])
    all_goals ref_fin))

/-- The per-form proof. -/
syntax "ref_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ref_tac) => `(tactic| (
    intro w outs w' ctl he h
    ref_body))

/-- The per-form proof of a form reading the flags: split the four flags of the world first. -/
syntax "ref_tac_fl" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ref_tac_fl) => `(tactic| (
    intro w outs w' ctl he h
    rcases bv1_cases (Arm.r (.FLAG .N) w) with hN | hN <;>
    rcases bv1_cases (Arm.r (.FLAG .Z) w) with hZ | hZ <;>
    rcases bv1_cases (Arm.r (.FLAG .C) w) with hC | hC <;>
    rcases bv1_cases (Arm.r (.FLAG .V) w) with hV | hV <;>
    ref_body))

variable (F : BitVec 64 → Prop) (ctx : FnCtx)

set_option maxHeartbeats 4000000 in
theorem ref_aluRRR (op : ALUOp) (sz : OperandSize) (d n m : Nat) (a b : CV) :
    RefAt F ctx (.aluRRR op sz (.vreg d .int) (.vreg n .int) (.vreg m .int)) [a, b] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRR_xn (op : ALUOp) (sz : OperandSize) (d m : Nat) (b : CV) :
    RefAt F ctx (.aluRRR op sz (.vreg d .int) .xzr (.vreg m .int)) [b] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRImm12 (op : ALUOp) (sz : OperandSize) (d n : Nat) (imm : Imm12) (a : CV) :
    RefAt F ctx (.aluRRImm12 op sz (.vreg d .int) (.vreg n .int) imm) [a] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRR_xd (op : ALUOp) (sz : OperandSize) (n m : Nat) (a b : CV) :
    RefAt F ctx (.aluRRR op sz .xzr (.vreg n .int) (.vreg m .int)) [a, b] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRR_xm (op : ALUOp) (sz : OperandSize) (d n : Nat) (a : CV) :
    RefAt F ctx (.aluRRR op sz (.vreg d .int) (.vreg n .int) .xzr) [a] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRR_xdm (op : ALUOp) (sz : OperandSize) (n : Nat) (a : CV) :
    RefAt F ctx (.aluRRR op sz .xzr (.vreg n .int) .xzr) [a] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRRR (op : ALUOp3) (sz : OperandSize) (d n m k : Nat) (a b c : CV) :
    RefAt F ctx (.aluRRRR op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) (.vreg k .int)) [a, b, c] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRRR_xa (op : ALUOp3) (sz : OperandSize) (d n m : Nat) (a b : CV) :
    RefAt F ctx (.aluRRRR op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) .xzr) [a, b] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRRShift (op : ALUOp) (sz : OperandSize) (d n m : Nat) (sh : ShiftOpAndAmt) (a b : CV) :
    RefAt F ctx (.aluRRRShift op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) sh) [a, b] := by
  obtain ⟨so, amt⟩ := sh
  cases op <;> cases sz <;> cases so <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRRExtend (op : ALUOp) (sz : OperandSize) (d n m : Nat) (e : ExtendOp) (a b : CV) :
    RefAt F ctx (.aluRRRExtend op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) e) [a, b] := by
  cases op <;> cases sz <;> cases e <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_bitRR (op : BitOp) (sz : OperandSize) (d n : Nat) (a : CV) :
    RefAt F ctx (.bitRR op sz (.vreg d .int) (.vreg n .int)) [a] := by
  cases op <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_cset (d : Nat) (c : Cond) :
    RefAt F ctx (.cset (.vreg d .int) c) [] := by
  cases c <;> ref_tac_fl

set_option maxHeartbeats 4000000 in
theorem ref_csel (d n m : Nat) (c : Cond) (a b : CV) :
    RefAt F ctx (.csel (.vreg d .int) (.vreg n .int) (.vreg m .int) c) [a, b] := by
  cases c <;> ref_tac_fl

set_option maxHeartbeats 4000000 in
theorem ref_movK (d n : Nat) (imm : MoveWideConst) (sz : OperandSize) (a : CV) :
    RefAt F ctx (.movK (.vreg d .int) (.vreg n .int) imm sz) [a] := by
  obtain ⟨bits, sh⟩ := imm
  rcases sh with _ | _ | _ | _ | sh <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_ccmpImm (sz : OperandSize) (n : Nat) (imm : Nat) (nzcv : NZCV) (c : Cond) (a : CV) :
    RefAt F ctx (.ccmpImm sz (.vreg n .int) imm nzcv c) [a] := by
  cases sz <;> cases c <;> ref_tac_fl

set_option maxHeartbeats 4000000 in
theorem ref_movWide (d : Nat) (imm : MoveWideConst) (sz : OperandSize) :
    RefAt F ctx (.movWide .movZ (.vreg d .int) imm sz) [] := by
  obtain ⟨bits, sh⟩ := imm
  rcases sh with _ | _ | _ | _ | sh <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRImm12_xd (op : ALUOp) (sz : OperandSize) (n : Nat) (imm : Imm12) (a : CV)
    (hop : (op == .subS || op == .addS) = true) :
    RefAt F ctx (.aluRRImm12 op sz .xzr (.vreg n .int) imm) [a] := by
  cases op <;> simp at hop <;> cases sz <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRRExtend_xd (op : ALUOp) (sz : OperandSize) (n m : Nat) (e : ExtendOp) (a b : CV)
    (hop : (op == .subS || op == .addS) = true) :
    RefAt F ctx (.aluRRRExtend op sz .xzr (.vreg n .int) (.vreg m .int) e) [a, b] := by
  cases op <;> simp at hop <;> cases sz <;> cases e <;> ref_tac

end Backend.Proof
