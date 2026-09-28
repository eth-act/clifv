import FV.Backend.Proof.RegallocTac

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
               | (simp (disch := decide) [sw_up, sw_down]; done)
               | (simp (disch := decide) [sw_up, sw_down]; rfl))
        | (refine SameWorld.w_left ?_ ?_; · simp [Masked]))
    done))

/-- Close a def-values goal (`BitVec` normalisation). -/
syntax "val_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| val_fin) => `(tactic| (
    try simp only [defOut, resX, opnd, lo64, ofX, List.cons.injEq, and_true]
    try dsimp only [OperandSize.bits]
    simp (disch := decide) [Arm.fst_AddWithCarry_eq_add, awc_sub, sw_up,
      sw_down, BitVec.not_not, amt32, amt64, udiv_ite, sdiv_ite, rot_mod32, rot_mod64]
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
    all_goals (first | sw_fin | val_fin)))


/-- The statement of a per-form `Refines` lemma. -/
def RefAt (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (us : List CV) : Prop :=
  ∀ (w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState) (ctl : Ctl),
    Arm.r .ERR w = .None → ispec i us w = some (outs, w', ctl) →
    ∃ w'', straightSem F ctx i us w = some (outs, w'', ctl) ∧ SameWorld F w'' w'

/-- The per-form proof: canonical set-up, cases, both sides computed, matched. -/
syntax "ref_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ref_tac) => `(tactic| (
    intro w outs w' ctl he h
    ss_tac
    all_goals (simp (config := {decide := true}) [ispec, rrrVal, aluVal, shiftVal, mulAddVal,
      aluShiftable, extendVal, movWideVal, movKVal] at h)
    all_goals (try simp only [awc_sub, Arm.fst_AddWithCarry_eq_add] at h)
    all_goals (try dsimp only [OperandSize.bits, opnd, lo64] at h)
    all_goals (revert h; (try simp only [and_imp]); intros; subst_vars)
    all_goals (simp (config := {decide := true}) [csimp_rules, he, Arm.w_program, imm12_enc,
      sw_ofNat, *])
    all_goals ref_fin))

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

end Backend.Proof
