import FV.Backend.Proof.RegallocInstsInt
import FV.Backend.Proof.RegallocInstsZR
import FV.Backend.Proof.RegallocInstsFP

/-!
# `OperandsSound` for every straight-line instruction form (M6 proof)

`os_of_corr` applied to the `Corr` theorems of `RegallocInstsInt.lean` (integer forms),
`RegallocInstsZR.lean` (zero-register operands) and `RegallocInstsFP.lean` (float/vector).
-/

namespace Backend.Proof

open Backend

/-! ## `OperandsSound` -/

/-- `MInst.assign` of a form with `k` vreg operands, by destructuring the allocation. -/
syntax "assign_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| assign_tac) => `(tactic| (intro regs h; first
    | (obtain ⟨_, _, _, _, rfl⟩ := regs4 (by simpa using h); rfl)
    | (obtain ⟨_, _, _, rfl⟩ := regs3 (by simpa using h); rfl)
    | (obtain ⟨_, _, rfl⟩ := regs2 (by simpa using h); rfl)
    | (obtain ⟨_, rfl⟩ := regs1 (by simpa using h); rfl)))

variable (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem)

theorem os_aluRRR (op : ALUOp) (sz : OperandSize) (d n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRR op sz (.vreg d .int) (.vreg n .int) (.vreg m .int)) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRR F ctx env op sz d n m)

theorem os_aluRRRR (op : ALUOp3) (sz : OperandSize) (d n m a : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRRR op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) (.vreg a .int)) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRRR F ctx env op sz d n m a)

theorem os_aluRRImm12 (op : ALUOp) (sz : OperandSize) (d n : Nat) (imm : Imm12) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRImm12 op sz (.vreg d .int) (.vreg n .int) imm) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRImm12 F ctx env op sz d n imm)

theorem os_aluRRImmLogic (op : ALUOp) (hop : logicOpOk op = true) (sz : OperandSize) (d n : Nat)
    (imm : ImmLogic) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRImmLogic op sz (.vreg d .int) (.vreg n .int) imm) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRImmLogic F ctx env op sz d n imm)

theorem os_aluRRImmShift (op : ALUOp) (hop : shiftOpOk op = true) (sz : OperandSize) (d n amt : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRImmShift op sz (.vreg d .int) (.vreg n .int) amt) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRImmShift F ctx env op sz d n amt)

theorem os_aluRRRShift (op : ALUOp) (sz : OperandSize) (d n m : Nat) (sh : ShiftOpAndAmt) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRRShift op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) sh) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRRShift F ctx env op sz d n m sh)

theorem os_aluRRRExtend (op : ALUOp) (sz : OperandSize) (d n m : Nat) (e : ExtendOp) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRRExtend op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) e) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRRExtend F ctx env op sz d n m e)

theorem os_bitRR (op : BitOp) (sz : OperandSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.bitRR op sz (.vreg d .int) (.vreg n .int)) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_bitRR F ctx env op sz d n)

theorem os_mov (sz : OperandSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.mov sz (.vreg d .int) (.vreg n .int)) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_mov F ctx env sz d n)

theorem os_movWide (op : MoveWideOp) (imm : MoveWideConst) (sz : OperandSize) (d : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.movWide op (.vreg d .int) imm sz) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_movWide F ctx env op imm sz d)

theorem os_movK (imm : MoveWideConst) (sz : OperandSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.movK (.vreg d .int) (.vreg n .int) imm sz) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_movK F ctx env imm sz n d)

theorem os_extend (signed : Bool) (fromBits toBits d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.extend (.vreg d .int) (.vreg n .int) signed fromBits toBits) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_extend F ctx env signed fromBits toBits d n)

theorem os_bitfieldMove (sz : OperandSize) (op : BfmOp) (d n immr imms : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.bitfieldMove sz op (.vreg d .int) (.vreg n .int) immr imms) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_bitfieldMove F ctx env sz op d n immr imms)

theorem os_cset (c : Cond) (d : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.cset (.vreg d .int) c) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_cset F ctx env c d)

theorem os_csel (c : Cond) (d n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.csel (.vreg d .int) (.vreg n .int) (.vreg m .int) c) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_csel F ctx env c d n m)

theorem os_ccmp (sz : OperandSize) (nzcv : NZCV) (c : Cond) (n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.ccmp sz (.vreg n .int) (.vreg m .int) nzcv c) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_ccmp F ctx env sz nzcv c n m)

theorem os_ccmpImm (sz : OperandSize) (imm : Nat) (nzcv : NZCV) (c : Cond) (n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.ccmpImm sz (.vreg n .int) imm nzcv c) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_ccmpImm F ctx env sz imm nzcv c n)


theorem os_aluRRR_rnZ (op : ALUOp) (sz : OperandSize) (d m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.aluRRR op sz (.vreg d .int) .xzr (.vreg m .int)) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRR_rnZ F ctx env op sz d m)

theorem os_aluRRR_rdZ (op : ALUOp) (sz : OperandSize) (n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.aluRRR op sz .xzr (.vreg n .int) (.vreg m .int)) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRR_rdZ F ctx env op sz n m)

theorem os_aluRRImm12_rdZ (op : ALUOp) (sz : OperandSize) (n : Nat) (imm : Imm12) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.aluRRImm12 op sz .xzr (.vreg n .int) imm) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRImm12_rdZ F ctx env op sz n imm)

theorem os_aluRRImmLogic_rdZ (op : ALUOp) (hop : logicOpOk op = true) (sz : OperandSize) (n : Nat)
    (imm : ImmLogic) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.aluRRImmLogic op sz .xzr (.vreg n .int) imm) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRImmLogic_rdZ F ctx env op sz n imm)

theorem os_aluRRRShift_rdZ (op : ALUOp) (sz : OperandSize) (n m : Nat) (sh : ShiftOpAndAmt) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRRShift op sz .xzr (.vreg n .int) (.vreg m .int) sh) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRRShift_rdZ F ctx env op sz n m sh)

theorem os_aluRRRShift_rnZ (op : ALUOp) (sz : OperandSize) (d m : Nat) (sh : ShiftOpAndAmt) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRRShift op sz (.vreg d .int) .xzr (.vreg m .int) sh) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRRShift_rnZ F ctx env op sz d m sh)

theorem os_aluRRRExtend_rdZ (op : ALUOp) (sz : OperandSize) (n m : Nat) (e : ExtendOp) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRRExtend op sz .xzr (.vreg n .int) (.vreg m .int) e) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRRExtend_rdZ F ctx env op sz n m e)

theorem os_aluRRRR_raZ (op : ALUOp3) (sz : OperandSize) (d n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRRR op sz (.vreg d .int) (.vreg n .int) (.vreg m .int) .xzr) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRRR_raZ F ctx env op sz d n m)

theorem os_aluRRR_rmZ (op : ALUOp) (sz : OperandSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.aluRRR op sz (.vreg d .int) (.vreg n .int) .xzr) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRR_rmZ F ctx env op sz d n)

theorem os_aluRRR_rdZ_rmZ (op : ALUOp) (sz : OperandSize) (n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.aluRRR op sz .xzr (.vreg n .int) .xzr) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_aluRRR_rdZ_rmZ F ctx env op sz n)

theorem os_movToFpu (sz : ScalarSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.movToFpu (.vreg d .float) (.vreg n .int) sz) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_movToFpu F ctx env sz d n)

theorem os_movFromVec (idx : Nat) (sz : ScalarSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.movFromVec (.vreg d .int) (.vreg n .float) idx sz) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_movFromVec F ctx env idx sz d n)

theorem os_vecMisc (op : VecMisc2) (sz : VectorSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.vecMisc op (.vreg d .float) (.vreg n .float) sz) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_vecMisc F ctx env op sz d n)

theorem os_vecLanes (op : VecLanesOp) (sz : VectorSize) (d n : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.vecLanes op (.vreg d .float) (.vreg n .float) sz) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_vecLanes F ctx env op sz d n)

theorem os_vecRRR (op : VecALUOp) (sz : VectorSize) (d n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.vecRRR op (.vreg d .float) (.vreg n .float) (.vreg m .float) sz) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_vecRRR F ctx env op sz d n m)

end Backend.Proof
