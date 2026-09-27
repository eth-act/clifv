import FV.Backend.Proof.IselRulesALU

/-!
# Term contracts for family A (binary ALU with operand look-through)

The instruction-emitting helpers of `inst.isle` the family's rules call (`alu_rr_imm12`,
`alu_rrr_shift`, `alu_rrr_extend`, `alu_rrrr`, `alu_rr_imm_logic`, `alu_rr_imm_shift` and their
wrappers `add_imm`, `sub_imm`, `add_shift`, …), each evaluated once for every fuel above a
bound and any lowering state, generic in the ALU operation (`ALUOp.ofIdx?`) and the operand
size (`operand_size_run`). Rule proofs use them as rewrite rules (`isel_eval [*, …]`).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

/-! ## `MInst.ofV` and `emit`, generic in the operation and size -/

section Emit
variable (ctx : Ctx) (st : LState)

theorem ofV_aluRRImm12 {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (rd rn : Reg)
    (i : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.imm12 i)]) =
      some (.aluRRImm12 op sz rd rn i) := by
  have e1 : MInst.ofV (.data 58 4 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.imm12 i)]) =
      (do return .aluRRImm12 (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn i) := rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_aluRRImmLogic {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (rd rn : Reg)
    (i : ImmLogic) :
    MInst.ofV (.data 58 5 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.immLogic i)]) =
      some (.aluRRImmLogic op sz rd rn i) := by
  have e1 : MInst.ofV (.data 58 5 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.immLogic i)]) =
      (do return .aluRRImmLogic (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn i) := rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_aluRRImmShift {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (rd rn : Reg)
    (i : Nat) :
    MInst.ofV (.data 58 6 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.immShift i)]) =
      some (.aluRRImmShift op sz rd rn i) := by
  have e1 : MInst.ofV (.data 58 6 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.immShift i)]) =
      (do return .aluRRImmShift (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn i) := rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_aluRRRShift {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (rd rn rm : Reg)
    (sh : ShiftOpAndAmt) :
    MInst.ofV (.data 58 7 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm,
      .op (.shiftOpAndAmt sh)]) = some (.aluRRRShift op sz rd rn rm sh) := by
  have e1 : MInst.ofV (.data 58 7 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm,
      .op (.shiftOpAndAmt sh)]) =
      (do return .aluRRRShift (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn rm sh) :=
    rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_aluRRRExtend {k ks ke : Nat} {op : ALUOp} {sz : OperandSize} {e : ExtendOp}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz)
    (he : ExtendOp.ofIdx? ke = some e) (rd rn rm : Reg) :
    MInst.ofV (.data 58 8 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm,
      .data 84 ke []]) = some (.aluRRRExtend op sz rd rn rm e) := by
  have e1 : MInst.ofV (.data 58 8 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm,
      .data 84 ke []]) =
      (do
        let o ← (V.data 59 k []).aluOp?
        let s ← (V.data 93 ks []).size?
        let x ← (V.data 84 ke []).extendOp?
        return .aluRRRExtend o s rd rn rm x) := rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  have e4 : (V.data 84 ke []).extendOp? = ExtendOp.ofIdx? ke := rfl
  rw [e1, e2, e3, e4, hk, hs, he]
  rfl

theorem ofV_aluRRRR {k ks : Nat} {op : ALUOp3} {sz : OperandSize}
    (hk : ALUOp3.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (rd rn rm ra : Reg) :
    MInst.ofV (.data 58 3 [.data 60 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm, .reg ra]) =
      some (.aluRRRR op sz rd rn rm ra) := by
  have e1 : MInst.ofV (.data 58 3 [.data 60 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm, .reg ra]) =
      (do return .aluRRRR (← (V.data 60 k []).aluOp3?) (← (V.data 93 ks []).size?) rd rn rm ra) :=
    rfl
  have e2 : (V.data 60 k []).aluOp3? = ALUOp3.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

end Emit

/-! ## `operand_size` at every width -/

section
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- `operand_size` at an integer type of width `w ≤ 64`: the size index of `szOf w`. -/
theorem operand_size_run {w : Nat} (hw : w ≤ 64) :
    ∃ ks rid, OperandSize.ofIdx? ks = some (szOf w) ∧
      ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
        .ok (some (.data 93 ks []), (st, tr.push rid)) := by
  by_cases h32 : w ≤ 32
  · exact ⟨0, _, by simp [szOf, h32]; rfl, fun st tr n => operand_size_32 hp ctx hc st tr n h32⟩
  · exact ⟨1, _, by simp [szOf, h32]; rfl,
      fun st tr n => operand_size_64 hp ctx hc st tr n (by omega) hw⟩

/-! ## The emitting helpers -/

variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem alu_rr_imm12_run {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) (i : Imm12) :
    (applyTerm p (sem ctx) cfg (n+20) 27 376 [.data 59 k [], .ty (.int w), .reg a, .op (.imm12 i)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImm12 op sz (st.fresh .int).1 a i),
          (tr.push rid).push rule_inst_2648.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_aluRRImm12 hk hs rd rn i)
  cases hp
  isel_eval [*, rule_inst_2648, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `add_imm` (`(alu_rr_imm12 (ALUOp.Add) ty x y)`) and `sub_imm` (`ALUOp.Sub`). -/
theorem add_imm_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) (i : Imm12) :
    (applyTerm p (sem ctx) cfg (n+30) 27 433 [.ty (.int w), .reg a, .op (.imm12 i)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImm12 .add sz (st.fresh .int).1 a i),
          ((tr.push rid).push rule_inst_2648.id).push rule_inst_3122.id)) := by
  have h := fun st tr n => alu_rr_imm12_run hp ctx hc st tr n hsz (k := 0) rfl hs
  cases hp
  isel_eval [*, rule_inst_3122]

include hp hc in
theorem sub_imm_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) (i : Imm12) :
    (applyTerm p (sem ctx) cfg (n+30) 27 438 [.ty (.int w), .reg a, .op (.imm12 i)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImm12 .sub sz (st.fresh .int).1 a i),
          ((tr.push rid).push rule_inst_2648.id).push rule_inst_3142.id)) := by
  have h := fun st tr n => alu_rr_imm12_run hp ctx hc st tr n hsz (k := 1) rfl hs
  cases hp
  isel_eval [*, rule_inst_3142]

end

end Backend.Proof
