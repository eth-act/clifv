import FV.Backend.Proof.IselExtern

/-!
# Contracts of internal ISLE terms (per-term lemmas)

Each lemma evaluates one internal constructor term on the argument shapes the probe's rules
pass, for every fuel above a bound, from any lowering state: its result value, the
instructions it appends to `LState.emitted`, the fresh vregs it allocates and the rules it
fires. Rule proofs use them as rewrite rules instead of re-evaluating the callee, so a term is
evaluated once however many rules call it (the M4 closure's shared helpers — `operand_size`,
`alu_rrr`, `with_flags`, `put_in_reg_zext32`, … — are exactly these).

All statements quantify over an abstract program `p` with `Data p` (see `IselData`).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## `emit` of the instruction values the rules build -/

section Emit
variable (st : LState) (rd rn rm : Reg)

theorem emit_add_32 : externCtor ctx T.emit
    [.data 58 2 [.data 59 0 [], .data 93 0 [], .reg rd, .reg rn, .reg rm]] st =
    .ok (.op .unit, st.emit (.aluRRR .add .size32 rd rn rm)) := ctor_emit _ _ (ofV_aluRRR_add_32 ..)
theorem emit_add_64 : externCtor ctx T.emit
    [.data 58 2 [.data 59 0 [], .data 93 1 [], .reg rd, .reg rn, .reg rm]] st =
    .ok (.op .unit, st.emit (.aluRRR .add .size64 rd rn rm)) := ctor_emit _ _ (ofV_aluRRR_add_64 ..)
theorem emit_subs_32 : externCtor ctx T.emit
    [.data 58 2 [.data 59 10 [], .data 93 0 [], .reg rd, .reg rn, .reg rm]] st =
    .ok (.op .unit, st.emit (.aluRRR .subS .size32 rd rn rm)) := ctor_emit _ _ (ofV_aluRRR_subs_32 ..)
theorem emit_subs_64 : externCtor ctx T.emit
    [.data 58 2 [.data 59 10 [], .data 93 1 [], .reg rd, .reg rn, .reg rm]] st =
    .ok (.op .unit, st.emit (.aluRRR .subS .size64 rd rn rm)) := ctor_emit _ _ (ofV_aluRRR_subs_64 ..)
theorem emit_lsr_32 : externCtor ctx T.emit
    [.data 58 2 [.data 59 16 [], .data 93 0 [], .reg rd, .reg rn, .reg rm]] st =
    .ok (.op .unit, st.emit (.aluRRR .lsr .size32 rd rn rm)) := ctor_emit _ _ (ofV_aluRRR_lsr_32 ..)
theorem emit_addi_32 (i : Imm12) : externCtor ctx T.emit
    [.data 58 4 [.data 59 0 [], .data 93 0 [], .reg rd, .reg rn, .op (.imm12 i)]] st =
    .ok (.op .unit, st.emit (.aluRRImm12 .add .size32 rd rn i)) :=
  ctor_emit _ _ (ofV_aluRRImm12_add_32 ..)
theorem emit_addi_64 (i : Imm12) : externCtor ctx T.emit
    [.data 58 4 [.data 59 0 [], .data 93 1 [], .reg rd, .reg rn, .op (.imm12 i)]] st =
    .ok (.op .unit, st.emit (.aluRRImm12 .add .size64 rd rn i)) :=
  ctor_emit _ _ (ofV_aluRRImm12_add_64 ..)
theorem emit_andi_32 (i : ImmLogic) : externCtor ctx T.emit
    [.data 58 5 [.data 59 4 [], .data 93 0 [], .reg rd, .reg rn, .op (.immLogic i)]] st =
    .ok (.op .unit, st.emit (.aluRRImmLogic .and .size32 rd rn i)) :=
  ctor_emit _ _ (ofV_aluRRImmLogic_and_32 ..)
theorem emit_uxt8_32 : externCtor ctx T.emit
    [.data 58 28 [.reg rd, .reg rn, .bool false, .int 8, .int 32]] st =
    .ok (.op .unit, st.emit (.extend rd rn false 8 32)) := ctor_emit _ _ (ofV_extend_u8_32 ..)
theorem emit_cset (c : Cond) : externCtor ctx T.emit
    [.data 58 33 [.reg rd, .data tyCond c.idx []]] st =
    .ok (.op .unit, st.emit (.cset rd c)) := ctor_emit _ _ (ofV_cset ..)

end Emit

/-! ## `operand_size` -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem operand_size_32 {w : Nat} (hw : w ≤ 32) :
    (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 0 []), (st, tr.push rule_inst_1592.id)) := by
  cases hp
  isel_eval [*, ext_fits_in_32, rule_inst_1592, rule_inst_1593]

include hp hc in
theorem operand_size_64 {w : Nat} (hw : 32 < w) (hw' : w ≤ 64) :
    (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 1 []), (st, tr.push rule_inst_1593.id)) := by
  have : ¬ w ≤ 32 := by omega
  cases hp
  isel_eval [*, ext_fits_in_32, ext_fits_in_64, rule_inst_1592, rule_inst_1593]

end

/-! ## `alu_rrr` and its callers

Generic in the ALU operation and the operand size: the caller supplies the evaluation of
`operand_size` at the type (`hsz`) and of `emit` on the instruction value (`hemit`). -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem alu_rrr_run {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hemit : ∀ st rd rn rm, externCtor ctx T.emit
      [.data 58 2 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm]] st =
      .ok (.op .unit, st.emit (.aluRRR op sz rd rn rm)))
    (a b : Reg) :
    (applyTerm p (sem ctx) cfg (n+20) 27 362 [.data 59 k [], .ty (.int w), .reg a, .reg b]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR op sz (st.fresh .int).1 a b),
          (tr.push rid).push rule_inst_2545.id)) := by
  cases hp
  isel_eval [*, rule_inst_2545, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `add` (`inst.isle`: `(rule (add ty x y) (alu_rrr (ALUOp.Add) ty x y))`). -/
theorem add_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hemit : ∀ st rd rn rm, externCtor ctx T.emit
      [.data 58 2 [.data 59 0 [], .data 93 ks [], .reg rd, .reg rn, .reg rm]] st =
      .ok (.op .unit, st.emit (.aluRRR .add sz rd rn rm)))
    (a b : Reg) :
    (applyTerm p (sem ctx) cfg (n+30) 27 432 [.ty (.int w), .reg a, .reg b]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR .add sz (st.fresh .int).1 a b),
          ((tr.push rid).push rule_inst_2545.id).push rule_inst_3118.id)) := by
  have h := fun st tr n => alu_rrr_run hp ctx hc st tr n hsz hemit
  cases hp
  isel_eval [*, rule_inst_3118]

include hp hc in
/-- `output_reg` (`prelude_lower.isle`: `(output (value_reg reg))`). -/
theorem output_reg_run (r : Reg) :
    (applyTerm p (sem ctx) cfg (n+10) 25 172 [.reg r]).run (st, tr) =
      .ok (some (.regsVec [[r]]), (st, tr.push rule_prelude_lower_105.id)) := by
  cases hp
  isel_eval [*, rule_prelude_lower_105, ctor_value_reg, ctor_output]

end

end Backend.Proof
