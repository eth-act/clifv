import FV.Backend.Proof.IselRules

/-!
# Forward interpreter lemmas for the two-register ALU root rules

For each rule of the family: the match phase on the instruction (`match_*`), the right-hand
side from the environment it builds, and the right-hand side failing when an operand has no
register (`rhs_*_none`). All by `isel_eval`, over an abstract `p` with `Data p`; the rule
theorems are in `IselFamilyALU`.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

section Extern
variable (st : LState)

theorem ctor_put_in_reg_none {x : Nat} (h : ctx.valueReg? x = none) :
    externCtor ctx T.put_in_reg [.value x] st = .unmodeled s!"put_in_reg v{x}" := by
  have : externCtor ctx T.put_in_reg [.value x] st = match ctx.valueReg? x with
      | some r => .ok (.reg r, st)
      | none => .unmodeled s!"put_in_reg v{x}" := rfl
  rw [this, h]

theorem ofV_aluRRR {k ks : Nat} {op : ALUOp} {sz : OperandSize} (hk : ALUOp.ofIdx? k = some op)
    (hs : OperandSize.ofIdx? ks = some sz) (rd rn rm : Reg) :
    MInst.ofV (.data 58 2 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm]) =
      some (.aluRRR op sz rd rn rm) := by
  have e1 : MInst.ofV (.data 58 2 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm]) =
      (do return .aluRRR (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn rm) := rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

/-- `emit` of any register-register ALU instruction value. -/
theorem emit_aluRRR {k ks : Nat} {op : ALUOp} {sz : OperandSize} (hk : ALUOp.ofIdx? k = some op)
    (hs : OperandSize.ofIdx? ks = some sz) (rd rn rm : Reg) :
    externCtor ctx T.emit [.data 58 2 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm]] st =
      .ok (.op .unit, st.emit (.aluRRR op sz rd rn rm)) :=
  ctor_emit _ _ (ofV_aluRRR hk hs rd rn rm)

end Extern

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
/-- `sub` (`inst.isle`: `(rule (sub ty x y) (alu_rrr (ALUOp.Sub) ty x y))`). -/
theorem sub_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hemit : ∀ st rd rn rm, externCtor ctx T.emit
      [.data 58 2 [.data 59 1 [], .data 93 ks [], .reg rd, .reg rn, .reg rm]] st =
      .ok (.op .unit, st.emit (.aluRRR .sub sz rd rn rm)))
    (a b : Reg) :
    (applyTerm p (sem ctx) cfg (n+30) 27 437 [.ty (.int w), .reg a, .reg b]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR .sub sz (st.fresh .int).1 a b),
          ((tr.push rid).push rule_inst_2545.id).push rule_inst_3138.id)) := by
  have h := fun st tr n => alu_rrr_run hp ctx hc st tr n hsz hemit
  cases hp
  isel_eval [*, rule_inst_3138]

end

/-! ## `isub_base_case` (`lower.isle:801`) -/

include hp in
theorem match_801 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 74 [], .values [x, y]]) (st : LState)
    (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_801 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  cases hp
  isel_eval [*, rule_lower_801, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_801 {x y w : Nat} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64) (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_801.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .sub (if w ≤ 32 then .size32 else .size64)
          (st.fresh .int).1 rx ry), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  by_cases h32 : w ≤ 32
  · have h1 := fun st tr n => sub_run hp ctx hc st tr n
      (fun st tr n => operand_size_32 hp ctx hc st tr n h32) (fun st => emit_aluRRR ctx st (sz := .size32) rfl rfl)
    cases hp
    refine Exists.intro ?w ?h
    case h =>
      isel_eval [*, rule_lower_801, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
      rfl
  · have h1 := fun st tr n => sub_run hp ctx hc st tr n
      (fun st tr n => operand_size_64 hp ctx hc st tr n (by omega) hw)
      (fun st => emit_aluRRR ctx st (sz := .size64) rfl rfl)
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_lower_801, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
      rfl

include hp in
theorem rhs_801_none {x y w : Nat} (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none)
    (st : LState) (tr : Array RuleId) (n : Nat) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_801.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_lower_801, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_801, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_801, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

/-! ## `iadd_base_case` (`lower.isle:86`) at every width -/

include hp hc in
theorem rhs_86 {x y w : Nat} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64) (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_86.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .add (if w ≤ 32 then .size32 else .size64)
          (st.fresh .int).1 rx ry), tr')) := by
  by_cases h32 : w ≤ 32
  · simp only [h32, ↓reduceIte]
    exact ⟨_, rhs_86_32 hp ctx hc hx hy h32 st tr n⟩
  · simp only [h32, ↓reduceIte]
    exact ⟨_, rhs_86_64 hp ctx hc hx hy (by omega) hw st tr n⟩

include hp in
theorem rhs_86_none {x y w : Nat} (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none)
    (st : LState) (tr : Array RuleId) (n : Nat) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_86.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_lower_86, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_86, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_86, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

end Backend.Proof
