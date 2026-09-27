import FV.Backend.Proof.IselTermsALUAMul

/-!
# Extended-register operands (`extended_value_from_value`): forward lemmas

`iadd_extend_right` (`lower.isle:108`), `iadd_extend_left` (`:111`), `isub_extend` (`:816`) look
through an operand defined by `uextend`/`sextend` of a 8/16/32-bit value `x'`
(`extended_value_from_value`, an external extractor: `ctx.defClif?` and `ctx.valueType?` of
`x'`, `extOpOf`) and emit `add`/`sub rd, rn, x', {u,s}xt{b,h,w}` through `add_extend`/
`sub_extend` → `alu_rr_extend_reg` → `alu_rrr_extend`. The rule theorems are in
`IselFamALUAExt`.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

/-- The extend operation `get_as_extended_value` picks for a CLIF extend from `b` bits. -/
def extOpOf (op : Clif.ExtendOp) (b : Nat) : Option ExtendOp :=
  match op, b with
  | .sextend, 8 => some .sxtb | .uextend, 8 => some .uxtb
  | .sextend, 16 => some .sxth | .uextend, 16 => some .uxth
  | .sextend, 32 => some .sxtw | .uextend, 32 => some .uxtw
  | _, _ => none

theorem ExtendOp.ofIdx?_idx (e : ExtendOp) : ExtendOp.ofIdx? e.idx = some e := by
  cases e <;> rfl

section Extern
variable (ctx : Ctx) (st : LState)

theorem ext_extended_eq (y : Nat) :
    externExtract ctx T.extended_value_from_value (.value y) st =
      match ctx.defClif? y with
      | some (.extend op _ x) =>
        match ctx.valueType? x with
        | some (.int b) =>
          match extOpOf op b with
          | some e => .ok [.op (.extended x e)]
          | none => .unmodeled "get_as_extended_value: bad width"
        | _ => .unmodeled "get_as_extended_value: operand type"
      | _ => .fail := rfl

/-- **`extended_value_from_value` succeeded on `y`**: `y` is an extend of a 8/16/32-bit value. -/
theorem ext_extended_inv {y : Nat} {fs : List V}
    (h : externExtract ctx T.extended_value_from_value (.value y) st = .ok fs) :
    ∃ op ty' x b e, ctx.defClif? y = some (.extend op ty' x) ∧ ctx.valueType? x = some (.int b) ∧
      extOpOf op b = some e ∧ fs = [.op (.extended x e)] := by
  rw [ext_extended_eq] at h
  split at h
  · rename_i op ty' x hd
    split at h
    · rename_i b hv
      split at h
      · rename_i e he
        cases h
        exact ⟨op, ty', x, b, e, hd, hv, he, rfl⟩
      · cases h
    · cases h
  · cases h

theorem ext_extended_some {y x b : Nat} {op : Clif.ExtendOp} {ty' : Clif.Ty} {e : ExtendOp}
    (hd : ctx.defClif? y = some (.extend op ty' x)) (hv : ctx.valueType? x = some (.int b))
    (he : extOpOf op b = some e) :
    externExtract ctx T.extended_value_from_value (.value y) st = .ok [.op (.extended x e)] := by
  rw [ext_extended_eq, hd]
  simp only [hv, he]

theorem ctor_put_extended_in_reg {x : Nat} {r : Reg} (e : ExtendOp) (h : ctx.valueReg? x = some r) :
    externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st = .ok (.reg r, st) := by
  have : externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st = match ctx.valueReg? x with
      | some r => .ok (.reg r, st)
      | none => .unmodeled "put_extended_in_reg" := rfl
  rw [this, h]

theorem ctor_put_extended_in_reg_none {x : Nat} (e : ExtendOp) (h : ctx.valueReg? x = none) :
    externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st =
      .unmodeled "put_extended_in_reg" := by
  have : externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st = match ctx.valueReg? x with
      | some r => .ok (.reg r, st)
      | none => .unmodeled "put_extended_in_reg" := rfl
  rw [this, h]

theorem ctor_get_extended_op (x : Nat) (e : ExtendOp) :
    externCtor ctx T.get_extended_op [.op (.extended x e)] st = .ok (.data 84 e.idx [], st) := rfl

end Extern

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## `alu_rrr_extend`, `alu_rr_extend_reg`, `add_extend`, `sub_extend` -/

section Helpers
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem alu_rrr_extend_run {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a b : Reg)
    (e : ExtendOp) :
    (applyTerm p (sem ctx) cfg (n+20) 27 380
      [.data 59 k [], .ty (.int w), .reg a, .reg b, .data 84 e.idx []]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRExtend op sz (st.fresh .int).1 a b e),
          (tr.push rid).push rule_inst_2684.id)) := by
  have hemit := fun st rd rn rm => ctor_emit ctx st
    (ofV_aluRRRExtend hk hs (ExtendOp.ofIdx?_idx e) rd rn rm)
  cases hp
  isel_eval [*, rule_inst_2684, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
theorem alu_rr_extend_reg_run {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) {x : Nat}
    {rx : Reg} (hx : ctx.valueReg? x = some rx) (e : ExtendOp) :
    (applyTerm p (sem ctx) cfg (n+30) 27 381
      [.data 59 k [], .ty (.int w), .reg a, .op (.extended x e)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRExtend op sz (st.fresh .int).1 a rx e),
          ((tr.push rid).push rule_inst_2684.id).push rule_inst_2693.id)) := by
  have h := fun st tr n => alu_rrr_extend_run hp ctx hc st tr n hsz hk hs
  have h1 := ctor_put_extended_in_reg ctx st e hx
  have h2 := ctor_get_extended_op ctx st x e
  cases hp
  isel_eval [*, rule_inst_2693]

include hp hc in
theorem add_extend_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) {x : Nat} {rx : Reg}
    (hx : ctx.valueReg? x = some rx) (e : ExtendOp) :
    (applyTerm p (sem ctx) cfg (n+40) 27 434 [.ty (.int w), .reg a, .op (.extended x e)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRExtend .add sz (st.fresh .int).1 a rx e),
          (((tr.push rid).push rule_inst_2684.id).push rule_inst_2693.id).push rule_inst_3126.id)) := by
  have h := fun st tr n => alu_rr_extend_reg_run hp ctx hc st tr n hsz (k := 0) rfl hs a hx e
  cases hp
  isel_eval [*, rule_inst_3126]

include hp hc in
theorem sub_extend_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) {x : Nat} {rx : Reg}
    (hx : ctx.valueReg? x = some rx) (e : ExtendOp) :
    (applyTerm p (sem ctx) cfg (n+40) 27 439 [.ty (.int w), .reg a, .op (.extended x e)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRExtend .sub sz (st.fresh .int).1 a rx e),
          (((tr.push rid).push rule_inst_2684.id).push rule_inst_2693.id).push rule_inst_3146.id)) := by
  have h := fun st tr n => alu_rr_extend_reg_run hp ctx hc st tr n hsz (k := 1) rfl hs a hx e
  cases hp
  isel_eval [*, rule_inst_3146]

end Helpers

/-! ## The root rules 108, 111, 816 -/

section Roots
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_108 {i x y x' w b : Nat} {info : IInfo} {op : Clif.ExtendOp} {ty' : Clif.Ty}
    {e : ExtendOp} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hdc : ctx.defClif? y = some (.extend op ty' x')) (hv : ctx.valueType? x' = some (.int b))
    (he : extOpOf op b = some e) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_108 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.op (.extended x' e))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_extended_some ctx st hdc hv he
  cases hp
  isel_eval [*, rule_lower_108, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp in
theorem match_111 {i x y x' w b : Nat} {info : IInfo} {op : Clif.ExtendOp} {ty' : Clif.Ty}
    {e : ExtendOp} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hdc : ctx.defClif? x = some (.extend op ty' x')) (hv : ctx.valueType? x' = some (.int b))
    (he : extOpOf op b = some e) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_111 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.op (.extended x' e)) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_extended_some ctx st hdc hv he
  cases hp
  isel_eval [*, rule_lower_111, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp in
theorem match_816 {i x y x' w b : Nat} {info : IInfo} {op : Clif.ExtendOp} {ty' : Clif.Ty}
    {e : ExtendOp} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 74 [], .values [x, y]])
    (hdc : ctx.defClif? y = some (.extend op ty' x')) (hv : ctx.valueType? x' = some (.int b))
    (he : extOpOf op b = some e) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_816 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.op (.extended x' e))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_extended_some ctx st hdc hv he
  cases hp
  isel_eval [*, rule_lower_816, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_108 {x x' w : Nat} {rx rx' : Reg} {e : ExtendOp} (hx : ctx.valueReg? x = some rx)
    (hx' : ctx.valueReg? x' = some rx') (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+60) rule_lower_108.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.extended x' e)))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRExtend .add (szOf w) (st.fresh .int).1 rx rx' e), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => add_extend_run hp ctx hc st tr n hsz hs rx hx' e
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_108, ctor_put_in_reg ctx _ hx]
    rfl

include hp hc in
theorem rhs_108_none {x x' w : Nat} {e : ExtendOp}
    (h : ctx.valueReg? x = none ∨ ctx.valueReg? x' = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+60) rule_lower_108.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.extended x' e)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hx : ctx.valueReg? x with
  | none =>
    cases hp
    isel_eval [*, rule_lower_108, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  | some rx =>
  have hx' : ctx.valueReg? x' = none := by simpa [hx] using h
  have h1 := ctor_put_extended_in_reg_none ctx st e hx'
  cases hp
  isel_eval [*, rule_lower_108, ctor_put_in_reg ctx _ hx, rule_inst_3126, rule_inst_2693]
  exact fun h => by cases h

include hp hc in
theorem rhs_111 {y x' w : Nat} {ry rx' : Reg} {e : ExtendOp} (hy : ctx.valueReg? y = some ry)
    (hx' : ctx.valueReg? x' = some rx') (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+60) rule_lower_111.rhs
        (env3 (.ty (.int w)) (.op (.extended x' e)) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRExtend .add (szOf w) (st.fresh .int).1 ry rx' e), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => add_extend_run hp ctx hc st tr n hsz hs ry hx' e
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_111, ctor_put_in_reg ctx _ hy]
    rfl

include hp hc in
theorem rhs_111_none {y x' w : Nat} {e : ExtendOp}
    (h : ctx.valueReg? y = none ∨ ctx.valueReg? x' = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+60) rule_lower_111.rhs
        (env3 (.ty (.int w)) (.op (.extended x' e)) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hy : ctx.valueReg? y with
  | none =>
    cases hp
    isel_eval [*, rule_lower_111, ctor_put_in_reg_none ctx _ hy]
    exact fun h => by cases h
  | some ry =>
  have hx' : ctx.valueReg? x' = none := by simpa [hy] using h
  have h1 := ctor_put_extended_in_reg_none ctx st e hx'
  cases hp
  isel_eval [*, rule_lower_111, ctor_put_in_reg ctx _ hy, rule_inst_3126, rule_inst_2693]
  exact fun h => by cases h

include hp hc in
theorem rhs_816 {x x' w : Nat} {rx rx' : Reg} {e : ExtendOp} (hx : ctx.valueReg? x = some rx)
    (hx' : ctx.valueReg? x' = some rx') (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+60) rule_lower_816.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.extended x' e)))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRExtend .sub (szOf w) (st.fresh .int).1 rx rx' e), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => sub_extend_run hp ctx hc st tr n hsz hs rx hx' e
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_816, ctor_put_in_reg ctx _ hx]
    rfl

include hp hc in
theorem rhs_816_none {x x' w : Nat} {e : ExtendOp}
    (h : ctx.valueReg? x = none ∨ ctx.valueReg? x' = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+60) rule_lower_816.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.extended x' e)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hx : ctx.valueReg? x with
  | none =>
    cases hp
    isel_eval [*, rule_lower_816, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  | some rx =>
  have hx' : ctx.valueReg? x' = none := by simpa [hx] using h
  have h1 := ctor_put_extended_in_reg_none ctx st e hx'
  cases hp
  isel_eval [*, rule_lower_816, ctor_put_in_reg ctx _ hx, rule_inst_3146, rule_inst_2693]
  exact fun h => by cases h

end Roots

end Backend.Proof
