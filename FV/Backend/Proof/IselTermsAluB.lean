import FV.Backend.Proof.IselRulesALU

/-!
# Family B: contracts of the emitting helper terms (`bit_rr`, `alu_rr_imm_shift`,
`alu_rr_imm12`, `alu_rr_imm_logic`, `extend`) and their one-rule wrappers

Same shape as `IselTerms`' `alu_rrr_run`: for every fuel above a bound and any lowering state,
the value (a fresh vreg), the one instruction appended and the rules fired. Generic in the
operation and the operand size (the caller supplies `operand_size`'s evaluation).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## Decoding the emitted instruction values -/

section OfV
variable (rd rn : Reg)

theorem ofV_bitRR {k ks : Nat} {op : BitOp} {sz : OperandSize} (hk : BitOp.ofIdx? k = some op)
    (hs : OperandSize.ofIdx? ks = some sz) :
    MInst.ofV (.data 58 9 [.data 85 k [], .data 93 ks [], .reg rd, .reg rn]) =
      some (.bitRR op sz rd rn) := by
  have e1 : MInst.ofV (.data 58 9 [.data 85 k [], .data 93 ks [], .reg rd, .reg rn]) =
      (do return .bitRR (← (V.data 85 k []).bitOp?) (← (V.data 93 ks []).size?) rd rn) := rfl
  have e2 : (V.data 85 k []).bitOp? = BitOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_aluRRImmShift_fb {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (i : Nat) :
    MInst.ofV (.data 58 6 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.immShift i)]) =
      some (.aluRRImmShift op sz rd rn i) := by
  have e1 : MInst.ofV (.data 58 6 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn,
      .op (.immShift i)]) =
      (do return .aluRRImmShift (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn i) :=
    rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_aluRRImm12_fb {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (i : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.imm12 i)]) =
      some (.aluRRImm12 op sz rd rn i) := by
  have e1 : MInst.ofV (.data 58 4 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn,
      .op (.imm12 i)]) =
      (do return .aluRRImm12 (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn i) :=
    rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_aluRRImmLogic_fb {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (i : ImmLogic) :
    MInst.ofV (.data 58 5 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .op (.immLogic i)]) =
      some (.aluRRImmLogic op sz rd rn i) := by
  have e1 : MInst.ofV (.data 58 5 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn,
      .op (.immLogic i)]) =
      (do return .aluRRImmLogic (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn i) :=
    rfl
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e1, e2, e3, hk, hs]
  rfl

theorem ofV_extend_fb (sg : Bool) (a b : Nat) :
    MInst.ofV (.data 58 28 [.reg rd, .reg rn, .bool sg, .int a, .int b]) =
      some (.extend rd rn sg a b) := rfl

end OfV

/-! ## The emitting terms -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
/-- `bit_rr` (`inst.isle`: `(BitRR op (operand_size ty) dst src)` into a fresh vreg). -/
theorem bit_rr_run {k ks : Nat} {op : BitOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : BitOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) :
    (applyTerm p (sem ctx) cfg (n+20) 27 386 [.data 85 k [], .ty (.int w), .reg a]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.bitRR op sz (st.fresh .int).1 a),
          (tr.push rid).push rule_inst_2733.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_bitRR rd rn hk hs)
  cases hp
  isel_eval [*, rule_inst_2733, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `alu_rr_imm_shift`. -/
theorem alu_rr_imm_shift_run {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) (i : Nat) :
    (applyTerm p (sem ctx) cfg (n+20) 27 361 [.data 59 k [], .ty (.int w), .reg a,
        .op (.immShift i)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmShift op sz (st.fresh .int).1 a i),
          (tr.push rid).push rule_inst_2537.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_aluRRImmShift_fb rd rn hk hs i)
  cases hp
  isel_eval [*, rule_inst_2537, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `alu_rr_imm12`. -/
theorem alu_rr_imm12_run_fb {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) (i : Imm12) :
    (applyTerm p (sem ctx) cfg (n+20) 27 376 [.data 59 k [], .ty (.int w), .reg a,
        .op (.imm12 i)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImm12 op sz (st.fresh .int).1 a i),
          (tr.push rid).push rule_inst_2648.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_aluRRImm12_fb rd rn hk hs i)
  cases hp
  isel_eval [*, rule_inst_2648, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `alu_rr_imm_logic`. -/
theorem alu_rr_imm_logic_run_fb {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat}
    {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a : Reg)
    (i : ImmLogic) :
    (applyTerm p (sem ctx) cfg (n+20) 27 360 [.data 59 k [], .ty (.int w), .reg a,
        .op (.immLogic i)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmLogic op sz (st.fresh .int).1 a i),
          (tr.push rid).push rule_inst_2529.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_aluRRImmLogic_fb rd rn hk hs i)
  cases hp
  isel_eval [*, rule_inst_2529, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `extend` (`(Extend dst rn signed from to)` into a fresh vreg). -/
theorem extend_run (a : Reg) (sg : Bool) (fb tb : Nat) :
    (applyTerm p (sem ctx) cfg (n+20) 27 417 [.reg a, .bool sg, .int fb, .int tb]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 a sg fb tb),
          tr.push rule_inst_2991.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_extend_fb rd rn sg fb tb)
  cases hp
  isel_eval [*, rule_inst_2991, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

end

/-! ## `put_in_reg_zext32` (three rules: `$I32`/`$I64` pass through, `fits_in_32` extends) -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

theorem ext_value_type_none {v : Nat} (h : ctx.valueType? v = none) :
    externExtract ctx T.value_type (.value v) st = .unmodeled s!"value_type of unknown v{v}" := by
  have : externExtract ctx T.value_type (.value v) st = match ctx.valueType? v with
    | some ty => .ok [.ty ty]
    | none => .unmodeled s!"value_type of unknown v{v}" := rfl
  rw [this, h]

theorem ext_fits_in_32_ty (t : CTy) :
    externExtract ctx T.fits_in_32 (.ty t) st = if t.bits ≤ 32 then .ok [.ty t] else .fail := by
  have : externExtract ctx T.fits_in_32 (.ty t) st =
    if decide (t.bits ≤ 32) = true then .ok [.ty t] else .fail := rfl
  rw [this]; by_cases h : t.bits ≤ 32 <;> simp [h]

theorem ctor_ty_bits_ty (t : CTy) : externCtor ctx T.ty_bits [.ty t] st = .ok (.int t.bits, st) :=
  rfl

theorem sem_eq_beq' (a b : V) : (sem ctx).eq a b = (a == b) := rfl

include hp hc in
theorem zext32_pass32 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx)
    (hT : ctx.valueType? x = some (.int 32)) :
    (applyTerm p (sem ctx) cfg (n+20) 27 556 [.value x]).run (st, tr) =
      .ok (some (.reg rx), (st, tr.push rule_inst_3813.id)) := by
  have h1 := ext_value_type ctx st hT
  have he := sem_eq_beq' ctx
  cases hp
  isel_eval [*, rule_inst_3809, rule_inst_3813, rule_inst_3814, ctor_put_in_reg ctx _ hx]

include hp hc in
theorem zext32_pass64 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx)
    (hT : ctx.valueType? x = some (.int 64)) :
    (applyTerm p (sem ctx) cfg (n+20) 27 556 [.value x]).run (st, tr) =
      .ok (some (.reg rx), (st, tr.push rule_inst_3814.id)) := by
  have h1 := ext_value_type ctx st hT
  have he := sem_eq_beq' ctx
  have hne : (V.ty (.int 64) == V.ty (.int 32)) = false := by decide
  cases hp
  isel_eval [*, rule_inst_3809, rule_inst_3813, rule_inst_3814, ctor_put_in_reg ctx _ hx]

include hp hc in
theorem zext32_ext {x : Nat} {rx : Reg} {t : CTy} (hx : ctx.valueReg? x = some rx)
    (hT : ctx.valueType? x = some t) (h32 : t ≠ .int 32) (h64 : t ≠ .int 64) (hb : t.bits ≤ 32) :
    (applyTerm p (sem ctx) cfg (n+40) 27 556 [.value x]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx false t.bits 32),
          (tr.push rule_inst_2991.id).push rule_inst_3809.id)) := by
  have h1 := ext_value_type ctx st hT
  have he := sem_eq_beq' ctx
  have hne32 : (V.ty t == V.ty (.int 32)) = false := by simp [h32]
  have hne64 : (V.ty t == V.ty (.int 64)) = false := by simp [h64]
  have hf := ext_fits_in_32_ty ctx st t
  simp only [hb, ↓reduceIte] at hf
  have hbits := ctor_ty_bits_ty ctx
  have hext : ∀ st tr n a, (applyTerm p (sem ctx) cfg (n+20) 27 417
      [.reg a, .bool false, .int t.bits, .int 32]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 a false t.bits 32),
          tr.push rule_inst_2991.id)) :=
    fun st tr n a => extend_run hp ctx hc st tr n a false t.bits 32
  cases hp
  isel_eval [*, rule_inst_3809, rule_inst_3813, rule_inst_3814, ctor_put_in_reg ctx _ hx]

theorem except_throw_eq {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

include hp in
theorem zext32_none {x : Nat} (hT : ctx.valueType? x = none) :
    (applyTerm p (sem ctx) cfg (n+20) 27 556 [.value x]).run (st, tr) =
      .error (.unmodeled s!"value_type of unknown v{x}") := by
  have h1 := ext_value_type_none ctx st hT
  cases hp
  isel_eval [*, rule_inst_3809, rule_inst_3813, rule_inst_3814, except_throw_eq]

include hp in
theorem zext32_big {x : Nat} {t : CTy} (hT : ctx.valueType? x = some t) (h32 : t ≠ .int 32)
    (h64 : t ≠ .int 64) (hb : ¬ t.bits ≤ 32) :
    (applyTerm p (sem ctx) cfg (n+20) 27 556 [.value x]).run (st, tr) =
      .error (.noRule "put_in_reg_zext32") := by
  have h1 := ext_value_type ctx st hT
  have he := sem_eq_beq' ctx
  have hne32 : (V.ty t == V.ty (.int 32)) = false := by simp [h32]
  have hne64 : (V.ty t == V.ty (.int 64)) = false := by simp [h64]
  have hf := ext_fits_in_32_ty ctx st t
  simp only [hb, ↓reduceIte] at hf
  cases hp
  isel_eval [*, rule_inst_3809, rule_inst_3813, rule_inst_3814]

end

end Backend.Proof
