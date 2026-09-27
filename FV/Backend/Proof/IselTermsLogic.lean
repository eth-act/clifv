import FV.Backend.Proof.IselRulesALUA

/-!
# `alu_rs_imm_logic_commutative` and `alu_rs_imm_logic`: forward lemmas of their rules

`alu_rs_imm_logic_commutative op ty x y` (`inst.isle:3913`, five rules) emits one instruction:
`AluRRR op` (base), `AluRRImmLogic op` when an operand is an `iconst` encodable as a logical
immediate, `AluRRRShift op … lsl #amt` when an operand is `ishl z (iconst k)`.
`alu_rs_imm_logic` (`:3937`, three rules) is the non-commutative variant (right operand only).
This file evaluates each rule's match phase on the looked-through definitions and its
right-hand side; `IselFamALUALogic` assembles the term contracts.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

/-! ## Extern constructors used by the if-lets -/

/-- `imm_logic_from_imm64 ty k` (types narrower than 32 bits use the 32-bit encoding). -/
def immLogicOf? (w : Nat) (k : Int) : Option ImmLogic :=
  if w ≤ 32 then ImmLogic.ofNat? (u64 k) .size32
  else if w = 64 then ImmLogic.ofNat? (u64 k) .size64 else none

/-- `lshl_from_imm64 ty k`: `lsl` by `k` masked to the type width, if `k < 64`. -/
def lshlOf? (w : Nat) (k : Int) : Option ShiftOpAndAmt :=
  match shiftImm? (u64 k) with
  | some s => if w ≤ 255 then some ⟨.lsl, Nat.land s (w - 1)⟩ else none
  | none => none

section Extern
variable (ctx : Ctx) (st : LState)

theorem ctor_imm_logic_from_imm64 (w : Nat) (k : Int) :
    externCtor ctx T.imm_logic_from_imm64 [.ty (.int w), .int k] st =
      (let ty := if (CTy.int w).bits < 32 then CTy.int 32 else CTy.int w
       if (ty == .int 32 || ty == .int 64) = true then
         match (ImmLogic.ofNat? (u64 k) (.ofBits ty.bits)).map (V.op ∘ Opnd.immLogic) with
         | some v => ExtResult.ok (v, st)
         | none => .fail
       else .fail) := by rfl

/-- `imm_logic_from_imm64` is `immLogicOf?` (by cases on the width, rewriting only: the
reduct of `ImmLogic.ofNat?` must never be unfolded). -/
theorem ctor_imm_logic_eq (w : Nat) (k : Int) :
    externCtor ctx T.imm_logic_from_imm64 [.ty (.int w), .int k] st =
      match immLogicOf? w k with
      | some i => .ok (.op (.immLogic i), st)
      | none => .fail := by
  rw [ctor_imm_logic_from_imm64]
  unfold immLogicOf?
  by_cases h1 : w < 32
  · have h1' : (CTy.int w).bits < 32 := h1
    have h2 : ((CTy.int 32 == CTy.int 32) || (CTy.int 32 == CTy.int 64)) = true := rfl
    have h3 : OperandSize.ofBits (CTy.int 32).bits = .size32 := rfl
    simp only [h1', if_true]
    rw [if_pos h2, h3, if_pos (Nat.le_of_lt h1)]
    generalize ImmLogic.ofNat? (u64 k) .size32 = I
    cases I <;> rfl
  · have h1' : ¬ (CTy.int w).bits < 32 := h1
    simp only [h1', if_false]
    by_cases h32 : w = 32
    · subst h32
      have h2 : ((CTy.int 32 == CTy.int 32) || (CTy.int 32 == CTy.int 64)) = true := rfl
      have h3 : OperandSize.ofBits (CTy.int 32).bits = .size32 := rfl
      rw [if_pos h2, h3, if_pos (Nat.le_refl _)]
      generalize ImmLogic.ofNat? (u64 k) .size32 = I
      cases I <;> rfl
    · by_cases h64 : w = 64
      · subst h64
        have h2 : ((CTy.int 64 == CTy.int 32) || (CTy.int 64 == CTy.int 64)) = true := rfl
        have h3 : OperandSize.ofBits (CTy.int 64).bits = .size64 := rfl
        rw [if_pos h2, h3, if_neg (by decide), if_pos rfl]
        generalize ImmLogic.ofNat? (u64 k) .size64 = I
        cases I <;> rfl
      · have h2 : ((CTy.int w == CTy.int 32) || (CTy.int w == CTy.int 64)) = false := by
          have a1 : (CTy.int w == CTy.int 32) = false := by
            show (w == 32) = false; exact beq_false_of_ne h32
          have a2 : (CTy.int w == CTy.int 64) = false := by
            show (w == 64) = false; exact beq_false_of_ne h64
          rw [a1, a2]; rfl
        rw [if_neg (by rw [h2]; decide), if_neg (by omega), if_neg h64]

theorem ctor_imm_logic_some {w : Nat} {k : Int} {i : ImmLogic} (h : immLogicOf? w k = some i) :
    externCtor ctx T.imm_logic_from_imm64 [.ty (.int w), .int k] st = .ok (.op (.immLogic i), st) := by
  rw [ctor_imm_logic_eq, h]

theorem ctor_imm_logic_none {w : Nat} {k : Int} (h : immLogicOf? w k = none) :
    externCtor ctx T.imm_logic_from_imm64 [.ty (.int w), .int k] st = .fail := by
  rw [ctor_imm_logic_eq, h]

theorem ctor_lshl_from_imm64 (w : Nat) (k : Int) :
    externCtor ctx T.lshl_from_imm64 [.ty (.int w), .int k] st =
      match lshlOf? w k with
      | some s => .ok (.op (.shiftOpAndAmt s), st)
      | none => .fail := by
  have e : externCtor ctx T.lshl_from_imm64 [.ty (.int w), .int k] st =
      (match shiftImm? (u64 k) with
       | some s => if (CTy.int w).bits ≤ 255 then
           ExtResult.ok (V.op (.shiftOpAndAmt ⟨.lsl, Nat.land s ((CTy.int w).bits - 1)⟩), st)
         else .fail
       | none => .fail) := rfl
  rw [e]
  unfold lshlOf?
  cases shiftImm? (u64 k) with
  | none => rfl
  | some s =>
    simp only [CTy.bits]
    by_cases h : w ≤ 255 <;> simp [h]

theorem ctor_lshl_some {w : Nat} {k : Int} {sh : ShiftOpAndAmt} (h : lshlOf? w k = some sh) :
    externCtor ctx T.lshl_from_imm64 [.ty (.int w), .int k] st = .ok (.op (.shiftOpAndAmt sh), st) := by
  rw [ctor_lshl_from_imm64, h]

theorem ctor_lshl_none {w : Nat} {k : Int} (h : lshlOf? w k = none) :
    externCtor ctx T.lshl_from_imm64 [.ty (.int w), .int k] st = .fail := by
  rw [ctor_lshl_from_imm64, h]

end Extern

/-- Rule environment with 6 variables, as the matcher builds it. -/
abbrev env6 (a b c d e g : V) : Interp.Env V :=
  ((((((Array.replicate 6 none).setIfInBounds 0 (some a)).setIfInBounds 1 (some b)).setIfInBounds 2
    (some c)).setIfInBounds 3 (some d)).setIfInBounds 4 (some e)).setIfInBounds 5 (some g)

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## The instruction-emitting helpers -/

section Helpers
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem alu_rr_imm_logic_run {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a : Reg) (i : ImmLogic) :
    (applyTerm p (sem ctx) cfg (n+20) 27 360 [.data 59 k [], .ty (.int w), .reg a, .op (.immLogic i)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmLogic op sz (st.fresh .int).1 a i),
          (tr.push rid).push rule_inst_2529.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_aluRRImmLogic hk hs rd rn i)
  cases hp
  isel_eval [*, rule_inst_2529, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
theorem alu_rrr_shift_run {k ks : Nat} {op : ALUOp} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a b : Reg)
    (sh : ShiftOpAndAmt) :
    (applyTerm p (sem ctx) cfg (n+20) 27 377
      [.data 59 k [], .ty (.int w), .reg a, .reg b, .op (.shiftOpAndAmt sh)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift op sz (st.fresh .int).1 a b sh),
          (tr.push rid).push rule_inst_2656.id)) := by
  have hemit := fun st rd rn rm => ctor_emit ctx st (ofV_aluRRRShift hk hs rd rn rm sh)
  cases hp
  isel_eval [*, rule_inst_2656, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

end Helpers

/-! ## `alu_rs_imm_logic_commutative` (term 565): the five rules -/

section Comm
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_3916 (k w x y : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_inst_3916 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  cases hp
  isel_eval [rule_inst_3916]

include hp hc in
theorem rhs_3916 {k w x y : Nat} {op : ALUOp} {rx ry : Reg} (hk : ALUOp.ofIdx? k = some op)
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3916.rhs
        (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR op (szOf w) (st.fresh .int).1 rx ry), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rrr_run hp ctx hc st tr n hsz
    (fun st rd rn rm => emit_aluRRR ctx st hk hs rd rn rm)
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3916, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
    rfl

include hp in
theorem rhs_3916_none {k w x y : Nat} (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3916.rhs
        (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_inst_3916, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_inst_3916, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_inst_3916, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

end Comm

section CommLook
variable (st : LState) (tr : Array RuleId) (n : Nat)

/-! ### An `iconst` operand (rules 3920 right, 3923 left) -/

include hp in
theorem match_3920 {k w x y j : Nat} {kk : Int} {infoj : IInfo} {imm : ImmLogic}
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int kk]) (himm : immLogicOf? w kk = some imm) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3920 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm))),
        (st, tr)) := by
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ctor_imm_logic_some ctx st himm
  cases hp
  isel_eval [*, rule_inst_3920]

include hp in
theorem match_3920_none {k w x y j : Nat} {kk : Int} {infoj : IInfo}
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int kk]) (himm : immLogicOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3920 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) = .ok (none, (st, tr)) := by
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ctor_imm_logic_none ctx st himm
  cases hp
  isel_eval [*, rule_inst_3920]

include hp in
theorem match_3923 {k w x y j : Nat} {kk : Int} {infoj : IInfo} {imm : ImmLogic}
    (hj : ctx.defInst? x = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int kk]) (himm : immLogicOf? w kk = some imm) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3923 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env5 (.data 59 k []) (.ty (.int w)) (.int kk) (.value y) (.op (.immLogic imm))),
        (st, tr)) := by
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ctor_imm_logic_some ctx st himm
  cases hp
  isel_eval [*, rule_inst_3923]

include hp in
theorem match_3923_none {k w x y j : Nat} {kk : Int} {infoj : IInfo}
    (hj : ctx.defInst? x = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int kk]) (himm : immLogicOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3923 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) = .ok (none, (st, tr)) := by
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ctor_imm_logic_none ctx st himm
  cases hp
  isel_eval [*, rule_inst_3923]

include hp hc in
theorem rhs_3920 {k w x : Nat} {kk : Int} {op : ALUOp} {rx : Reg} {imm : ImmLogic}
    (hk : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? x = some rx) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3920.rhs
        (env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.fresh .int).1 rx imm), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rr_imm_logic_run hp ctx hc st tr n hsz hk hs
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3920, ctor_put_in_reg ctx _ hx]
    rfl

include hp in
theorem rhs_3920_none {k w x : Nat} {kk : Int} {imm : ImmLogic} (hx : ctx.valueReg? x = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3920.rhs
        (env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm)))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_inst_3920, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp hc in
theorem rhs_3923 {k w y : Nat} {kk : Int} {op : ALUOp} {ry : Reg} {imm : ImmLogic}
    (hk : ALUOp.ofIdx? k = some op) (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3923.rhs
        (env5 (.data 59 k []) (.ty (.int w)) (.int kk) (.value y) (.op (.immLogic imm)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.fresh .int).1 ry imm), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rr_imm_logic_run hp ctx hc st tr n hsz hk hs
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3923, ctor_put_in_reg ctx _ hy]
    rfl

include hp in
theorem rhs_3923_none {k w y : Nat} {kk : Int} {imm : ImmLogic} (hy : ctx.valueReg? y = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3923.rhs
        (env5 (.data 59 k []) (.ty (.int w)) (.int kk) (.value y) (.op (.immLogic imm)))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_inst_3923, ctor_put_in_reg_none ctx _ hy]
  exact fun h => by cases h

/-! ### An `ishl z (iconst k)` operand (rules 3928 right, 3931 left) -/

include hp in
theorem match_3928 {k w x y z b j1 j2 : Nat} {kk : Int} {info1 info2 : IInfo} {sh : ShiftOpAndAmt}
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = some sh) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3928 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk)
        (.op (.shiftOpAndAmt sh))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_some ctx st hsh
  cases hp
  isel_eval [*, rule_inst_3928, ext_value_array_2]

include hp in
theorem match_3928_none {k w x y z b j1 j2 : Nat} {kk : Int} {info1 info2 : IInfo}
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3928 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) = .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_none ctx st hsh
  cases hp
  isel_eval [*, rule_inst_3928, ext_value_array_2]

include hp in
theorem match_3931 {k w x y z b j1 j2 : Nat} {kk : Int} {info1 info2 : IInfo} {sh : ShiftOpAndAmt}
    (hj1 : ctx.defInst? x = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = some sh) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3931 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env6 (.data 59 k []) (.ty (.int w)) (.value z) (.int kk) (.value y)
        (.op (.shiftOpAndAmt sh))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_some ctx st hsh
  cases hp
  isel_eval [*, rule_inst_3931, ext_value_array_2]

include hp in
theorem match_3931_none {k w x y z b j1 j2 : Nat} {kk : Int} {info1 info2 : IInfo}
    (hj1 : ctx.defInst? x = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3931 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) = .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_none ctx st hsh
  cases hp
  isel_eval [*, rule_inst_3931, ext_value_array_2]

include hp hc in
theorem rhs_3928 {k w x z : Nat} {kk : Int} {op : ALUOp} {rx rz : Reg} {sh : ShiftOpAndAmt}
    (hk : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? x = some rx) (hz : ctx.valueReg? z = some rz)
    (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3928.rhs
        (env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk)
          (.op (.shiftOpAndAmt sh)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.fresh .int).1 rx rz sh), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rrr_shift_run hp ctx hc st tr n hsz hk hs
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3928, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hz]
    rfl

include hp in
theorem rhs_3928_none {k w x z : Nat} {kk : Int} {sh : ShiftOpAndAmt}
    (hxz : ctx.valueReg? x = none ∨ ctx.valueReg? z = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3928.rhs
        (env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk)
          (.op (.shiftOpAndAmt sh)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxz with hx | hz
  · isel_eval [*, rule_inst_3928, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_inst_3928, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_inst_3928, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hz]
      exact fun h => by cases h

include hp hc in
theorem rhs_3931 {k w y z : Nat} {kk : Int} {op : ALUOp} {ry rz : Reg} {sh : ShiftOpAndAmt}
    (hk : ALUOp.ofIdx? k = some op) (hy : ctx.valueReg? y = some ry) (hz : ctx.valueReg? z = some rz)
    (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3931.rhs
        (env6 (.data 59 k []) (.ty (.int w)) (.value z) (.int kk) (.value y)
          (.op (.shiftOpAndAmt sh)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.fresh .int).1 ry rz sh), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rrr_shift_run hp ctx hc st tr n hsz hk hs
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3931, ctor_put_in_reg ctx _ hy, ctor_put_in_reg ctx _ hz]
    rfl

include hp in
theorem rhs_3931_none {k w y z : Nat} {kk : Int} {sh : ShiftOpAndAmt}
    (hyz : ctx.valueReg? y = none ∨ ctx.valueReg? z = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3931.rhs
        (env6 (.data 59 k []) (.ty (.int w)) (.value z) (.int kk) (.value y)
          (.op (.shiftOpAndAmt sh)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hyz with hy | hz
  · isel_eval [*, rule_inst_3931, ctor_put_in_reg_none ctx _ hy]
    exact fun h => by cases h
  · cases hy : ctx.valueReg? y with
    | none =>
      isel_eval [*, rule_inst_3931, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h
    | some ry =>
      isel_eval [*, rule_inst_3931, ctor_put_in_reg ctx _ hy, ctor_put_in_reg_none ctx _ hz]
      exact fun h => by cases h

end CommLook

include hp in
theorem match_1412 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 97 [], .values [x, y]]) (st : LState)
    (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1412 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_1412, ext_ty_int, ext_value_array_2]

include hp in
theorem args_1412 (w x y : Nat) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalArgs p (sem ctx) cfg (n+5) [.term 59 1966 [], .var 14 0, .var 15 1, .var 15 2]
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some [.data 59 4 [], .ty (.int w), .value x, .value y], (st, tr)) := by
  cases hp
  isel_eval [*]

include hp in
theorem match_1449 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [x, y]]) (st : LState)
    (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1449 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_1449, ext_ty_int, ext_value_array_2]

include hp in
theorem args_1449 (w x y : Nat) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalArgs p (sem ctx) cfg (n+5) [.term 59 1964 [], .var 14 0, .var 15 1, .var 15 2]
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some [.data 59 2 [], .ty (.int w), .value x, .value y], (st, tr)) := by
  cases hp
  isel_eval [*]

include hp in
theorem match_1516 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 99 [], .values [x, y]]) (st : LState)
    (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1516 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_1516, ext_ty_int, ext_value_array_2]

include hp in
theorem args_1516 (w x y : Nat) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalArgs p (sem ctx) cfg (n+5) [.term 59 1969 [], .var 14 0, .var 15 1, .var 15 2]
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some [.data 59 7 [], .ty (.int w), .value x, .value y], (st, tr)) := by
  cases hp
  isel_eval [*]

/-! ## `add_shift` / `sub_shift` and the shifted-operand `iadd`/`isub` rules (116, 120, 821) -/

section ShiftRules
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem add_shift_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a b : Reg) (sh : ShiftOpAndAmt) :
    (applyTerm p (sem ctx) cfg (n+30) 27 435 [.ty (.int w), .reg a, .reg b, .op (.shiftOpAndAmt sh)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift .add sz (st.fresh .int).1 a b sh),
          ((tr.push rid).push rule_inst_2656.id).push rule_inst_3130.id)) := by
  have h := fun st tr n => alu_rrr_shift_run hp ctx hc st tr n hsz (k := 0) rfl hs
  cases hp
  isel_eval [*, rule_inst_3130]

include hp hc in
theorem sub_shift_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a b : Reg) (sh : ShiftOpAndAmt) :
    (applyTerm p (sem ctx) cfg (n+30) 27 440 [.ty (.int w), .reg a, .reg b, .op (.shiftOpAndAmt sh)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift .sub sz (st.fresh .int).1 a b sh),
          ((tr.push rid).push rule_inst_2656.id).push rule_inst_3150.id)) := by
  have h := fun st tr n => alu_rrr_shift_run hp ctx hc st tr n hsz (k := 1) rfl hs
  cases hp
  isel_eval [*, rule_inst_3150]

include hp in
theorem match_116 {i x y z b w j1 j2 : Nat} {kk : Int} {info info1 info2 : IInfo} {sh : ShiftOpAndAmt}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = some sh) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_116 [.inst i]).run (st, tr) =
      .ok (some (env5 (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh))), (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_some ctx st hsh
  cases hp
  isel_eval [*, rule_lower_116, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp in
theorem match_116_none {i x y z b w j1 j2 : Nat} {kk : Int} {info info1 info2 : IInfo}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_116 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_none ctx st hsh
  cases hp
  isel_eval [*, rule_lower_116, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_116 {x z w : Nat} {kk : Int} {rx rz : Reg} {sh : ShiftOpAndAmt}
    (hx : ctx.valueReg? x = some rx) (hz : ctx.valueReg? z = some rz) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_116.rhs (env5 (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh)))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRShift .add (szOf w) (st.fresh .int).1 rx rz sh), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => add_shift_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_116, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hz]
    rfl

include hp in
theorem rhs_116_none {x z w : Nat} {kk : Int} {sh : ShiftOpAndAmt}
    (hxz : ctx.valueReg? x = none ∨ ctx.valueReg? z = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_116.rhs (env5 (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxz with hx | hz
  · isel_eval [*, rule_lower_116, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_116, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_116, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hz]
      exact fun h => by cases h

include hp in
theorem match_120 {i x y z b w j1 j2 : Nat} {kk : Int} {info info1 info2 : IInfo} {sh : ShiftOpAndAmt}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj1 : ctx.defInst? x = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = some sh) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_120 [.inst i]).run (st, tr) =
      .ok (some (env5 (.ty (.int w)) (.value z) (.int kk) (.value y) (.op (.shiftOpAndAmt sh))), (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_some ctx st hsh
  cases hp
  isel_eval [*, rule_lower_120, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp in
theorem match_120_none {i x y z b w j1 j2 : Nat} {kk : Int} {info info1 info2 : IInfo}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj1 : ctx.defInst? x = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_120 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_none ctx st hsh
  cases hp
  isel_eval [*, rule_lower_120, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_120 {y z w : Nat} {kk : Int} {rx rz : Reg} {sh : ShiftOpAndAmt}
    (hx : ctx.valueReg? y = some rx) (hz : ctx.valueReg? z = some rz) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_120.rhs (env5 (.ty (.int w)) (.value z) (.int kk) (.value y) (.op (.shiftOpAndAmt sh)))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRShift .add (szOf w) (st.fresh .int).1 rx rz sh), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => add_shift_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_120, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hz]
    rfl

include hp in
theorem rhs_120_none {y z w : Nat} {kk : Int} {sh : ShiftOpAndAmt}
    (hxz : ctx.valueReg? y = none ∨ ctx.valueReg? z = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_120.rhs (env5 (.ty (.int w)) (.value z) (.int kk) (.value y) (.op (.shiftOpAndAmt sh)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxz with hx | hz
  · isel_eval [*, rule_lower_120, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? y with
    | none =>
      isel_eval [*, rule_lower_120, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_120, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hz]
      exact fun h => by cases h

include hp in
theorem match_821 {i x y z b w j1 j2 : Nat} {kk : Int} {info info1 info2 : IInfo} {sh : ShiftOpAndAmt}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 74 [], .values [x, y]])
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = some sh) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_821 [.inst i]).run (st, tr) =
      .ok (some (env5 (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh))), (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_some ctx st hsh
  cases hp
  isel_eval [*, rule_lower_821, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp in
theorem match_821_none {i x y z b w j1 j2 : Nat} {kk : Int} {info info1 info2 : IInfo}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 74 [], .values [x, y]])
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_821 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_none ctx st hsh
  cases hp
  isel_eval [*, rule_lower_821, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_821 {x z w : Nat} {kk : Int} {rx rz : Reg} {sh : ShiftOpAndAmt}
    (hx : ctx.valueReg? x = some rx) (hz : ctx.valueReg? z = some rz) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_821.rhs (env5 (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh)))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRShift .sub (szOf w) (st.fresh .int).1 rx rz sh), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => sub_shift_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_821, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hz]
    rfl

include hp in
theorem rhs_821_none {x z w : Nat} {kk : Int} {sh : ShiftOpAndAmt}
    (hxz : ctx.valueReg? x = none ∨ ctx.valueReg? z = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_821.rhs (env5 (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxz with hx | hz
  · isel_eval [*, rule_lower_821, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_821, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_821, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hz]
      exact fun h => by cases h

end ShiftRules

end Backend.Proof
