import FV.Backend.Proof.IselFamAluBBase

/-!
# Family B: unary ALU root rules (`ineg`, `bnot`, …), forward lemmas and `LowerRuleOk`

Per rule: the match phase (`match_*`), the right-hand side at every width (`rhs_*`) and the
right-hand side failing when the operand has no register (`rhs_*_none`), all by `isel_eval`
over an abstract `p` with `Data p`; then the rule theorem from `unary_front` (which
instruction), the forward lemmas (determinism), `PRun` (the emitted code) and a width lemma.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

theorem ctor_zero_reg (st : LState) : externCtor ctx T.zero_reg [] st = .ok (.reg .xzr, st) := rfl

theorem szOf_bits {w : Nat} (hw : w ≤ 64) : w ≤ (szOf w).bits := by
  unfold szOf; split <;> simp [OperandSize.bits] <;> omega

/-! ## `ineg_base_case` (`lower.isle:857`): `(sub ty (zero_reg) x)` -/

include hp in
theorem match_857 {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 29 [.data 151 75 [], .value x]) (st : LState)
    (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_857 [.inst i]).run (st, tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_857]

include hp hc in
theorem rhs_857 {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) (hw : w ≤ 64)
    (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_857.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .sub (szOf w) (st.fresh .int).1 .xzr rx), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have hz := ctor_zero_reg ctx
  by_cases h32 : w ≤ 32
  · have h1 := fun st tr n => sub_run hp ctx hc st tr n
      (fun st tr n => operand_size_32 hp ctx hc st tr n h32)
      (fun st => emit_aluRRR ctx st (sz := .size32) rfl rfl)
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w ?h
    case h =>
      isel_eval [*, rule_lower_857, ctor_put_in_reg ctx _ hx]
      rfl
  · have h1 := fun st tr n => sub_run hp ctx hc st tr n
      (fun st tr n => operand_size_64 hp ctx hc st tr n (by omega) hw)
      (fun st => emit_aluRRR ctx st (sz := .size64) rfl rfl)
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_lower_857, ctor_put_in_reg ctx _ hx]
      rfl

include hp in
theorem rhs_857_none {x w : Nat} (hx : ctx.valueReg? x = none) (st : LState)
    (tr : Array RuleId) (n : Nat) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_857.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) ≠ .ok (some v, s') := by
  have hz := ctor_zero_reg ctx
  cases hp
  isel_eval [*, rule_lower_857, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

set_option maxRecDepth 20000 in
theorem variantNames_Ineg : (variantNames 151)[75]? = some "Ineg" := rfl

theorem ispec_xzr_sub (sz : OperandSize) (d x : Nat) (a : CV) (w : Arm.ArmState) :
    ispec (.aluRRR .sub sz (.vreg d .int) .xzr (.vreg x .int)) [a] w =
      some ([resX sz (0#sz.bits - opnd sz a)], w, .next) := by
  cases sz <;> rfl

include hp in
/-- **`ineg_base_case`** (`lower.isle:857`), i8..i64: `sub wd, wzr, wn` / `sub xd, xzr, xn`. -/
theorem ineg_base_case_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_857 :=
  unary_ruleOk hp (cop := .ineg) rfl hp.t2359 term_2359_kind variantNames_Ineg rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun _ => True) (fun _ _ => True) (fun _ _ => 1)
    (fun w _ b x => [.aluRRR .sub (szOf w) (.vreg b .int) .xzr (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ _ _ st tr m _ _ hi hty hw hd _ h => by
      rw [match_857 hp ctx hi hty hw hd st tr m] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      exact ⟨h.1.symm, h.2.symm, trivial⟩)
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_857 hp ctx hc hx hw st tr n
      exact ⟨tr', _, h, by simp [LState.emit, LState.fresh], rfl⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_857_none hp ctx hx st tr n v s'
      · exact absurd trivial hx)
    (fun _ _ _ => Nat.le_refl _)
    (fun _ _ b _ mi hmi d hd => by
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [(vdefs_rr rfl).1] at hd; simp at hd; omega)
    (fun _ _ b x mi hmi u hu => by
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [(vdefs_rr rfl).2] at hu; simp at hu; exact .inr hu)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ _ _ _ _ hu => ⟨_, prun_rr hR rfl (fun w => ispec_xzr_sub _ _ _ _ w)
      (prun_nil _), by
        have hu' : (ρ x).setWidth ty.width = u := hu
        subst hu'
        wcases ty hety [Clif.Sem.unary, Clif.Sem.ineg]⟩)

end Backend.Proof
