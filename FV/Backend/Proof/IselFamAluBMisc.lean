import FV.Backend.Proof.IselFamAluBUnary

/-!
# Family B: `bnot_base_case` (1377), `nop` (78), `ireduce` (2146)

* `bnot`: `orn wd, wzr, wn` / `orn xd, xzr, xn` (`orr_not ty (zero_reg) x`), i8..i64.
* `nop`: no code, no result (`invalid_reg`).
* `ireduce`: no code; the result is the operand's own vreg (values are the low bits of their
  register, so narrowing is free).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## `bnot_base_case` (`lower.isle:1377`) -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
/-- `orr_not` (`inst.isle`: `(alu_rrr (ALUOp.OrrNot) ty x y)`). -/
theorem orr_not_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a b : Reg) :
    (applyTerm p (sem ctx) cfg (n+30) 27 495 [.ty (.int w), .reg a, .reg b]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR .orrNot sz (st.fresh .int).1 a b),
          ((tr.push rid).push rule_inst_2545.id).push rule_inst_3403.id)) := by
  have h := fun st tr n => alu_rrr_run hp ctx hc st tr n (k := 3) (op := .orrNot) hsz
    (fun st => emit_aluRRR ctx st (k := 3) (op := .orrNot) rfl hs)
  cases hp
  isel_eval [*, rule_inst_3403]

include hp in
theorem match_1377 {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 29 [.data 151 100 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1377 [.inst i]).run (st, tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_ty_int ctx st w
  cases hp
  isel_eval [*, rule_lower_1377]

include hp hc in
theorem rhs_1377 {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1377.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .orrNot (szOf w) (st.fresh .int).1 .xzr rx), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have hz := ctor_zero_reg ctx
  by_cases h32 : w ≤ 32
  · have h1 := fun st tr n => orr_not_run hp ctx hc st tr n
      (fun st tr n => operand_size_32 hp ctx hc st tr n h32) (sz := .size32) rfl
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?bw1 ?bh1
    case bh1 =>
      isel_eval [*, rule_lower_1377, ctor_put_in_reg ctx _ hx]
      rfl
  · have h1 := fun st tr n => orr_not_run hp ctx hc st tr n
      (fun st tr n => operand_size_64 hp ctx hc st tr n (w := w) (by omega) hw) (sz := .size64) rfl
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?bw2 ?bh2
    case bh2 =>
      isel_eval [*, rule_lower_1377, ctor_put_in_reg ctx _ hx]
      rfl

include hp in
theorem rhs_1377_none {x w : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1377.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) ≠ .ok (some v, s') := by
  have hz := ctor_zero_reg ctx
  cases hp
  isel_eval [*, rule_lower_1377, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

end

set_option maxRecDepth 20000 in
theorem variantNames_Bnot : (variantNames 151)[100]? = some "Bnot" := rfl

theorem ispec_xzr_orrNot (sz : OperandSize) (d x : Nat) (a : CV) (w : Arm.ArmState) :
    ispec (.aluRRR .orrNot sz (.vreg d .int) .xzr (.vreg x .int)) [a] w =
      some ([resX sz (0#sz.bits ||| ~~~(opnd sz a))], w, .next) := by
  cases sz <;> rfl

include hp in
/-- **`bnot_base_case`** (`lower.isle:1377`), i8..i64: `orn wd, wzr, wn` / `orn xd, xzr, xn`. -/
theorem bnot_base_case_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1377 :=
  unary_ruleOk hp (cop := .bnot) rfl hp.t2384 term_2384_kind variantNames_Bnot rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun _ => True) (fun _ _ => True) (fun _ _ => 1)
    (fun w _ b x => [.aluRRR .orrNot (szOf w) (.vreg b .int) .xzr (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ _ _ st tr m _ _ hi hty hw hd _ h => by
      rw [match_1377 hp ctx st tr m hi hty hw hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      exact ⟨h.1.symm, h.2.symm, trivial⟩)
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_1377 hp ctx hc st tr n hx hw
      exact ⟨tr', _, h, by simp [LState.emit, LState.fresh], rfl⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1377_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => Nat.le_refl _)
    (fun _ _ b _ mi hmi d hd => by
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [(vdefs_rr rfl).1] at hd; simp at hd; omega)
    (fun _ _ b x mi hmi u hu => by
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [(vdefs_rr rfl).2] at hu; simp at hu; exact .inr hu)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ _ _ _ _ hu => ⟨_, prun_rr hR rfl (fun w => ispec_xzr_orrNot _ _ _ _ w)
      (prun_nil _), by
        have hu' : (ρ x).setWidth ty.width = u := hu
        subst hu'
        wcases ty hety [Clif.Sem.unary, Clif.Sem.bnot]⟩)

/-! ## `nop` (`lower.isle:78`) -/

set_option maxRecDepth 20000 in
theorem variantNames_NullAry : (variantNames 152)[19]? = some "NullAry" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Nop : (variantNames 151)[64]? = some "Nop" := rfl

theorem instNames_nop {c : Clif.Inst} (h : instNames c = ("NullAry", "Nop")) : c = .nop := by
  cases c <;> simp [instNames] at h ⊢
  all_goals first
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [divOpcode] at h)
    | (rename_i op _ _; cases op <;> simp at h)
    | (rename_i op _ _ _ _ _; cases op <;> simp [loadOpcode] at h)
    | (rename_i op _ _ _ _ _ _; cases op <;> simp [storeOpcode] at h)
    | skip

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_78 {i : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hd : info.data = .data 152 19 [.data 151 64 []]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_78 [.inst i]).run (st, tr) =
      .ok (some (Array.replicate 0 none), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd] at h1
  cases hp
  isel_eval [*, rule_lower_78]

theorem ctor_invalid_reg : externCtor ctx T.invalid_reg [] st = .ok (.reg .invalid, st) := rfl

theorem term_178_kind' : T.«invalid_reg».kind = (.decl ⟨false, false, false, false⟩
    (some (.external "invalid_reg")) (some (.internal (.list [(.atom "extractor"),
      (.list [(.atom "invalid_reg")]), (.list [(.atom "is_valid_reg"), (.atom "false")])])))) := rfl

include hp hc in
theorem rhs_78 : ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_78.rhs
    (Array.replicate 0 none)).run (st, tr) = .ok (some (.regsVec [[.invalid]]), (st, tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := ctor_invalid_reg ctx
  have h4 := term_178_kind'
  cases hp
  refine Exists.intro ?nw ?nh
  case nh =>
    isel_eval [*, rule_lower_78]
    rfl

end

set_option maxRecDepth 20000 in
include hp in
/-- **`nop`** (`lower.isle:78`): no code, no results. -/
theorem nop_ok (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) :
    LowerRuleOk isem MR env cp p rule_lower_78 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn _ _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx (r := rule_lower_78) rfl hp.t2466
    term_2466_kind hp.t2348 term_2348_kind (m := m' + 1) hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [variantNames_NullAry] at hf
  rw [variantNames_Nop] at ho
  have hnm : instNames inst = ("NullAry", "Nop") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  have := instNames_nop hnm
  subst this
  have hfs : fs = [] := by
    simp only [instData, pure, Except.pure, Except.ok.injEq, instDataV] at hdat
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data hdat
    injection h3 with _ h4
    all_goals exact h4.symm
  subst hfs
  obtain ⟨tys, htys, -, hlen⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hres : info.results = [] := List.eq_nil_of_length_eq_zero hlen
  rw [match_78 hp ctx st tr m' hi hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨tr'', h⟩ := rhs_78 hp ctx hco st tr n'
  rw [h] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨[], _, by simp, rfl, LowerInstOk.mk (Nat.le_refl _) (fun m hm => by cases hm) ?_⟩
  intro fr cm ρ w _ _ _ hmr
  have ho : instOutcome env cp fr cm .nop = .ok ([], cm) := rfl
  rw [ho]
  exact ⟨fun m hm => absurd hm List.not_mem_nil, ρ, w, rfl, .inl hres, hmr⟩

/-! ## `ireduce` (`lower.isle:2146`) -/

set_option maxRecDepth 20000 in
theorem variantNames_Ireduce : (variantNames 151)[131]? = some "Ireduce" := rfl

theorem instNames_ireduce {c : Clif.Inst} (h : instNames c = ("Unary", "Ireduce")) :
    ∃ ty x, c = .ireduce ty x := by
  cases c <;> simp only [instNames, Prod.mk.injEq] at h
  all_goals first
    | exact ⟨_, _, rfl⟩
    | (exfalso; simp at h; done)
    | (exfalso; rename_i op _ _; cases op <;> simp [unaryOpcode] at h; done)
    | (exfalso; rename_i op _ _; cases op <;> simp at h; done)

theorem instData_ireduce {f : Clif.Function} {ty : Clif.Ty} {x ko : Nat} {fs : List V}
    (h : instData f (.ireduce ty x) = .ok (.data 152 29 (.data 151 ko [] :: fs))) :
    eTy ty = true ∧ fs = [.value x] := by
  simp only [instData] at h
  split at h
  · rename_i he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    injection h3 with _ h4
    exact ⟨he, h4⟩
  · cases h

theorem evalInst_ireduce_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {x : Nat}
    {vals : List Clif.Val} (h : Clif.evalInst fr cm (.ireduce ty x) = .ok (vals, cm')) :
    ∃ a, fr.regs x = some a ∧ ty.width < a.ty.width ∧
      vals = [⟨ty, Clif.Sem.ireduce ty.width a.bits⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst, Clif.Frame.get] at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some a =>
    rw [hx] at h
    by_cases hlt : ty.width < a.ty.width
    · simp [Clif.Res.ofOption, bind, Clif.Res.bind, Clif.Res.check, hlt, pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨a, rfl, hlt, rfl, rfl⟩
    · simp [Clif.Res.ofOption, bind, Clif.Res.bind, Clif.Res.check, hlt] at h

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

theorem ctor_ty_int_ref_scalar_64 {w : Nat} (hw : w ≤ 64) :
    externCtor ctx T.ty_int_ref_scalar_64 [.ty (.int w)] st = .ok (.ty (.int w), st) := by
  have : externCtor ctx T.ty_int_ref_scalar_64 [.ty (.int w)] st =
    if (decide ((CTy.int w).bits ≤ 64) && !(CTy.int w).isFloat && !(CTy.int w).isVector) = true
    then .ok (.ty (.int w), st) else .fail := rfl
  rw [this]; simp [CTy.bits, CTy.isFloat, CTy.isVector, hw]

include hp in
theorem match_2146 {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 29 [.data 151 131 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_2146 [.inst i]).run (st, tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := fun st => ctor_ty_int_ref_scalar_64 ctx st hw
  cases hp
  isel_eval [*, rule_lower_2146]

include hp hc in
theorem rhs_2146 {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_2146.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) =
      .ok (some (.regsVec [[rx]]), (st, tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st => ctor_put_in_regs ctx st hx
  have h4 := fun st r rs => ctor_value_regs_get_0 ctx st r rs
  cases hp
  refine Exists.intro ?iw ?ih
  case ih =>
    isel_eval [*, rule_lower_2146]
    rfl

include hp in
theorem rhs_2146_none {x w : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_2146.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) ≠ .ok (some v, s') := by
  have h3 : ∀ st, externCtor ctx T.put_in_regs [.value x] st = .unmodeled s!"put_in_regs v{x}" := by
    intro st
    have : externCtor ctx T.put_in_regs [.value x] st = match ctx.valueReg? x with
      | some r => .ok (.regs [r], st)
      | none => .unmodeled s!"put_in_regs v{x}" := rfl
    rw [this, hx]
  cases hp
  isel_eval [*, rule_lower_2146]
  exact fun h => by cases h

end

include hp in
/-- **`ireduce`** (`lower.isle:2146`), to i8..i64: no code, the operand's vreg. -/
theorem ireduce_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2146 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx (r := rule_lower_2146) rfl hp.t2476
    term_2476_kind hp.t2415 term_2415_kind (m := m' + 9) hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [variantNames_Unary] at hf
  rw [variantNames_Ireduce] at ho
  have hnm : instNames inst = ("Unary", "Ireduce") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, x, rfl⟩ := instNames_ireduce hnm
  obtain ⟨hety, rfl⟩ := instData_ireduce hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by rw [hres]; simp [ofClif_int_width]
  have hw := eTy_width hety
  rw [match_2146 hp ctx st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_2146_none hp ctx st tr n' hrx out (st', tr'))
  | some rx =>
  have ex := hctx.valueReg x rx hrx
  subst ex
  obtain ⟨tr'', h⟩ := rhs_2146 hp ctx hco st tr n' hrx
  rw [h] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨[], _, by simp, rfl, ?_⟩
  refine lowerInstOk_one (d := x) hMR (Nat.le_refl _) (fun _ h => by cases h) rfl ?_
  intro fr cm ρ vals cm' _ hvals _ ho
  obtain ⟨a, ha, hlt, rfl, rfl⟩ := evalInst_ireduce_ok ho
  refine ⟨rfl, (fun _ h => by cases h), .inr (by simp [ha]), _, ρ, rfl, prun_nil _, ?_⟩
  have hv := hvals x a ha
  simp only [VHolds] at hv ⊢
  simp only [Clif.Sem.ireduce]
  rw [← hv, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hlt)]

end Backend.Proof
