import FV.Backend.Proof.IselFamAluBMisc
import FV.Backend.Proof.IselTermsAluB

/-!
# Family B: `uextend` (`lower.isle:1261`) and `sextend` (`lower.isle:1315`)

`(extend x signed (ty_bits in) (ty_bits out))` with `in` the operand's `value_type`: one
`uxt*`/`sxt*` (`Extend`) instruction. The operand's CLIF type is its `value_type`
(`FrameTyped`), and CLIF checks `in < out`, so the extension is one of the six widening pairs
of `i8..i64`, each an `ispec` `extend` form.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-- The environment of the extend rules: `out`, `in` (`value_type`), `x`. -/
abbrev envExt (w x : Nat) (t : CTy) : Interp.Env V :=
  (((Array.replicate 3 none).setIfInBounds 0 (some (V.ty (CTy.int w)))).setIfInBounds 2
    (some (V.value x))).setIfInBounds 1 (some (V.ty t))

set_option maxRecDepth 20000 in
theorem variantNames_Uextend : (variantNames 151)[141]? = some "Uextend" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Sextend : (variantNames 151)[142]? = some "Sextend" := rfl

theorem instNames_extend {c : Clif.Inst} {op : Clif.ExtendOp}
    (h : instNames c = ("Unary", if op == .uextend then "Uextend" else "Sextend")) :
    ∃ ty x, c = .extend op ty x := by
  cases c <;> simp only [instNames, Prod.mk.injEq] at h
  all_goals first
    | (exfalso; cases op <;> simp at h; done)
    | (exfalso; rename_i op' _ _; cases op <;> cases op' <;> simp [unaryOpcode] at h; done)
    | (rename_i op' ty x; refine ⟨ty, x, ?_⟩; cases op <;> cases op' <;> simp at h ⊢)

theorem instData_extend {f : Clif.Function} {op : Clif.ExtendOp} {ty : Clif.Ty} {x ko : Nat}
    {fs : List V} (h : instData f (.extend op ty x) = .ok (.data 152 29 (.data 151 ko [] :: fs))) :
    eTy ty = true ∧ fs = [.value x] := by
  simp only [instData] at h
  split at h
  · rename_i he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    injection h3 with _ h4
    exact ⟨he, h4⟩
  · cases h

/-- The CLIF value of `extend op` to `ty`. -/
def extVal_fb (op : Clif.ExtendOp) (ty : Clif.Ty) {w : Nat} (b : BitVec w) : BitVec ty.width :=
  match op with
  | .uextend => Clif.Sem.uextend ty.width b
  | .sextend => Clif.Sem.sextend ty.width b

theorem evalInst_extend_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.ExtendOp}
    {ty : Clif.Ty} {x : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.extend op ty x) = .ok (vals, cm')) :
    ∃ a, fr.regs x = some a ∧ a.ty.width < ty.width ∧ cm' = cm ∧
      vals = [⟨ty, extVal_fb op ty a.bits⟩] := by
  simp only [Clif.evalInst, Clif.Frame.get] at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some a =>
    rw [hx] at h
    by_cases hlt : a.ty.width < ty.width
    · cases op <;> simp [Clif.Res.ofOption, bind, Clif.Res.bind, Clif.Res.check, hlt, pure] at h <;>
        obtain ⟨rfl, rfl⟩ := h <;> exact ⟨a, rfl, hlt, rfl, rfl⟩
    · simp [Clif.Res.ofOption, bind, Clif.Res.bind, Clif.Res.check, hlt] at h

/-! ## Forward lemmas -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_ext {r : Rule} (hr : r = rule_lower_1261 ∨ r = rule_lower_1315) {ko : Nat}
    (hko : r = rule_lower_1261 ∧ ko = 141 ∨ r = rule_lower_1315 ∧ ko = 142)
    {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64) {t : CTy}
    (hT : ctx.valueType? x = some t) (hd : info.data = .data 152 29 [.data 151 ko [], .value x]) :
    (matchRule p (sem ctx) cfg (n+10) r [.inst i]).run (st, tr) =
      .ok (some (envExt w x t), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_type ctx st hT
  clear hr
  rcases hko with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hp; isel_eval [*, rule_lower_1261]
  · cases hp; isel_eval [*, rule_lower_1315]

include hp in
theorem match_ext_none {r : Rule} {ko : Nat}
    (hko : r = rule_lower_1261 ∧ ko = 141 ∨ r = rule_lower_1315 ∧ ko = 142)
    {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hT : ctx.valueType? x = none) (hd : info.data = .data 152 29 [.data 151 ko [], .value x])
    (env : Interp.Env V) (s : LState × Array RuleId) :
    (matchRule p (sem ctx) cfg (n+10) r [.inst i]).run (st, tr) ≠ .ok (some env, s) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_type_none ctx st hT
  rcases hko with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hp; isel_eval [*, rule_lower_1261]; exact fun h => by cases h
  · cases hp; isel_eval [*, rule_lower_1315]; exact fun h => by cases h

include hp hc in
theorem rhs_ext {r : Rule} {sg : Bool}
    (hr : r = rule_lower_1261 ∧ sg = false ∨ r = rule_lower_1315 ∧ sg = true)
    {x w : Nat} {t : CTy} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) r.rhs (envExt w x t)).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx sg t.bits w), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a sg fb tb => extend_run hp ctx hc st tr n a sg fb tb
  have h4 := ctor_ty_bits_ty ctx
  have h5 := fun st => ctor_put_in_reg ctx st hx
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hp
    refine Exists.intro ?ew1 ?eh1
    case eh1 =>
      isel_eval [*, rule_lower_1261]
      rfl
  · cases hp
    refine Exists.intro ?ew2 ?eh2
    case eh2 =>
      isel_eval [*, rule_lower_1315]
      rfl

include hp in
theorem rhs_ext_none {r : Rule} (hr : r = rule_lower_1261 ∨ r = rule_lower_1315)
    {x w : Nat} {t : CTy} (hx : ctx.valueReg? x = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) r.rhs (envExt w x t)).run (st, tr) ≠ .ok (some v, s') := by
  have h4 := ctor_ty_bits_ty ctx
  rcases hr with rfl | rfl
  · cases hp; isel_eval [*, rule_lower_1261, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hp; isel_eval [*, rule_lower_1315, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h

end

/-! ## Meaning: the six widening pairs -/

theorem extend_sem {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {op : Clif.ExtendOp}
    {sg : Bool} (hsg : op = .uextend ∧ sg = false ∨ op = .sextend ∧ sg = true) {ty aty : Clif.Ty}
    (hety : eTy ty = true)
    (hlt : aty.width < ty.width) (b x : Nat) (ρ : Nat → CV) (u : BitVec aty.width)
    (hu : VHolds ⟨aty, u⟩ (ρ x)) :
    ∃ ρ', PRun F isem [.extend (.vreg b .int) (.vreg x .int) sg aty.width ty.width] ρ ρ' ∧
      VHolds ⟨ty, extVal_fb op ty u⟩ (ρ' b) := by
  have hu' : (ρ x).setWidth aty.width = u := hu
  subst hu'
  rcases hsg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  cases aty <;> cases ty <;> simp [eTy, Clif.Ty.width] at hety hlt <;>
    refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩ <;>
    simp only [VHolds, ofX, lo64, upd, ↓reduceIte, extVal_fb, Clif.Sem.uextend, Clif.Sem.sextend,
      Clif.Ty.width, Bool.false_eq_true] <;> bv_decide

/-! ## The rule theorems -/

theorem extend_rule_ok {p : Program} (hp : Data p) {r : Rule} {op : Clif.ExtendOp} {ko opT : Nat}
    {sg : Bool} (hcase : (r = rule_lower_1261 ∧ op = .uextend ∧ ko = 141 ∧ opT = 2425 ∧ sg = false) ∨
      (r = rule_lower_1315 ∧ op = .sextend ∧ ko = 142 ∧ opT = 2426 ∧ sg = true))
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hR : Refines F isem) (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p r := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  have hko : r = rule_lower_1261 ∧ ko = 141 ∨ r = rule_lower_1315 ∧ ko = 142 := by
    rcases hcase with ⟨h1, -, h2, -⟩ | ⟨h1, -, h2, -⟩ <;> simp [h1, h2]
  have hr' : r = rule_lower_1261 ∧ sg = false ∨ r = rule_lower_1315 ∧ sg = true := by
    rcases hcase with ⟨h1, -, -, -, h2⟩ | ⟨h1, -, -, -, h2⟩ <;> simp [h1, h2]
  have hr2 : r = rule_lower_1261 ∨ r = rule_lower_1315 := by
    rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  obtain ⟨info', fs, hi', hd⟩ : ∃ info' fs, ctx.insts[ii]? = some info' ∧
      info'.data = .data 152 29 (.data 151 ko [] :: fs) := by
    rcases hcase with ⟨rfl, -, rfl, rfl, -⟩ | ⟨rfl, -, rfl, rfl, -⟩
    · exact root_match_data hp ctx (r := rule_lower_1261) rfl hp.t2476 term_2476_kind hp.t2425
        term_2425_kind (m := m' + 9) hmatch
    · exact root_match_data hp ctx (r := rule_lower_1315) rfl hp.t2476 term_2476_kind hp.t2426
        term_2426_kind (m := m' + 9) hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [variantNames_Unary] at hf
  have hnm : instNames inst = ("Unary", if op == .uextend then "Uextend" else "Sextend") := by
    rcases hcase with ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, -⟩
    · rw [variantNames_Uextend] at ho
      exact Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
    · rw [variantNames_Sextend] at ho
      exact Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, x, rfl⟩ := instNames_extend hnm
  obtain ⟨hety, rfl⟩ := instData_extend hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by rw [hres]; simp [ofClif_int_width]
  have hw := eTy_width hety
  cases hT : ctx.valueType? x with
  | none => exact absurd hmatch (match_ext_none hp ctx st tr m' hko hi hhead hw hT hd _ _)
  | some t =>
  rw [match_ext hp ctx st tr m' hr2 hko hi hhead hw hT hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_ext_none hp ctx st tr n' hr2 hrx out (st', tr'))
  | some rx =>
  have ex := hctx.valueReg x rx hrx
  subst ex
  have hxlt := hvb x _ hrx
  obtain ⟨tr'', h⟩ := rhs_ext hp ctx hco st tr n' hr' hrx (w := ty.width) (t := t)
  rw [h] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨[.extend (.vreg st.nextVreg .int) (.vreg x .int) sg t.bits ty.width], _,
    by simp [LState.emit, LState.fresh], rfl, ?_⟩
  refine lowerInstOk_one_fb hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro mi hmi d hd'
    simp only [List.mem_singleton] at hmi; subst hmi
    rw [vdd_extend, List.mem_singleton] at hd'; subst hd'
    simp [LState.emit, LState.fresh]
  intro fr cm ρ vals cm' _ hvals hdfg ho
  obtain ⟨a, ha, hlt, rfl, rfl⟩ := evalInst_extend_ok ho
  have ht : t = .int a.ty.width := by rw [← hdfg.2 x t a hT ha, ofClif_int_width]
  subst ht
  obtain ⟨aty, u⟩ := a
  have hsg : op = .uextend ∧ sg = false ∨ op = .sextend ∧ sg = true := by
    rcases hcase with ⟨-, h1, -, -, h2⟩ | ⟨-, h1, -, -, h2⟩ <;> simp [h1, h2]
  obtain ⟨ρ', hrun, hheld⟩ := extend_sem hR hsg hety hlt st.nextVreg x ρ u (hvals x _ ha)
  refine ⟨rfl, usesOk_of [x] ?_ (by simp [ha]), .inl (Nat.le_refl _), _, ρ', rfl, hrun, hheld⟩
  intro mi hmi u hu
  simp only [List.mem_singleton] at hmi; subst hmi
  rw [vdu_extend, List.mem_singleton] at hu
  exact .inr (by simp [hu])

include hp in
/-- **`uextend`** (`lower.isle:1261`), to i16..i64: one `uxtb`/`uxth`/`mov w` (`Extend`). -/
theorem uextend_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1261 :=
  extend_rule_ok hp (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) F isem MR env cp hR hMR

include hp in
/-- **`sextend`** (`lower.isle:1315`), to i16..i64: one `sxtb`/`sxth`/`sxtw` (`Extend`). -/
theorem sextend_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1315 :=
  extend_rule_ok hp (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) F isem MR env cp hR hMR

end Backend.Proof
