import FV.Backend.Proof.IselFamAluBExtend
import FV.Backend.Proof.IselBaseTI

/-!
# `IselFamAluBExtend` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBExtend`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
theorem extend_rule_okTI {p : Program} (hp : Data p) {r : Rule} {op : Clif.ExtendOp} {ko opT : Nat}
    {sg : Bool} (hcase : (r = rule_lower_1261 ∧ op = .uextend ∧ ko = 141 ∧ opT = 2425 ∧ sg = false) ∨
      (r = rule_lower_1315 ∧ op = .sextend ∧ ko = 142 ∧ opT = 2426 ∧ sg = true))
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hR : Refines F isem) (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p r := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
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
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width (isInt_of_eTy hety)]
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
  have ex := hctx.valueRegI x rx hrx
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
  have ht : t = .int a.ty.width := by
    have hta := hdfg.2 x t a hT ha
    rw [← hta, ofClif_int_width (isInt_of_ofClif_mem (hta ▸ hctx.valTyEI x t hT))]
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
theorem uextend_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1261 :=
  extend_rule_okTI hp (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) F isem MR env cp hR hMR

include hp in
/-- **`sextend`** (`lower.isle:1315`), to i16..i64: one `sxtb`/`sxth`/`sxtw` (`Extend`). -/
theorem sextend_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1315 :=
  extend_rule_okTI hp (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) F isem MR env cp hR hMR

end Backend.Proof
