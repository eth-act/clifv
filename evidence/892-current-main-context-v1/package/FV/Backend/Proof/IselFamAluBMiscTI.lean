import FV.Backend.Proof.IselFamAluBMisc
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamAluBBaseTI

/-!
# `IselFamAluBMisc` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBMisc`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
include hp in
/-- **`bnot_base_case`** (`lower.isle:1377`), i8..i64: `orn wd, wzr, wn` / `orn xd, xzr, xn`. -/
theorem bnot_base_case_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1377 :=
  unary_ruleOkTI hp (cop := .bnot) rfl hp.t2384 term_2384_kind variantNames_Bnot rfl
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
        generalize hs : szOf (Clif.Ty.width ty) = sz at *
        cases ty <;> simp [eTy] at hety <;> simp [szOf, Clif.Ty.width] at hs <;> subst hs <;>
          simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary,
            Clif.Sem.bnot] at * <;>
          dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
          (try unfold OperandSize.bits Clif.Ty.width at *) <;>
          apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
          repeat (first | omega | (rcases i with _ | i; · simp))⟩)

section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
set_option maxRecDepth 20000 in
include hp in
/-- **`nop`** (`lower.isle:78`): no code, no results. -/
theorem nop_okTI (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) :
    LowerRuleOkTI isem MR env cp p rule_lower_78 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn _ _ hmatch
      heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
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

section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
include hp in
/-- **`ireduce`** (`lower.isle:2146`), to i8..i64: no code, the operand's vreg. -/
theorem ireduce_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2146 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
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
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width (isInt_of_eTy hety)]
  have hw := eTy_width hety
  rw [match_2146 hp ctx st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_2146_none hp ctx st tr n' hrx out (st', tr'))
  | some rx =>
  have ex := hctx.valueRegI x rx hrx
  subst ex
  obtain ⟨tr'', h⟩ := rhs_2146 hp ctx hco st tr n' hrx
  rw [h] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨[], _, by simp, rfl, ?_⟩
  refine lowerInstOk_one_fb (d := x) hMR (Nat.le_refl _) (fun _ h => by cases h) rfl ?_
  intro fr cm ρ vals cm' _ hvals _ ho
  obtain ⟨a, ha, hlt, rfl, rfl⟩ := evalInst_ireduce_ok ho
  refine ⟨rfl, (fun _ h => by cases h), .inr (by simp [ha]), _, ρ, rfl, prun_nil _, ?_⟩
  have hv := hvals x a ha
  simp only [VHolds] at hv ⊢
  simp only [Clif.Sem.ireduce]
  rw [← hv, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hlt)]

end Backend.Proof
