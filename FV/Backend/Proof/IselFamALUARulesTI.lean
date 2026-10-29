module

public import FV.Backend.Proof.IselFamALUARules
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamALUATI

@[expose] public section

/-!
# `IselFamALUARules` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamALUARules`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
/-- **`iadd_imm12_right`** (`lower.isle:90`, `iadd x (iconst k)` with `k` an `Imm12` →
`add x, #k`), i8..i64. -/
theorem iadd_imm12_right_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_90 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, hfs⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨imm, himm, -⟩ := imm12_args_inv hp ctx hfs
  rw [match_90 hp ctx hi hhead hw hd hj hij hdj himm st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_90_none hp ctx hrx st tr n' out (st', tr'))
  | some rx =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain ⟨tr'', he⟩ := rhs_90 hp ctx hco hrx hw st tr n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨hiv, hib⟩ := iconst_imm12 hdfg hw hj hij hcl hy himm
  refine ⟨fun z hz => ?_, (imm12_sem (szOf_bits hw) hiv hib (hvals x _ (getAs_ok hx)) w).1⟩
  rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
  subst hz
  simp [getAs_ok hx]

/-- **`iadd_imm12_left`** (`lower.isle:93`, `iadd (iconst k) y` → `add y, #k`), i8..i64. -/
theorem iadd_imm12_left_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_93 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, hfs⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpx
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨imm, himm, -⟩ := imm12_args_inv hp ctx hfs
  rw [match_93 hp ctx hi hhead hw hd hj hij hdj himm st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_93_none hp ctx hry st tr n' out (st', tr'))
  | some ry =>
  obtain rfl := hctx.valueRegI y ry hry
  obtain ⟨tr'', he⟩ := rhs_93 hp ctx hco hry hw st tr n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨hiv, hib⟩ := iconst_imm12 hdfg hw hj hij hcl hx himm
  obtain ⟨res, hs, hh⟩ := (imm12_sem (szOf_bits hw) hiv hib (hvals y _ (getAs_ok hy)) w).1
  refine ⟨fun z hz => ?_, res, hs, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hy]
  · show VHolds ⟨ty, u + v⟩ res
    rw [BitVec.add_comm]
    exact hh

/-- **`isub_imm12`** (`lower.isle:805`, `isub x (iconst k)` → `sub x, #k`), i8..i64. -/
theorem isub_imm12_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_805 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, hfs⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨imm, himm, -⟩ := imm12_args_inv hp ctx hfs
  rw [match_805 hp ctx hi hhead hw hd hj hij hdj himm st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_805_none hp ctx hrx st tr n' out (st', tr'))
  | some rx =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain ⟨tr'', he⟩ := rhs_805 hp ctx hco hrx hw st tr n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨hiv, hib⟩ := iconst_imm12 hdfg hw hj hij hcl hy himm
  refine ⟨fun z hz => ?_, (imm12_sem (szOf_bits hw) hiv hib (hvals x _ (getAs_ok hx)) w).2⟩
  rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
  subst hz
  simp [getAs_ok hx]

/-- **iadd_imm12_neg_right** (`lower.isle:98`, `iadd x (iconst k)` with `-k` an `Imm12` → `sub x, #-k`), i8..i64. -/
theorem iadd_imm12_neg_right_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_98 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, hil⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 39) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, hpy⟩ := values2_match_inv hp ctx hrest
  have he1 := matchPat_bind_wild_inv ctx hpy
  have he2 := matchPat_bind_wild_inv ctx hpx
  have hy : e1[2]? = some (some (.value y)) := getElem_bind_env (matchPat_bind_inv hpy).1 he1
  obtain ⟨v0, s2, happ⟩ := iflet_term_var_inv ctx (m := m' + 35) hil hy
  obtain ⟨j, infoj, ty', c, hj, hij, hcl, hdj, htyj⟩ :=
    negated_value_invTI hp ctx hctx hco (m := m' + 32) happ
  cases hneg : negImm12? ty'.width (imm64OfIconst ty' c) with
  | none =>
    rw [match_98_none hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
    cases hmatch
  | some imm =>
  rw [match_98 hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hr : ctx.valueReg? x with
  | none => exact absurd heval (rhs_98_none hp ctx hr st _ n' out (st', tr'))
  | some r =>
  obtain rfl := hctx.valueRegI x r hr
  obtain ⟨tr'', he⟩ := rhs_98 hp ctx hco hr hw st _ n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hy) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hib, hK⟩ := negImm12_value hw v (by unfold negImm12? at hneg; exact hneg)
  refine ⟨fun z hz => ?_, _, ispec_aluRRImm12_sub hib, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hx]
  · have := holds_sub_K (szOf_bits hw) (hK _ (szOf_bits hw)) (hvals x _ (getAs_ok hx))
    show VHolds ⟨ty, u + v⟩ _
    rwa [BitVec.sub_eq_add_neg, BitVec.neg_neg] at this

/-- **iadd_imm12_neg_left** (`lower.isle:102`, `iadd (iconst k) y` with `-k` an `Imm12` → `sub y, #-k`), i8..i64. -/
theorem iadd_imm12_neg_left_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_102 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, hil⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 39) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, hpy⟩ := values2_match_inv hp ctx hrest
  have he1 := matchPat_bind_wild_inv ctx hpy
  have he2 := matchPat_bind_wild_inv ctx hpx
  have hx : e1[1]? = some (some (.value x)) := by rw [getElem_bind_env_ne (by decide) he1]; exact getElem_bind_env (matchPat_bind_inv hpx).1 he2
  obtain ⟨v0, s2, happ⟩ := iflet_term_var_inv ctx (m := m' + 35) hil hx
  obtain ⟨j, infoj, ty', c, hj, hij, hcl, hdj, htyj⟩ :=
    negated_value_invTI hp ctx hctx hco (m := m' + 32) happ
  cases hneg : negImm12? ty'.width (imm64OfIconst ty' c) with
  | none =>
    rw [match_102_none hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
    cases hmatch
  | some imm =>
  rw [match_102 hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hr : ctx.valueReg? y with
  | none => exact absurd heval (rhs_102_none hp ctx hr st _ n' out (st', tr'))
  | some r =>
  obtain rfl := hctx.valueRegI y r hr
  obtain ⟨tr'', he⟩ := rhs_102 hp ctx hco hr hw st _ n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hx) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hib, hK⟩ := negImm12_value hw u (by unfold negImm12? at hneg; exact hneg)
  refine ⟨fun z hz => ?_, _, ispec_aluRRImm12_sub hib, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hy]
  · have := holds_sub_K (szOf_bits hw) (hK _ (szOf_bits hw)) (hvals y _ (getAs_ok hy))
    show VHolds ⟨ty, u + v⟩ _
    rwa [BitVec.sub_eq_add_neg, BitVec.neg_neg, BitVec.add_comm] at this

/-- **isub_imm12_neg** (`lower.isle:810`, `isub x (iconst k)` with `-k` an `Imm12` → `add x, #-k`), i8..i64. -/
theorem isub_imm12_neg_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_810 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, hil⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 39) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, hpx, hpy⟩ := values2_match_inv hp ctx hrest
  have he1 := matchPat_bind_wild_inv ctx hpy
  have he2 := matchPat_bind_wild_inv ctx hpx
  have hy : e1[2]? = some (some (.value y)) := getElem_bind_env (matchPat_bind_inv hpy).1 he1
  obtain ⟨v0, s2, happ⟩ := iflet_term_var_inv ctx (m := m' + 35) hil hy
  obtain ⟨j, infoj, ty', c, hj, hij, hcl, hdj, htyj⟩ :=
    negated_value_invTI hp ctx hctx hco (m := m' + 32) happ
  cases hneg : negImm12? ty'.width (imm64OfIconst ty' c) with
  | none =>
    rw [match_810_none hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
    cases hmatch
  | some imm =>
  rw [match_810 hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hr : ctx.valueReg? x with
  | none => exact absurd heval (rhs_810_none hp ctx hr st _ n' out (st', tr'))
  | some r =>
  obtain rfl := hctx.valueRegI x r hr
  obtain ⟨tr'', he⟩ := rhs_810 hp ctx hco hr hw st _ n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hy) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hib, hK⟩ := negImm12_value hw v (by unfold negImm12? at hneg; exact hneg)
  refine ⟨fun z hz => ?_, _, ispec_aluRRImm12_add hib, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hx]
  · have := holds_add_K (szOf_bits hw) (hK _ (szOf_bits hw)) (hvals x _ (getAs_ok hx))
    show VHolds ⟨ty, u - v⟩ _
    rwa [← BitVec.sub_eq_add_neg] at this

end Backend.Proof
