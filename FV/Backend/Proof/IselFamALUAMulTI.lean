import FV.Backend.Proof.IselFamALUAMul
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamALUATI

/-!
# `IselFamALUAMul` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamALUAMul`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
/-- A `binary` instruction whose first result type is `.int ty.width` has an integer type. -/
theorem binary_isIntTI {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {op : Clif.BinaryOp} {ty : Clif.Ty} {x y : Nat} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some (.binary op ty x y)) (hhead : info.resTys.head? = some (.int ty.width)) :
    ty.isInt = true := by
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hhead
  exact (ofClif_eq_int (by simpa using hhead)).1

set_option maxRecDepth 20000 in
/-- **`smulhi_64`** (`lower.isle:1056`, `smulhi.i64 x y` → `smulh`). -/
theorem smulhi_64_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1056 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, -, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .smulhi) rfl hp.t2363 term_2363_kind
      variantNames_Smulhi rfl hmatch
  by_cases h64 : ty.width ≠ 64
  · rw [match_1056_ne hp ctx st tr m' hi hhead h64 hd] at hmatch; cases hmatch
  obtain rfl := ty_i64_of_width (Decidable.of_not_not h64) (binary_isIntTI hctx hi hc hhead)
  rw [match_1056 hp ctx st tr m' hi hhead hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_1056_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_1056_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI y ry hry
  obtain ⟨tr'', he⟩ := rhs_1056 hp ctx hco st tr n' hrx hry
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals _ u v hx hy => ?_
  refine ⟨fun z hz => ?_, _, rfl, smulh_holds (hvals x _ (getAs_ok hx)) (hvals y _ (getAs_ok hy))⟩
  rw [vuseNums_aluRRR] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl
  · exact getAs_isSome hx
  · exact getAs_isSome hy

set_option maxRecDepth 20000 in
/-- **`umulhi_64`** (`lower.isle:1068`, `umulhi.i64 x y` → `umulh`). -/
theorem umulhi_64_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1068 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, -, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .umulhi) rfl hp.t2362 term_2362_kind
      variantNames_Umulhi rfl hmatch
  by_cases h64 : ty.width ≠ 64
  · rw [match_1068_ne hp ctx st tr m' hi hhead h64 hd] at hmatch; cases hmatch
  obtain rfl := ty_i64_of_width (Decidable.of_not_not h64) (binary_isIntTI hctx hi hc hhead)
  rw [match_1068 hp ctx st tr m' hi hhead hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_1068_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_1068_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI y ry hry
  obtain ⟨tr'', he⟩ := rhs_1068 hp ctx hco st tr n' hrx hry
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals _ u v hx hy => ?_
  refine ⟨fun z hz => ?_, _, rfl, umulh_holds (hvals x _ (getAs_ok hx)) (hvals y _ (getAs_ok hy))⟩
  rw [vuseNums_aluRRR] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl
  · exact getAs_isSome hx
  · exact getAs_isSome hy

/-- **`imul_base_case`** (`lower.isle:871`, `imul x y` → `madd x, y, xzr`), i8..i64. -/
theorem imul_base_case_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_871 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, -, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .imul) rfl hp.t2361 term_2361_kind
      variantNames_Imul rfl hmatch
  rw [match_871 hp ctx st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_871_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_871_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI y ry hry
  obtain ⟨tr'', he⟩ := rhs_871 hp ctx hco st tr n' hrx hry hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals _ u v hx hy => ?_
  refine ⟨fun z hz => ?_, _, ispec_aluRRRR_xzr rfl,
    holds_mul0 (szOf_bits hw) (hvals x _ (getAs_ok hx)) (hvals y _ (getAs_ok hy))⟩
  rw [vuseNums_aluRRRR_xzr] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl
  · exact getAs_isSome hx
  · exact getAs_isSome hy

/-- **`iadd_imul_right`** (`lower.isle:125`, `iadd x (imul y z)` → `madd y, z, x`), i8..i64. -/
theorem iadd_imul_right_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_125 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2361 term_2361_kind hpy
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdatj
  obtain ⟨ty1, a, b, rfl, -, rfl⟩ := instData_binary_inv variantNames_Imul (cop := .imul) rfl hdatj
  rw [match_125 hp ctx st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_125_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hra : ctx.valueReg? a with
  | none => exact absurd heval (rhs_125_none hp ctx st tr n' (.inr (.inl hra)) _ _)
  | some ra =>
  cases hrb : ctx.valueReg? b with
  | none => exact absurd heval (rhs_125_none hp ctx st tr n' (.inr (.inr hrb)) _ _)
  | some rb =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI a ra hra
  obtain rfl := hctx.valueRegI b rb hrb
  obtain ⟨tr'', he⟩ := rhs_125 hp ctx hco st tr n' hrx hra hrb hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨u', w', ha, hb, rfl⟩ := binary_value hdfg hj hij hcl rfl hy
  refine ⟨fun z hz => ?_, _, ispec_aluRRRR rfl,
    holds_madd (szOf_bits hw) (hvals a _ (getAs_ok ha)) (hvals b _ (getAs_ok hb))
      (hvals x _ (getAs_ok hx))⟩
  rw [vuseNums_aluRRRR] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact getAs_isSome ha
  · exact getAs_isSome hb
  · exact getAs_isSome hx

/-- **`iadd_imul_left`** (`lower.isle:128`, `iadd (imul x y) z` → `madd x, y, z`), i8..i64. -/
theorem iadd_imul_left_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_128 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2361 term_2361_kind hpx
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdatj
  obtain ⟨ty1, a, b, rfl, -, rfl⟩ := instData_binary_inv variantNames_Imul (cop := .imul) rfl hdatj
  rw [match_128 hp ctx st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hra : ctx.valueReg? a with
  | none => exact absurd heval (rhs_128_none hp ctx st tr n' (.inl hra) _ _)
  | some ra =>
  cases hrb : ctx.valueReg? b with
  | none => exact absurd heval (rhs_128_none hp ctx st tr n' (.inr (.inl hrb)) _ _)
  | some rb =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_128_none hp ctx st tr n' (.inr (.inr hry)) _ _)
  | some ry =>
  obtain rfl := hctx.valueRegI a ra hra
  obtain rfl := hctx.valueRegI b rb hrb
  obtain rfl := hctx.valueRegI y ry hry
  obtain ⟨tr'', he⟩ := rhs_128 hp ctx hco st tr n' hra hrb hry hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨u', w', ha, hb, rfl⟩ := binary_value hdfg hj hij hcl rfl hx
  refine ⟨fun z hz => ?_, _, ispec_aluRRRR rfl, ?_⟩
  · rw [vuseNums_aluRRRR] at hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact getAs_isSome ha
    · exact getAs_isSome hb
    · exact getAs_isSome hy
  · have := holds_madd (szOf_bits hw) (hvals a _ (getAs_ok ha)) (hvals b _ (getAs_ok hb))
      (hvals y _ (getAs_ok hy))
    show VHolds ⟨ty, u' * w' + v⟩ _
    rwa [BitVec.add_comm]

/-- **`isub_imul`** (`lower.isle:132`, `isub x (imul y z)` → `msub y, z, x`), i8..i64. -/
theorem isub_imul_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_132 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2361 term_2361_kind hpy
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdatj
  obtain ⟨ty1, a, b, rfl, -, rfl⟩ := instData_binary_inv variantNames_Imul (cop := .imul) rfl hdatj
  rw [match_132 hp ctx st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_132_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hra : ctx.valueReg? a with
  | none => exact absurd heval (rhs_132_none hp ctx st tr n' (.inr (.inl hra)) _ _)
  | some ra =>
  cases hrb : ctx.valueReg? b with
  | none => exact absurd heval (rhs_132_none hp ctx st tr n' (.inr (.inr hrb)) _ _)
  | some rb =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI a ra hra
  obtain rfl := hctx.valueRegI b rb hrb
  obtain ⟨tr'', he⟩ := rhs_132 hp ctx hco st tr n' hrx hra hrb hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨u', w', ha, hb, rfl⟩ := binary_value hdfg hj hij hcl rfl hy
  refine ⟨fun z hz => ?_, _, ispec_aluRRRR rfl,
    holds_msub (szOf_bits hw) (hvals a _ (getAs_ok ha)) (hvals b _ (getAs_ok hb))
      (hvals x _ (getAs_ok hx))⟩
  rw [vuseNums_aluRRRR] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact getAs_isSome ha
  · exact getAs_isSome hb
  · exact getAs_isSome hx

end Backend.Proof
