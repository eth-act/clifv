module

public import FV.Backend.Proof.IselEmitTDefs
public import FV.Backend.Proof.IselEmitTFns
public import FV.Backend.Proof.IselEmitHand
public import FV.Backend.Proof.IselFamALUATI
public import FV.Backend.Proof.IselFloatBitcast

@[expose] public section

/-!
# Emission conditions of the typed ISLE lowering (S11): the hand-checked root rules

The root rules of `lower` the typed emission analysis does not check (`CovT.emitHandIdsT`) emit
one instruction with the emission conditions and no branch targets (`hand_emitT`):

* `uextend`/`sextend` (808, 819), `extr_32_or_64` (862, 863): `IselEmitHand` over float-capable
  contexts (`CtxInvT`): an extend's operand is in an integer position (`CtxInvT.intOps`), the
  `extr` inversions are `binary_root_invTI`/`ctxInv_clifTI`;
* `bitcast` GPR → SIMD&FP (1083): `mov_to_fpu` of the operand at its scalar size; by
  `BitcastsSameWidth` the operand is an `i32`/`i64` (the result is an `f32`/`f64`), so the size
  is `Size32`/`Size64` (`bitcast_emitT`; the inversion is `bitcast_gpr_fp_okT`'s).

A right-hand side that evaluates to `none` does not exist (`totality`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000

/-! ## `uextend`/`sextend` (808, 819) -/

theorem extend_emitT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hW : ExtendsWiden ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hic : info.clif = some inst) {r : Rule} {op : Clif.ExtendOp} {ko opT : Nat} {sg : Bool}
    (hcase : (r = rule_lower_1261 ∧ op = .uextend ∧ ko = 141 ∧ opT = 2425 ∧ sg = false) ∨
      (r = rule_lower_1315 ∧ op = .sextend ∧ ko = 142 ∧ opT = 2426 ∧ sg = true))
    {cfg : Config} (hco : cfg.checkOverlap = false) {m n : Nat} {s0 st : LState} {tr : Array RuleId}
    {env' : Interp.Env V} {s1 : LState × Array RuleId} {out : Option V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hE : EmSince s0 st)
    (hmatch : (matchRule program (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1))
    (heval : (evalExpr program (sem ctx) cfg n r.rhs env').run s1 = .ok (out, (st', tr'))) :
    EmSince s0 st' := by
  have hp := data_program
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  have hko : r = rule_lower_1261 ∧ ko = 141 ∨ r = rule_lower_1315 ∧ ko = 142 := by
    rcases hcase with ⟨h1, -, h2, -⟩ | ⟨h1, -, h2, -⟩ <;> simp [h1, h2]
  have hr' : r = rule_lower_1261 ∧ sg = false ∨ r = rule_lower_1315 ∧ sg = true := by
    rcases hcase with ⟨h1, -, -, -, h2⟩ | ⟨h1, -, -, -, h2⟩ <;> simp [h1, h2]
  have hr2 : r = rule_lower_1261 ∨ r = rule_lower_1315 := by
    rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have htot : totalE program r.rhs = true := by
    rcases hr2 with rfl | rfl
    · exact total_1261
    · exact total_1315
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
  obtain ⟨t, hT, hlt⟩ := hW ii info op ty x hi hic
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width (isInt_of_eTy hety)]
  have hw := eTy_width hety
  rw [match_ext hp ctx st tr m' hr2 hko hi hhead hw hT hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none =>
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp (totality.1 ctx cfg _ _ _ _ _ _ htot heval)
    exact absurd heval (rhs_ext_none hp ctx st tr n' hr2 hrx v (st', tr'))
  | some rx =>
  obtain ⟨tr'', h⟩ := rhs_ext hp ctx hco st tr n' hr' hrx (w := ty.width) (t := t)
  rw [h] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq] at heval
  obtain ⟨-, rfl, -⟩ := heval
  rw [ofClif_int_width (isInt_of_eTy hety)] at hlt
  exact emSince_emit hE (extend_emitOk (hctx.intOps ii info _ hi hic x (by simp [intArgs]) t hT) hlt hw _ _ _) rfl

/-! ## `extr_32_or_64` (862, 863) -/

theorem extr_emitT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} (hco : cfg.checkOverlap = false) {m n : Nat} {s0 st : LState} {tr : Array RuleId}
    {env' : Interp.Env V} {s1 : LState × Array RuleId} {out : Option V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hE : EmSince s0 st)
    (hmatch : (matchRule program (sem ctx) cfg m rule_lower_1501 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr program (sem ctx) cfg n rule_lower_1501.rhs env').run s1 =
      .ok (out, (st', tr'))) :
    EmSince s0 st' := by
  have hp := data_program
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, a, b, e0, e1, rfl, hd, hhead, -, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 19) (cop := .bor) rfl hp.t2382 term_2382_kind
      variantNames_Bor rfl hmatch
  cases Classical.em (ty.width = 32 ∨ ty.width = 64) with
  | inr hnw => rw [match_1501_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clifTI hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, x, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clifTI hctx hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty3, k3, rfl, rfl⟩ := instData_iconst_inv hdat2
  have he3 := instData_iconst_eTy hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := ctxInv_clifTI hctx hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, y, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := ctxInv_clifTI hctx hj4 hij4
  rw [hd4] at hdat4
  obtain ⟨ty4, k4, rfl, rfl⟩ := instData_iconst_inv hdat4
  have he4 := instData_iconst_eTy hdat4
  cases Classical.em (ExtrOk ty.width (u64 (imm64OfIconst ty3 k3)) (u64 (imm64OfIconst ty4 k4))) with
  | inr hnok =>
    rw [match_1501_none hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4
      hd4 hnok] at hmatch
    cases hmatch
  | inl hok =>
  rw [match_1501 hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4 hd4
    hok] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨hsum, hXp, -, hY64, -, -⟩ := extrOk_nat (by omega) hok
  cases hrx : ctx.valueReg? x with
  | none =>
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp (totality.1 ctx cfg _ _ _ _ _ _ total_1501 heval)
    exact absurd heval (rhs_1501_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none =>
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp (totality.1 ctx cfg _ _ _ _ _ _ total_1501 heval)
    exact absurd heval (rhs_1501_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain ⟨tr'', sh, hsh, he'⟩ := rhs_1501 hp ctx hco st tr n' hrx hry hw hY64
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq] at heval
  obtain ⟨-, rfl, -⟩ := heval
  exact emSince_emit hE (extr_emitOk hw (sh := sh) (by omega) _ _ _) rfl

theorem extr2_emitT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} (hco : cfg.checkOverlap = false) {m n : Nat} {s0 st : LState} {tr : Array RuleId}
    {env' : Interp.Env V} {s1 : LState × Array RuleId} {out : Option V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hE : EmSince s0 st)
    (hmatch : (matchRule program (sem ctx) cfg m rule_lower_1507 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr program (sem ctx) cfg n rule_lower_1507.rhs env').run s1 =
      .ok (out, (st', tr'))) :
    EmSince s0 st' := by
  have hp := data_program
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, a, b, e0, e1, rfl, hd, hhead, -, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 19) (cop := .bor) rfl hp.t2382 term_2382_kind
      variantNames_Bor rfl hmatch
  cases Classical.em (ty.width = 32 ∨ ty.width = 64) with
  | inr hnw => rw [match_1507_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clifTI hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, y, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clifTI hctx hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty4, k4, rfl, rfl⟩ := instData_iconst_inv hdat2
  have he4 := instData_iconst_eTy hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := ctxInv_clifTI hctx hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, x, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := ctxInv_clifTI hctx hj4 hij4
  rw [hd4] at hdat4
  obtain ⟨ty3, k3, rfl, rfl⟩ := instData_iconst_inv hdat4
  have he3 := instData_iconst_eTy hdat4
  cases Classical.em (ExtrOk ty.width (u64 (imm64OfIconst ty3 k3)) (u64 (imm64OfIconst ty4 k4))) with
  | inr hnok =>
    rw [match_1507_none hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4
      hd4 hnok] at hmatch
    cases hmatch
  | inl hok =>
  rw [match_1507 hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4 hd4
    hok] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨hsum, hXp, -, hY64, -, -⟩ := extrOk_nat (by omega) hok
  cases hrx : ctx.valueReg? x with
  | none =>
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp (totality.1 ctx cfg _ _ _ _ _ _ total_1507 heval)
    exact absurd heval (rhs_1507_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none =>
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp (totality.1 ctx cfg _ _ _ _ _ _ total_1507 heval)
    exact absurd heval (rhs_1507_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain ⟨tr'', sh, hsh, he'⟩ := rhs_1507 hp ctx hco st tr n' hrx hry hw hY64
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq] at heval
  obtain ⟨-, rfl, -⟩ := heval
  exact emSince_emit hE (extr_emitOk hw (sh := sh) (by omega) _ _ _) rfl

/-! ## `bitcast` GPR → SIMD&FP (1083) -/

theorem total_2793 : totalE program rule_lower_2793.rhs = true := by decide

/-- An emitted instruction with the emission conditions and no targets keeps `EmSince`. -/
theorem emSince_push' {s0 s s' : LState} (h : EmSince s0 s) {mi : MInst}
    (he : s'.emitted = s.emitted.push mi) (hm : mi.emitOk = true) (ht : mi.targets = []) :
    EmSince s0 s' := by
  obtain ⟨ms, h1, h2⟩ := h
  refine ⟨ms ++ [mi], by rw [he, h1]; simp, fun m' hm' => ?_⟩
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact h2 m' hm'
  · simp only [List.mem_singleton] at hm'; subst hm'; exact ⟨hm, ht⟩

set_option maxHeartbeats 8000000 in
/-- **`bitcast` GPR → SIMD&FP** (`rule_lower_2793`): the `fmov s/d, w/x` of an `i32`/`i64`
operand (`BitcastsSameWidth`) has the emission conditions. -/
theorem bitcast_emitT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hB : BitcastsSameWidth ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst)
    {cfg : Config} (hco : cfg.checkOverlap = false) {m n : Nat} {s0 st : LState} {tr : Array RuleId}
    {env' : Interp.Env V} {s1 : LState × Array RuleId} {out : Option V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hE : EmSince s0 st)
    (hmatch : (matchRule program (sem ctx) cfg m rule_lower_2793 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr program (sem ctx) cfg n rule_lower_2793.rhs env').run s1 =
      .ok (out, (st', tr'))) :
    EmSince s0 st' := by
  obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
    (totality.1 ctx cfg _ _ _ _ _ _ total_2793 heval)
  have hp := data_program
  have hK : KeepEq st.nextVreg st.nextVreg := rfl
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, fl, x, rfl, hd⟩ := bitcast_front hp hctx hi hic rfl (m := m' + 9) hmatch
  have hp' := hp
  isel_inv' hp [ext_ty_float_or_vec_iff, ctor_ty_int_ref_scalar_64_iff] at hmatch heval
  obtain ⟨d0, hd0⟩ : ∃ d0, KeepEq _ d0 := ⟨_, ‹KeepEq _ _›⟩
  unfold KeepEq at hd0
  obtain ⟨rfl, rfl, rfl⟩ := bitcast_data_eq hi hd ‹ctx.insts[ii]? = some _› ‹V.data 152 17 _ = _›
  obtain ⟨t, ht, htw⟩ := (ext_value_type_iff ctx _ x _).mp ‹externExtract ctx T.value_type _ _ = _›
  simp only [List.cons.injEq, and_true] at htw
  subst htw
  obtain ⟨hint, rfl, rfl⟩ :=
    (ctor_ty_int_ref_scalar_64_iff ctx _ t _ _).mp ‹externCtor ctx T.ty_int_ref_scalar_64 _ _ = _›
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ x _ _).mp ‹externCtor ctx T.put_in_reg _ _ = _›
  obtain ⟨w, rfl, hw⟩ : ∃ w, t = .int w ∧ (w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) := by
    rcases mCTys_cases (hctx.valTyM x t ht) with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ⟨_, rfl, by decide⟩ | (simp [CTy.isFloat] at hint)
  have hpos : IntPos ctx x := fun t' ht' => by
    rw [ht] at ht'
    cases ht'
    rcases hw with rfl | rfl | rfl | rfl <;> simp [eCTys]
  obtain rfl := hctx.valueReg_int hrx hpos
  have h1 := ‹ApplyInternal _ _ _ _ 95 307 _ _ _ _›
  obtain ⟨rfl, hs1⟩ := scalar_size_int_ok hp' hco (by omega) hw h1
  have h2 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
  obtain ⟨k', hk', rfl, m1, hm1, hs2⟩ := mov_to_fpu_any_ok hp' hco (by omega) h2
  have h3 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp' hco (by omega) h3
  try simp only at hs1 hs3
  rw [hs1] at hs2 hm1
  rw [hs2] at hs3
  subst hs3
  simp only [LState.fresh, hd0] at hm1
  have hk3 : k' ≤ 3 := by
    rcases hk' with rfl | ⟨-, rfl⟩
    · unfold szIdxOf; repeat' split
      all_goals omega
    · omega
  obtain ⟨sz, rfl, hsz2, hsz3⟩ := ofV_movToFpu hk3 hm1
  have hfv : ((CTy.ofClif ty).isFloat || (CTy.ofClif ty).isVector) = true := by
    rw [← bitcast_resTy hctx hi hic]; assumption
  obtain ⟨t', ht', hbits⟩ := hB ii _ ty fl x hi hic
  rw [ht] at ht'
  cases ht'
  refine emSince_push' hE (mi := .movToFpu (.vreg d0 .float) (.vreg x .int) sz)
    (by simp [LState.emit, LState.fresh]) ?_ rfl
  rcases ofClif_float_or_vec hfv with rfl | rfl
  · have hw32 : w = 32 := by simpa [CTy.ofClif, CTy.bits] using hbits
    subst hw32
    obtain rfl := hsz2 (by rcases hk' with h | ⟨h, -⟩ <;> simp [szIdxOf] at h <;> omega)
    rfl
  · have hw64 : w = 64 := by simpa [CTy.ofClif, CTy.bits] using hbits
    subst hw64
    obtain rfl := hsz3 (by rcases hk' with h | ⟨h, -⟩ <;> simp [szIdxOf] at h <;> omega)
    rfl

/-! ## The five rules -/

/-- The `k`-th rule of `lower`, by evaluation of the rule data. -/
local macro "lowerData" : term =>
  `((by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl))

/-- **The hand-checked root rules of `lower` (`CovT.emitHandIdsT`) emit only instructions with the
emission conditions and no branch targets.** -/
theorem hand_emitT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hW : ExtendsWiden ctx)
    (hB : BitcastsSameWidth ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower)
    (hid : CovT.emitHandIdsT.contains rl.id = true) :
    ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (m n : Nat) (s0 s : LState) (tr : Array RuleId)
      (env : Isle.Interp.Env V) (s1 : LState × Array RuleId) (r : Option V) (s2 : LState)
      (tr2 : Array RuleId), 1000 ≤ m → 1000 ≤ n → EmSince s0 s →
      (matchRule program (sem ctx) cfg m rl [.inst ii]).run (s, tr) = .ok (some env, s1) →
      (evalExpr program (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → EmSince s0 s2 := by
  intro cfg hco m n s0 s tr env s1 r s2 tr2 hm hn hE hmatch heval
  simp only [CovT.emitHandIdsT, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at hid
  rcases hid with h | h | h | h | h
  · obtain rfl := lower_rule_eq hrl (k := 459) (r0 := rule_lower_1261) lowerData
      (by rw [h]; rfl)
    exact extend_emitT hctx hW hi hc (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hco hm hn hE hmatch heval
  · obtain rfl := lower_rule_eq hrl (k := 500) (r0 := rule_lower_1315) lowerData
      (by rw [h]; rfl)
    exact extend_emitT hctx hW hi hc (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hco hm hn hE hmatch heval
  · obtain rfl := lower_rule_eq hrl (k := 19) (r0 := rule_lower_1501) lowerData
      (by rw [h]; rfl)
    exact extr_emitT hctx hi hc hco hm hn hE hmatch heval
  · obtain rfl := lower_rule_eq hrl (k := 20) (r0 := rule_lower_1507) lowerData
      (by rw [h]; rfl)
    exact extr2_emitT hctx hi hc hco hm hn hE hmatch heval
  · obtain rfl := lower_rule_eq hrl (k := 30) (r0 := rule_lower_2793) lowerData
      (by rw [h]; rfl)
    exact bitcast_emitT hctx hB hi hc hco hm hn hE hmatch heval

end Backend.Proof.Driver
