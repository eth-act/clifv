import FV.Backend.Proof.IselEmitDefs
import FV.Backend.Proof.IselEmitFns
import FV.Backend.Proof.IselLowerAll
import FV.Backend.Proof.IselShpTotal

/-!
# Emission conditions of the ISLE lowering (V6c): the hand-checked root rules

The root rules of `lower` the emission analysis does not check (`emitHandIds`) emit one
instruction with the emission conditions and no branch targets (`hand_emit`):
* `uextend`/`sextend` (808, 819): `Extend rd rn sg (ty_bits in) (ty_bits out)`, whose from-width
  is the operand's type (`i8..i64`, `CtxInv.valTyE`), narrower than the result type
  (`ExtendsWiden`): in the encoder's range (`extend_emitOk`);
* `extr_32_or_64` (862, 863): `AluRRRShift Extr` on I32/I64 by `ys`, `0 < ys < width` from the
  rule's guards `xs + ys = width`, `xs, ys > 0` (`extr_emitOk`).

The inversions are those of the correctness proofs (`extend_rule_ok`, `extr_32_or_64_ok`,
`extr_32_or_64_2_ok`); a right-hand side that evaluates to `none` does not exist (`totality`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64

/-! ## The emitted instructions -/

theorem emSince_emit {s0 s : LState} (h : EmSince s0 s) {mi : MInst} (hm : mi.emitOk = true)
    (ht : mi.targets = []) : EmSince s0 ((s.fresh .int).2.emit mi) := by
  obtain ⟨ms, he, hall⟩ := h
  refine ⟨ms ++ [mi], ?_, ?_⟩
  · rw [emitted_fresh_emit, he]; simp
  · intro m' hm'
    rcases List.mem_append.mp hm' with h | h
    · exact hall m' h
    · rw [List.mem_singleton.mp h]; exact ⟨hm, ht⟩

/-- A widening extension from an `i8..i64` type is in the encoder's range. -/
theorem extend_emitOk {t : CTy} (hE : t ∈ eCTys) {w : Nat} (hlt : t.bits < w) (hw : w ≤ 64)
    (rd rn : Reg) (sg : Bool) : (MInst.extend rd rn sg t.bits w).emitOk = true := by
  simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl <;> simp only [CTy.bits] at hlt ⊢ <;>
    cases sg <;> simp [MInst.emitOk, immOkB, MInst.noAlways] <;> (repeat' split) <;> omega

/-- An `extr` on I32/I64 by less than the width is in the encoder's range. -/
theorem extr_emitOk {w : Nat} (hw : w = 32 ∨ w = 64) {sh : ShiftOpAndAmt} (h : sh.amt < w)
    (rd rn rm : Reg) : (MInst.aluRRRShift .extr (szOf w) rd rn rm sh).emitOk = true := by
  rcases hw with rfl | rfl <;>
    simp [MInst.emitOk, immOkB, MInst.noAlways, szOf, OperandSize.is64, h]

/-! ## `uextend`/`sextend` (808, 819) -/

set_option maxRecDepth 100000
theorem total_1261 : totalE program rule_lower_1261.rhs = true := by decide
theorem total_1315 : totalE program rule_lower_1315.rhs = true := by decide
theorem total_1501 : totalE program rule_lower_1501.rhs = true := by decide
theorem total_1507 : totalE program rule_lower_1507.rhs = true := by decide

theorem extend_emit {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hW : ExtendsWiden ctx)
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
  have hhead : info.resTys.head? = some (.int ty.width) := by rw [hres]; simp [ofClif_int_width]
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
  rw [ofClif_int_width] at hlt
  exact emSince_emit hE (extend_emitOk (hctx.valTyE x t hT) hlt hw _ _ _) rfl

/-! ## `extr_32_or_64` (862, 863) -/

theorem extr_emit {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
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
    binary_root_inv hp hctx hi hc (m := m' + 19) (cop := .bor) rfl hp.t2382 term_2382_kind
      variantNames_Bor rfl hmatch
  cases Classical.em (ty.width = 32 ∨ ty.width = 64) with
  | inr hnw => rw [match_1501_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clif hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, x, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clif hctx hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty3, k3, rfl, rfl⟩ := instData_iconst_inv hdat2
  have he3 := instData_iconst_eTy hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := ctxInv_clif hctx hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, y, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := ctxInv_clif hctx hj4 hij4
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

theorem extr2_emit {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
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
    binary_root_inv hp hctx hi hc (m := m' + 19) (cop := .bor) rfl hp.t2382 term_2382_kind
      variantNames_Bor rfl hmatch
  cases Classical.em (ty.width = 32 ∨ ty.width = 64) with
  | inr hnw => rw [match_1507_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clif hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, y, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clif hctx hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty4, k4, rfl, rfl⟩ := instData_iconst_inv hdat2
  have he4 := instData_iconst_eTy hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := ctxInv_clif hctx hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, x, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := ctxInv_clif hctx hj4 hij4
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

/-! ## The four rules -/

/-- The `k`-th rule of `lower`, by evaluation of the rule data. -/
local macro "lowerData" : term =>
  `((by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl))

/-- **The hand-checked root rules of `lower` (`emitHandIds`) emit only instructions with the
emission conditions and no branch targets.** -/
theorem hand_emit {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hW : ExtendsWiden ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower)
    (hid : emitHandIds.contains rl.id = true) :
    ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (m n : Nat) (s0 s : LState) (tr : Array RuleId)
      (env : Isle.Interp.Env V) (s1 : LState × Array RuleId) (r : Option V) (s2 : LState)
      (tr2 : Array RuleId), 1000 ≤ m → 1000 ≤ n → EmSince s0 s →
      (matchRule program (sem ctx) cfg m rl [.inst ii]).run (s, tr) = .ok (some env, s1) →
      (evalExpr program (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → EmSince s0 s2 := by
  intro cfg hco m n s0 s tr env s1 r s2 tr2 hm hn hE hmatch heval
  simp only [emitHandIds, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at hid
  rcases hid with h | h | h | h
  · obtain rfl := lower_rule_eq hrl (k := 459) (r0 := rule_lower_1261) lowerData
      (by rw [h]; rfl)
    exact extend_emit hctx hW hi hc (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hco hm hn hE hmatch heval
  · obtain rfl := lower_rule_eq hrl (k := 500) (r0 := rule_lower_1315) lowerData
      (by rw [h]; rfl)
    exact extend_emit hctx hW hi hc (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hco hm hn hE hmatch heval
  · obtain rfl := lower_rule_eq hrl (k := 19) (r0 := rule_lower_1501) lowerData
      (by rw [h]; rfl)
    exact extr_emit hctx hi hc hco hm hn hE hmatch heval
  · obtain rfl := lower_rule_eq hrl (k := 20) (r0 := rule_lower_1507) lowerData
      (by rw [h]; rfl)
    exact extr2_emit hctx hi hc hco hm hn hE hmatch heval

end Backend.Proof.Driver
