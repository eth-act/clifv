module

public import FV.Backend.Proof.IselFamALUALogicNot
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamALUATI

@[expose] public section

/-!
# `IselFamALUALogicNot` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamALUALogicNot`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
section Cases
variable {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
  {cfg : Config} (hc : cfg.checkOverlap = false) {k : Nat} {op : ALUOp}
  (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op) {ty : Clif.Ty} (hw : ty.width ≤ 64)
  {x y m n : Nat} {st st2 : LState} {tr tr2 : Array RuleId} {env : Interp.Env V}
  {s1 : LState × Array RuleId} {a : V}
include hp hctx hc hk hop hw in
theorem notlogic_3939TI
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3939
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3939.rhs env).run s1 =
      .ok (some a, (st2, tr2)))
    (hxI : IntPos ctx x := by int_posA) (hyI : IntPos ctx y := by int_posA) :
    LogicOut ctx st ty x y (notOpVal op) a st2 := by
  rw [match_3939 hp ctx st tr (m + 8)] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_3939_none hp ctx st tr n (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_3939_none hp ctx st tr n (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI y ry hry
  obtain ⟨tr', he⟩ := rhs_3939 hp ctx hc st tr n hk hrx hry hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨.aluRRR op (szOf ty.width) (.vreg st.nextVreg .int) (.vreg x .int) (.vreg y .int),
    by rw [fresh_fst], by rw [fresh_fst], _, operands_aluRRR _ _ _ _ _, rfl, ?_⟩
  intro fr ρ w hvals _ u v hx hy
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [vuseNums_aluRRR] at hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact getAs_isSome hx
    · exact getAs_isSome hy
  · obtain ⟨r, hr, hh⟩ := aluVal_holds_not hop (szOf_bits hw) (hvals x _ (getAs_ok hx))
      (opnd_setWidth_eq (szOf_bits hw) (hvals y _ (getAs_ok hy)))
    exact ⟨_, ispec_aluRRR' hop.op8 hr, hh⟩

include hp hctx hc hk hop hw in
theorem notlogic_3941TI
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3941
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3941.rhs env).run s1 =
      .ok (some a, (st2, tr2)))
    (hxI : IntPos ctx x := by int_posA) (hyI : IntPos ctx y := by int_posA) :
    LogicOut ctx st ty x y (notOpVal op) a st2 := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e2, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e3, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e4, hpy, -⟩ := matchArgs_cons_inv ha
  obtain ⟨j, infoj, fs, e5, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  cases himm : immLogicOf? ty.width (imm64OfIconst ty' c) with
  | none => rw [match_3941_none hp ctx st tr m hj hij hdj himm] at hmatch; cases hmatch
  | some imm =>
  rw [match_3941 hp ctx st tr m hj hij hdj himm] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_3941_none hp ctx st tr n hrx _ _)
  | some rx =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain ⟨tr', he⟩ := rhs_3941 hp ctx hc st tr n hk hrx hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨.aluRRImmLogic op (szOf ty.width) (.vreg st.nextVreg .int) (.vreg x .int) imm,
    by rw [fresh_fst], by rw [fresh_fst], _, operands_aluRRImmLogic _ _ _ _ _, rfl, ?_⟩
  intro fr ρ w hvals hdfg u v hx hy
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hy) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hiv, hio⟩ := immLogicOf_spec hw himm
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [vuseNums_aluRRImmLogic, List.mem_singleton] at hz
    subst hz
    exact getAs_isSome hx
  · obtain ⟨r, hr, hh⟩ := aluVal_holds_not hop (szOf_bits hw) (hvals x _ (getAs_ok hx))
      (show (BitVec.ofNat (szOf ty.width).bits imm.value).setWidth ty.width = v by
        rw [hiv]; exact setWidth_ofNat_toNat (szOf_bits hw) v)
    exact ⟨_, ispec_aluRRImmLogic hio hop.op6 hr, hh⟩

include hp hctx hc hk hop hw in
theorem notlogic_3944TI
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3944
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3944.rhs env).run s1 =
      .ok (some a, (st2, tr2)))
    (hxI : IntPos ctx x := by int_posA) (hyI : IntPos ctx y := by int_posA) :
    LogicOut ctx st ty x y (notOpVal op) a st2 := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e2, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e3, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e4, hpy, -⟩ := matchArgs_cons_inv ha
  obtain ⟨j1, info1, fs1, e5, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpy
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clifTI hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, z, b, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat1
  obtain ⟨e6, -, hpb⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e7, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpb
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clifTI hctx hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty3, c3, rfl, rfl⟩ := instData_iconst_inv hdat2
  have he3 := instData_iconst_eTy hdat2
  cases hsh : lshlOf? ty.width (imm64OfIconst ty3 c3) with
  | none => rw [match_3944_none hp ctx st tr m hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch; cases hmatch
  | some sh =>
  rw [match_3944 hp ctx st tr m hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_3944_none hp ctx st tr n (.inl hrx) _ _)
  | some rx =>
  cases hrz : ctx.valueReg? z with
  | none => exact absurd heval (rhs_3944_none hp ctx st tr n (.inr hrz) _ _)
  | some rz =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI z rz hrz
  obtain ⟨tr', he⟩ := rhs_3944 hp ctx hc st tr n hk hrx hrz hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨.aluRRRShift op (szOf ty.width) (.vreg st.nextVreg .int) (.vreg x .int) (.vreg z .int) sh,
    by rw [fresh_fst], by rw [fresh_fst], _, operands_aluRRRShift _ _ _ _ _ _, rfl, ?_⟩
  intro fr ρ w hvals hdfg u v hx hy
  obtain ⟨u', hz, hshl, hamt, rfl⟩ :=
    ishl_const_value hdfg hw hj1 hij1 hcl1 hj2 hij2 hcl2 he3 hy hsh
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [vuseNums_aluRRRShift] at hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · exact getAs_isSome hx
    · exact getAs_isSome hz
  · have hB : (opnd (szOf ty.width) (ρ z) <<< sh.amt).setWidth ty.width = u' <<< sh.amt := by
      rw [BitVec.setWidth_shiftLeft_of_le (szOf_bits hw),
        opnd_setWidth_eq (szOf_bits hw) (hvals z _ (getAs_ok hz))]
    obtain ⟨r, hr, hh⟩ := aluVal_holds_not hop (szOf_bits hw) (hvals x _ (getAs_ok hx)) hB
    exact ⟨_, ispec_aluRRRShift hop.op8 hshl (Nat.lt_of_lt_of_le hamt (szOf_bits hw)) hr, hh⟩

end Cases
/-- **Term contract of `alu_rs_imm_logic op ty x y`** (`op` = `AndNot`/`OrrNot`/`EorNot`):
whichever of its three rules fires, it emits one instruction computing `notOpVal op x y` into
the fresh vreg. -/
theorem aluRsImmLogic_okTI {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {cfg : Config} (hc : cfg.checkOverlap = false) {k : Nat} {op : ALUOp}
    (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op) {ty : Clif.Ty} (hw : ty.width ≤ 64)
    {x y n : Nat} {st st2 : LState} {tr tr2 : Array RuleId} {a : V}
    (h : (applyTerm p (sem ctx) cfg (n + 60) 27 566
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) =
      .ok (some a, (st2, tr2)))
    (hxI : IntPos ctx x := by int_posA) (hyI : IntPos ctx y := by int_posA) :
    LogicOut ctx st ty x y (notOpVal op) a st2 := by
  obtain ⟨r, hr, m, env, s1, st', tr', hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some hc hp.t566 term_566_kind rfl h
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  rw [hp.r566] at hr hmn
  simp only [List.length_cons, List.length_nil] at hmn
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  have heval' : (evalExpr p (sem ctx) cfg ((n + 19) + 40) r.rhs env).run s1 =
      .ok (some a, (st2, tr')) := heval
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact notlogic_3941TI hp hctx hc hk hop hw hmatch heval'
  · exact notlogic_3944TI hp hctx hc hk hop hw hmatch heval'
  · exact notlogic_3939TI hp hctx hc hk hop hw hmatch heval'

/-- The right-hand side `(output_reg (alu_rs_imm_logic op ty a b))` of the `bnot` rules, from
the evaluation of its arguments: one instruction computing `notOpVal op a b`. -/
theorem notRoot_rhsTI {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {cfg : Config} (hco : cfg.checkOverlap = false) {r : Rule}
    {k : Nat} {op : ALUOp} (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op) {ty : Clif.Ty}
    (hw : ty.width ≤ 64) {args : List Expr} {a b N : Nat} {env : Interp.Env V} {st st' : LState}
    {tr tr' : Array RuleId} {out : V}
    (hrhs : r.rhs = .term 25 172 [.term 27 566 args])
    (hargsF : ∀ st tr n, (evalArgs p (sem ctx) cfg (n+5) args env).run (st, tr) =
      .ok (some [.data 59 k [], .ty (.int ty.width), .value a, .value b], (st, tr)))
    (heval : (evalExpr p (sem ctx) cfg (N + 100) r.rhs env).run (st, tr) =
      .ok (some out, (st', tr')))
    (haI : IntPos ctx a := by int_posA) (hbI : IntPos ctx b := by int_posA) :
    ∃ mi, st' = (st.fresh .int).2.emit mi ∧ out = .regsVec [[.vreg st.nextVreg .int]] ∧
      OneInstOk ctx st ty a b (notOpVal op) mi := by
  rw [hrhs] at heval
  obtain ⟨vs, s2, a', s3, hvs, happ, hout⟩ := rhs_output_inv (n := N + 97) heval
  rw [show N + 97 = (N + 92) + 5 from rfl, hargsF st tr (N + 92)] at hvs
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hvs
  obtain ⟨rfl, rfl⟩ := hvs
  obtain ⟨st3, tr3⟩ := s3
  obtain ⟨mi, rfl, rfl, hone⟩ := aluRsImmLogic_okTI hp hctx hco hk hop hw (n := N + 37) happ
  rw [show N + 97 + 2 = (N + 89) + 10 from rfl, output_reg_run hp ctx hco] at hout
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hout
  obtain ⟨rfl, rfl, -⟩ := hout
  exact ⟨mi, rfl, rfl, hone⟩

/-- **Template: `cop x (bnot y)`** (`fits_in_64 (ty_int ty)`) →
`(alu_rs_imm_logic op ty x y)`. -/
theorem notRightRoot_ruleOkTI {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp}
    {op : ALUOp} {k : Nat} {nm : String} {opT opT2 : TermId} {to : Term} {ko : Nat}
    {tyPat : Pattern} {Px : Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 [.term 151 opT [], .term 147 1614
      [Px, .term 15 1 [.term 18 209 [.wildcard 14, .term 152 2476 [.term 151 2384 [],
        .bind 15 2 (.wildcard 15)]]]]]]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some nm) (hcop : binaryOpcode cop = some nm)
    (hshift : cop.isShift = false) (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op)
    (hg : ∀ {w : Nat} (u v : BitVec w), Clif.Sem.binary cop u v = notOpVal op u (~~~v))
    (hrhs : r.rhs = .term 25 172 [.term 27 566 [.term 59 opT2 [], .var 14 0, .var 15 1, .var 15 2]])
    (hmatchF : ∀ (ctx : Ctx) (cfg : Config) ii (info infoj : IInfo) w x y y' j st tr m,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] →
      ctx.defInst? y = some j → ctx.insts[j]? = some infoj →
      infoj.data = .data 152 29 [.data 151 100 [], .value y'] →
      (matchRule p (sem ctx) cfg (m + 10) r [.inst ii]).run (st, tr) =
        .ok (some (env3 (.ty (.int w)) (.value x) (.value y')), (st, tr)))
    (henum : ∀ (ctx : Ctx) (cfg : Config) w a b st tr n,
      (evalExpr p (sem ctx) cfg (n+2) (.term 59 opT2 []) (env3 (.ty (.int w)) (.value a) (.value b))).run
        (st, tr) = .ok (some (.data 59 k []), (st, tr))) :
    ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
      Refines F isem → MRStable F MR → LowerRuleOkTI isem MR env cp p r := by
  intro F isem MR env cp hR hMR f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out
      st' tr' hm hn _hvb _hfirst hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) hargs hto hko hname hcop hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2476 term_2476_kind hp.t2384 term_2384_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty1, y', rfl, rfl⟩ := instData_bnot_inv hdat
  rw [hmatchF ctx cfg ii info infoj ty.width x y y' j st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨mi, rfl, rfl, hone⟩ := notRoot_rhsTI hp hctx hco hk hop hw hrhs
    (fun st tr n => args_not_right hp ctx st tr n opT2 k ty.width x y' (henum ctx cfg ty.width x y')) heval
  exact ⟨[mi], _, emitted_fresh_emit _ _, rfl,
    OneInstOk.lowerInstOk hR hMR hshift (fun u v => hg u v) (hone.bnot_right hj hij hcl)⟩

/-- **Template: `cop (bnot y) x`** → `(alu_rs_imm_logic op ty x y)`. -/
theorem notLeftRoot_ruleOkTI {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp}
    {op : ALUOp} {k : Nat} {nm : String} {opT opT2 : TermId} {to : Term} {ko : Nat}
    {tyPat : Pattern} {Px : Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 [.term 151 opT [], .term 147 1614
      [.term 15 1 [.term 18 209 [.wildcard 14, .term 152 2476 [.term 151 2384 [],
        .bind 15 1 (.wildcard 15)]]], Px]]]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some nm) (hcop : binaryOpcode cop = some nm)
    (hshift : cop.isShift = false) (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op)
    (hg : ∀ {w : Nat} (u v : BitVec w), Clif.Sem.binary cop u v = notOpVal op v (~~~u))
    (hrhs : r.rhs = .term 25 172 [.term 27 566 [.term 59 opT2 [], .var 14 0, .var 15 2, .var 15 1]])
    (hmatchF : ∀ (ctx : Ctx) (cfg : Config) ii (info infoj : IInfo) w x y y' j st tr m,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 2 [.data 151 ko [], .values [y, x]] →
      ctx.defInst? y = some j → ctx.insts[j]? = some infoj →
      infoj.data = .data 152 29 [.data 151 100 [], .value y'] →
      (matchRule p (sem ctx) cfg (m + 10) r [.inst ii]).run (st, tr) =
        .ok (some (env3 (.ty (.int w)) (.value y') (.value x)), (st, tr)))
    (henum : ∀ (ctx : Ctx) (cfg : Config) w a b st tr n,
      (evalExpr p (sem ctx) cfg (n+2) (.term 59 opT2 []) (env3 (.ty (.int w)) (.value a) (.value b))).run
        (st, tr) = .ok (some (.data 59 k []), (st, tr))) :
    ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
      Refines F isem → MRStable F MR → LowerRuleOkTI isem MR env cp p r := by
  intro F isem MR env cp hR hMR f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out
      st' tr' hm hn _hvb _hfirst hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, y, x, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) hargs hto hko hname hcop hmatch
  obtain ⟨e2, hpy, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2476 term_2476_kind hp.t2384 term_2384_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty1, y', rfl, rfl⟩ := instData_bnot_inv hdat
  rw [hmatchF ctx cfg ii info infoj ty.width x y y' j st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨mi, rfl, rfl, hone⟩ := notRoot_rhsTI hp hctx hco hk hop hw hrhs
    (fun st tr n => args_not_left hp ctx st tr n opT2 k ty.width y' x (henum ctx cfg ty.width y' x)) heval
  exact ⟨[mi], _, emitted_fresh_emit _ _, rfl,
    OneInstOk.lowerInstOk hR hMR hshift (fun u v => hg u v) (hone.bnot_left hj hij hcl)⟩

set_option maxRecDepth 20000 in
/-- **`band_not_right`** (`lower.isle:1429`, `band x (bnot y)` → `bic`), i8..i64. -/
theorem band_not_right_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1429 :=
  notRightRoot_ruleOkTI hp (cop := .band) (op := .andNot) (k := 6) rfl hp.t2381 term_2381_kind
    variantNames_Band rfl rfl rfl (.inl rfl)
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.band, notOpVal]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1429 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_AndNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`band_not_left`** (`lower.isle:1431`, `band (bnot y) x` → `bic`), i8..i64. -/
theorem band_not_left_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1431 :=
  notLeftRoot_ruleOkTI hp (cop := .band) (op := .andNot) (k := 6) rfl hp.t2381 term_2381_kind
    variantNames_Band rfl rfl rfl (.inl rfl)
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.band, notOpVal, BitVec.and_comm]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1431 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_AndNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bor_not_right`** (`lower.isle:1466`, `bor x (bnot y)` → `orn`), i8..i64. -/
theorem bor_not_right_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1466 :=
  notRightRoot_ruleOkTI hp (cop := .bor) (op := .orrNot) (k := 3) rfl hp.t2382 term_2382_kind
    variantNames_Bor rfl rfl rfl (.inr (.inl rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bor, notOpVal]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1466 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_OrrNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bor_not_left`** (`lower.isle:1468`, `bor (bnot y) x` → `orn`), i8..i64. -/
theorem bor_not_left_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1468 :=
  notLeftRoot_ruleOkTI hp (cop := .bor) (op := .orrNot) (k := 3) rfl hp.t2382 term_2382_kind
    variantNames_Bor rfl rfl rfl (.inr (.inl rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bor, notOpVal, BitVec.or_comm]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1468 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_OrrNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bxor_not_right`** (`lower.isle:1534`, `bxor x (bnot y)` → `eon`), i8..i64. -/
theorem bxor_not_right_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1534 :=
  notRightRoot_ruleOkTI hp (cop := .bxor) (op := .eorNot) (k := 8) rfl hp.t2383 term_2383_kind
    variantNames_Bxor rfl rfl rfl (.inr (.inr rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bxor, notOpVal]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1534 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_EorNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bxor_not_left`** (`lower.isle:1536`, `bxor (bnot y) x` → `eon`), i8..i64. -/
theorem bxor_not_left_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1536 :=
  notLeftRoot_ruleOkTI hp (cop := .bxor) (op := .eorNot) (k := 8) rfl hp.t2383 term_2383_kind
    variantNames_Bxor rfl rfl rfl (.inr (.inr rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bxor, notOpVal, BitVec.xor_comm]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1536 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_EorNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bnot (bxor x y)`** (`lower.isle:1406`, → `eon x, y`), i8..i64. -/
theorem bnot_bxor_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1406 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨info', fs, e0, e1, hi', hd, hrest, -⟩ :=
    root_match_inv hp ctx (m := m' + 9) rfl hp.t2476 term_2476_kind hp.t2384 term_2384_kind hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  obtain ⟨ty, z, rfl, rfl⟩ := instData_bnot_inv hdat
  have hw := eTy_width (instData_unary_eTy hdat)
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width (isInt_of_eTy (instData_unary_eTy hdat))]
  obtain ⟨e2, hpz, -⟩ := matchArgs_cons_inv hrest
  obtain ⟨j, infoj, fs', e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2383 term_2383_kind hpz
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdatj
  obtain ⟨ty1, x, y, rfl, -, rfl⟩ := instData_binary_inv variantNames_Bxor (cop := .bxor) rfl hdatj
  rw [match_1406 hp ctx st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨mi, rfl, rfl, hone⟩ := notRoot_rhsTI hp hctx hco (k := 8) rfl (.inr (.inr rfl)) hw rfl
    (fun st tr n => args_not_right hp ctx st tr n 1970 8 ty.width x y (enum_EorNot hp ctx ty.width x y))
    heval
  refine ⟨[mi], _, emitted_fresh_emit _ _, rfl, lowerInstOk_unary_look hR hMR hone ?_⟩
  intro fr hdfg a hz
  obtain ⟨vals, hev, hl⟩ := hdfg.1 z j infoj _ _ hj hij hcl rfl (getAs_ok hz)
  obtain ⟨u, v, hx, hy, rfl⟩ := evalInst_binary_inv rfl (hev default)
  have hv := lookup_zip_single hl
  cases hv
  exact ⟨u, v, hx, hy, BitVec.not_xor_right⟩

end Backend.Proof
