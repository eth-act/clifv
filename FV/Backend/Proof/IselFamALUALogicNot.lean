import FV.Backend.Proof.IselTermsLogicNot
import FV.Backend.Proof.IselFamALUALogic

/-!
# Term contract of `alu_rs_imm_logic` (term 566), and the `band`/`bor`/`bxor`-with-`bnot` root
rules

`aluRsImmLogic_ok`: whatever rule of `alu_rs_imm_logic op ty x y` fires (register-register,
logical immediate for `y`, `ishl` by a constant for `y`), it emits one instruction computing
`notOpVal op x y` (`x & ~y`, `x | ~y`, `x ^ ~y` for `AndNot`/`OrrNot`/`EorNot`) into a fresh
vreg (`LogicOut`). The root rules `band/bor/bxor x (bnot y)` (1429/1466/1534) and
`… (bnot y) x` (1431/1468/1536) look through the `bnot` (`instData_bnot_inv`, `bnot_value`)
and call it; `bnot_eor` rule 1406 (family B) uses the contract with `EorNot`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## The negated-operand logical operations -/

/-- The value of the negated-second-operand logical operations (`bic`/`orn`/`eon`). -/
def notOpVal (op : ALUOp) {w : Nat} (a b : BitVec w) : BitVec w :=
  match op with
  | .andNot => a &&& ~~~b
  | .orrNot => a ||| ~~~b
  | .eorNot => a ^^^ ~~~b
  | _ => a

/-- The operations `alu_rs_imm_logic` is called with. -/
def NotOp (op : ALUOp) : Prop := op = .andNot ∨ op = .orrNot ∨ op = .eorNot

theorem NotOp.op8 {op : ALUOp} (h : NotOp op) :
    op = .add ∨ op = .sub ∨ op = .and ∨ op = .orr ∨ op = .eor ∨ op = .andNot ∨ op = .orrNot ∨
      op = .eorNot := by
  rcases h with rfl | rfl | rfl <;> simp

theorem NotOp.op6 {op : ALUOp} (h : NotOp op) :
    op = .and ∨ op = .orr ∨ op = .eor ∨ op = .andNot ∨ op = .orrNot ∨ op = .eorNot := by
  rcases h with rfl | rfl | rfl <;> simp

/-- **Width lemma** of the negated-operand operations, second operand any `B` whose low bits
are `v`. -/
theorem aluVal_holds_not {op : ALUOp} (hop : NotOp op) {ty : Clif.Ty} {sz : OperandSize}
    (hw : ty.width ≤ sz.bits) {a : CV} {B : BitVec sz.bits} {u v : BitVec ty.width}
    (ha : VHolds ⟨ty, u⟩ a) (hB : B.setWidth ty.width = v) :
    ∃ r, aluVal op (opnd sz a) B = some r ∧ VHolds ⟨ty, notOpVal op u v⟩ (resX sz r) := by
  have h64 := opSize_bits_le sz
  simp only [VHolds] at ha ⊢
  rcases hop with rfl | rfl | rfl <;> refine ⟨_, rfl, ?_⟩ <;> rw [resX_setWidth hw h64]
  · rw [BitVec.setWidth_and, BitVec.setWidth_not hw, opnd_setWidth hw h64, ha, hB]; rfl
  · rw [BitVec.setWidth_or, BitVec.setWidth_not hw, opnd_setWidth hw h64, ha, hB]; rfl
  · rw [BitVec.setWidth_xor, BitVec.setWidth_not hw, opnd_setWidth hw h64, ha, hB]; rfl

/-! ## The three rules -/

section Cases
variable {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
  {cfg : Config} (hc : cfg.checkOverlap = false) {k : Nat} {op : ALUOp}
  (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op) {ty : Clif.Ty} (hw : ty.width ≤ 64)
  {x y m n : Nat} {st st2 : LState} {tr tr2 : Array RuleId} {env : Interp.Env V}
  {s1 : LState × Array RuleId} {a : V}

include hp hctx hc hk hop hw in
theorem notlogic_3939
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3939
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3939.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
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
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
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
theorem notlogic_3941
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3941
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3941.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (notOpVal op) a st2 := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e2, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e3, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e4, hpy, -⟩ := matchArgs_cons_inv ha
  obtain ⟨j, infoj, fs, e5, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
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
  obtain rfl := hctx.valueReg x rx hrx
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
theorem notlogic_3944
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3944
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3944.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (notOpVal op) a st2 := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e2, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e3, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e4, hpy, -⟩ := matchArgs_cons_inv ha
  obtain ⟨j1, info1, fs1, e5, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpy
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clif hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, z, b, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat1
  obtain ⟨e6, -, hpb⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e7, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpb
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clif hctx hj2 hij2
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
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg z rz hrz
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
theorem aluRsImmLogic_ok {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {cfg : Config} (hc : cfg.checkOverlap = false) {k : Nat} {op : ALUOp}
    (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op) {ty : Clif.Ty} (hw : ty.width ≤ 64)
    {x y n : Nat} {st st2 : LState} {tr tr2 : Array RuleId} {a : V}
    (h : (applyTerm p (sem ctx) cfg (n + 60) 27 566
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) =
      .ok (some a, (st2, tr2))) :
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
  · exact notlogic_3941 hp hctx hc hk hop hw hmatch heval'
  · exact notlogic_3944 hp hctx hc hk hop hw hmatch heval'
  · exact notlogic_3939 hp hctx hc hk hop hw hmatch heval'

/-! ## `bnot` look-through -/

set_option maxRecDepth 20000 in
theorem variantNames_Unary_fa : (variantNames 152)[29]? = some "Unary" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Bnot : (variantNames 151)[100]? = some "Bnot" := rfl

theorem instNames_bnot {c : Clif.Inst} (h : instNames c = ("Unary", "Bnot")) :
    ∃ ty x, c = .unary .bnot ty x := by
  cases c <;> simp only [instNames, Prod.mk.injEq] at h <;> simp at h
  case unary op ty x =>
    cases op <;> simp [unaryOpcode] at h
    exact ⟨ty, x, rfl⟩
  case extend op ty x =>
    cases op <;> simp at h

/-- A matched `Unary (Bnot) y` is a `bnot`. -/
theorem instData_bnot_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 29 (.data 151 100 [] :: fs))) :
    ∃ ty y, cl = .unary .bnot ty y ∧ fs = [.value y] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [variantNames_Unary_fa] at hf
  rw [variantNames_Bnot] at ho
  have : instNames cl = ("Unary", "Bnot") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, y, rfl⟩ := instNames_bnot this
  refine ⟨ty, y, rfl, ?_⟩
  simp only [instData, unaryOpcode] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      injection h3 with _ h4

theorem evalInst_unary_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.UnaryOp}
    {ty : Clif.Ty} {x : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.unary op ty x) = .ok (vals, cm')) :
    ∃ u, fr.getAs x ty = .ok u ∧ vals = [⟨ty, Clif.Sem.unary op u⟩] := by
  simp only [Clif.evalInst] at h
  cases hx : fr.getAs x ty with
  | ok u =>
    rw [hx] at h
    simp only [bind, Clif.Res.bind, pure] at h
    cases h
    exact ⟨u, rfl, rfl⟩
  | trap c => rw [hx] at h; cases h
  | stuck m => rw [hx] at h; cases h

/-- **The value of a looked-through `bnot y'`** read at the instruction's type: the complement
of `y'`'s value at that type. -/
theorem bnot_value {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {y j y' : Nat}
    {infoj : IInfo} {ty1 ty : Clif.Ty} {v : BitVec ty.width} (hj : ctx.defInst? y = some j)
    (hij : ctx.insts[j]? = some infoj) (hcl : infoj.clif = some (.unary .bnot ty1 y'))
    (hy : fr.getAs y ty = .ok v) : ∃ w, fr.getAs y' ty = .ok w ∧ v = ~~~w := by
  obtain ⟨vals, hev, hl⟩ := hdfg.1 y j infoj _ _ hj hij hcl rfl (getAs_ok hy)
  obtain ⟨u, hu, rfl⟩ := evalInst_unary_inv (hev default)
  have hv := lookup_zip_single hl
  cases hv
  exact ⟨u, hu, rfl⟩

theorem OneInstOk.bnot_right {ctx : Ctx} {st : LState} {ty : Clif.Ty} {x y y' j : Nat}
    {infoj : IInfo} {ty1 : Clif.Ty} {g : BitVec ty.width → BitVec ty.width → BitVec ty.width}
    {mi : MInst} (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hcl : infoj.clif = some (.unary .bnot ty1 y')) (h : OneInstOk ctx st ty x y' g mi) :
    OneInstOk ctx st ty x y (fun u v => g u (~~~v)) mi := by
  obtain ⟨ops, hops, hdefs, hs⟩ := h
  refine ⟨ops, hops, hdefs, fun fr ρ w hv hd u v hx hy => ?_⟩
  obtain ⟨w', hy', rfl⟩ := bnot_value hd hj hij hcl hy
  simp only [BitVec.not_not]
  exact hs fr ρ w hv hd u w' hx hy'

theorem OneInstOk.bnot_left {ctx : Ctx} {st : LState} {ty : Clif.Ty} {x y y' j : Nat}
    {infoj : IInfo} {ty1 : Clif.Ty} {g : BitVec ty.width → BitVec ty.width → BitVec ty.width}
    {mi : MInst} (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hcl : infoj.clif = some (.unary .bnot ty1 y')) (h : OneInstOk ctx st ty x y' g mi) :
    OneInstOk ctx st ty y x (fun u v => g v (~~~u)) mi := by
  obtain ⟨ops, hops, hdefs, hs⟩ := h
  refine ⟨ops, hops, hdefs, fun fr ρ w hv hd u v hy hx => ?_⟩
  obtain ⟨w', hy', rfl⟩ := bnot_value hd hj hij hcl hy
  simp only [BitVec.not_not]
  exact hs fr ρ w hv hd v w' hx hy'

/-! ## The root rules -/

/-- The right-hand side `(output_reg (alu_rs_imm_logic op ty a b))` of the `bnot` rules, from
the evaluation of its arguments: one instruction computing `notOpVal op a b`. -/
theorem notRoot_rhs {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {cfg : Config} (hco : cfg.checkOverlap = false) {r : Rule}
    {k : Nat} {op : ALUOp} (hk : ALUOp.ofIdx? k = some op) (hop : NotOp op) {ty : Clif.Ty}
    (hw : ty.width ≤ 64) {args : List Expr} {a b N : Nat} {env : Interp.Env V} {st st' : LState}
    {tr tr' : Array RuleId} {out : V}
    (hrhs : r.rhs = .term 25 172 [.term 27 566 args])
    (hargsF : ∀ st tr n, (evalArgs p (sem ctx) cfg (n+5) args env).run (st, tr) =
      .ok (some [.data 59 k [], .ty (.int ty.width), .value a, .value b], (st, tr)))
    (heval : (evalExpr p (sem ctx) cfg (N + 100) r.rhs env).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ mi, st' = (st.fresh .int).2.emit mi ∧ out = .regsVec [[.vreg st.nextVreg .int]] ∧
      OneInstOk ctx st ty a b (notOpVal op) mi := by
  rw [hrhs] at heval
  obtain ⟨vs, s2, a', s3, hvs, happ, hout⟩ := rhs_output_inv (n := N + 97) heval
  rw [show N + 97 = (N + 92) + 5 from rfl, hargsF st tr (N + 92)] at hvs
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hvs
  obtain ⟨rfl, rfl⟩ := hvs
  obtain ⟨st3, tr3⟩ := s3
  obtain ⟨mi, rfl, rfl, hone⟩ := aluRsImmLogic_ok hp hctx hco hk hop hw (n := N + 37) happ
  rw [show N + 97 + 2 = (N + 89) + 10 from rfl, output_reg_run hp ctx hco] at hout
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hout
  obtain ⟨rfl, rfl, -⟩ := hout
  exact ⟨mi, rfl, rfl, hone⟩

/-- **Template: `cop x (bnot y)`** (`fits_in_64 (ty_int ty)`) →
`(alu_rs_imm_logic op ty x y)`. -/
theorem notRightRoot_ruleOk {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp}
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
      Refines F isem → MRStable F MR → LowerRuleOk isem MR env cp p r := by
  intro F isem MR env cp hR hMR f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr'
    hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) hargs hto hko hname hcop hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2476 term_2476_kind hp.t2384 term_2384_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty1, y', rfl, rfl⟩ := instData_bnot_inv hdat
  rw [hmatchF ctx cfg ii info infoj ty.width x y y' j st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨mi, rfl, rfl, hone⟩ := notRoot_rhs hp hctx hco hk hop hw hrhs
    (fun st tr n => args_not_right hp ctx st tr n opT2 k ty.width x y' (henum ctx cfg ty.width x y')) heval
  exact ⟨[mi], _, emitted_fresh_emit _ _, rfl,
    OneInstOk.lowerInstOk hR hMR hshift (fun u v => hg u v) (hone.bnot_right hj hij hcl)⟩

/-- **Template: `cop (bnot y) x`** → `(alu_rs_imm_logic op ty x y)`. -/
theorem notLeftRoot_ruleOk {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp}
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
      Refines F isem → MRStable F MR → LowerRuleOk isem MR env cp p r := by
  intro F isem MR env cp hR hMR f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr'
    hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, y, x, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) hargs hto hko hname hcop hmatch
  obtain ⟨e2, hpy, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2476 term_2476_kind hp.t2384 term_2384_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty1, y', rfl, rfl⟩ := instData_bnot_inv hdat
  rw [hmatchF ctx cfg ii info infoj ty.width x y y' j st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨mi, rfl, rfl, hone⟩ := notRoot_rhs hp hctx hco hk hop hw hrhs
    (fun st tr n => args_not_left hp ctx st tr n opT2 k ty.width y' x (henum ctx cfg ty.width y' x)) heval
  exact ⟨[mi], _, emitted_fresh_emit _ _, rfl,
    OneInstOk.lowerInstOk hR hMR hshift (fun u v => hg u v) (hone.bnot_left hj hij hcl)⟩

set_option maxRecDepth 20000 in
/-- **`band_not_right`** (`lower.isle:1429`, `band x (bnot y)` → `bic`), i8..i64. -/
theorem band_not_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1429 :=
  notRightRoot_ruleOk hp (cop := .band) (op := .andNot) (k := 6) rfl hp.t2381 term_2381_kind
    variantNames_Band rfl rfl rfl (.inl rfl)
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.band, notOpVal]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1429 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_AndNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`band_not_left`** (`lower.isle:1431`, `band (bnot y) x` → `bic`), i8..i64. -/
theorem band_not_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1431 :=
  notLeftRoot_ruleOk hp (cop := .band) (op := .andNot) (k := 6) rfl hp.t2381 term_2381_kind
    variantNames_Band rfl rfl rfl (.inl rfl)
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.band, notOpVal, BitVec.and_comm]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1431 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_AndNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bor_not_right`** (`lower.isle:1466`, `bor x (bnot y)` → `orn`), i8..i64. -/
theorem bor_not_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1466 :=
  notRightRoot_ruleOk hp (cop := .bor) (op := .orrNot) (k := 3) rfl hp.t2382 term_2382_kind
    variantNames_Bor rfl rfl rfl (.inr (.inl rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bor, notOpVal]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1466 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_OrrNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bor_not_left`** (`lower.isle:1468`, `bor (bnot y) x` → `orn`), i8..i64. -/
theorem bor_not_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1468 :=
  notLeftRoot_ruleOk hp (cop := .bor) (op := .orrNot) (k := 3) rfl hp.t2382 term_2382_kind
    variantNames_Bor rfl rfl rfl (.inr (.inl rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bor, notOpVal, BitVec.or_comm]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1468 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_OrrNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bxor_not_right`** (`lower.isle:1534`, `bxor x (bnot y)` → `eon`), i8..i64. -/
theorem bxor_not_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1534 :=
  notRightRoot_ruleOk hp (cop := .bxor) (op := .eorNot) (k := 8) rfl hp.t2383 term_2383_kind
    variantNames_Bxor rfl rfl rfl (.inr (.inr rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bxor, notOpVal]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1534 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_EorNot hp ctx w a b st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bxor_not_left`** (`lower.isle:1536`, `bxor (bnot y) x` → `eon`), i8..i64. -/
theorem bxor_not_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1536 :=
  notLeftRoot_ruleOk hp (cop := .bxor) (op := .eorNot) (k := 8) rfl hp.t2383 term_2383_kind
    variantNames_Bxor rfl rfl rfl (.inr (.inr rfl))
    (fun u v => by simp [Clif.Sem.binary, Clif.Sem.bxor, notOpVal, BitVec.xor_comm]) rfl
    (fun ctx _ _ _ _ _ _ _ _ _ st tr m hi hty hw hd hj hij hdj =>
      match_1536 hp ctx st tr m hi hty hw hd hj hij hdj)
    (fun ctx _ w a b st tr n => enum_EorNot hp ctx w a b st tr n) F isem MR env cp hR hMR

/-! ## `bnot (bxor x y)` (rule 1406, family B's fusion, proven here for M4AluB2) -/

theorem instData_unary_eTy {f : Clif.Function} {op : Clif.UnaryOp} {ty : Clif.Ty} {x : Nat}
    {d : V} (h : instData f (.unary op ty x) = .ok d) : eTy ty = true := by
  simp only [instData] at h
  split at h
  · split at h
    · cases h
    · rename_i hne
      simpa using hne
  · cases h

/-- **`LowerInstOk` of a unary instruction `cop ty z` lowered to one instruction `mi`** that
computes `g u v` from values `x`, `y` (`OneInstOk`), when `z`'s value `a` determines them with
`cop a = g u v` (look-through of `z`'s definition). -/
theorem lowerInstOk_unary_look {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {ctx : Ctx} (hR : Refines F isem) (hMR : MRStable F MR)
    {cop : Clif.UnaryOp} {ty : Clif.Ty} {z x y : Nat} {results : List Nat} {st : LState}
    {mi : MInst} {g : BitVec ty.width → BitVec ty.width → BitVec ty.width}
    (h : OneInstOk ctx st ty x y g mi)
    (hz : ∀ fr, DFGCons ctx fr → ∀ a, fr.getAs z ty = .ok a →
      ∃ u v, fr.getAs x ty = .ok u ∧ fr.getAs y ty = .ok v ∧ Clif.Sem.unary cop a = g u v) :
    LowerInstOk isem MR env cp ctx (.unary cop ty z) results st [[.vreg st.nextVreg .int]]
      ((st.fresh .int).2.emit mi) [mi] := by
  obtain ⟨ops, hops, hdefs, hsem⟩ := h
  have hvd : vdefs mi = [st.nextVreg] := by simp [vdefs, hops, hdefs]
  refine ⟨by rw [nextVreg_fresh_emit]; omega, ?_, ?_⟩
  · intro m hm d hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [hvd, List.mem_singleton] at hd
    subst hd
    rw [nextVreg_fresh_emit]
    omega
  intro fr cm ρ w _ hvals hdfg hmr
  have hout : instOutcome env cp fr cm (.unary cop ty z) = Clif.evalInst fr cm (.unary cop ty z) := rfl
  rw [hout]
  simp only [Clif.evalInst]
  cases hzv : fr.getAs z ty with
  | trap c => simp [bind, Clif.Res.bind, explicitTrapInst]
  | stuck msg => simp [bind, Clif.Res.bind]
  | ok a =>
  simp only [bind, Clif.Res.bind, pure]
  obtain ⟨u, v, hx, hy, hg⟩ := hz fr hdfg a hzv
  obtain ⟨hus, r, hs, hh⟩ := hsem fr ρ w hvals hdfg u v hx hy
  obtain ⟨w', hrun, hsw⟩ := seqRun_one hR hops hdefs hs
  refine ⟨fun m hm q hq => ?_, _, w', hrun, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hsw.nf hmr⟩
  · simp only [List.mem_singleton] at hm
    subst hm
    exact .inr (hus q hq)
  · intro j rs val hrs hval
    match j, hrs, hval with
    | 0, hrs, hval =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
      subst hrs; subst hval
      refine ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), ?_⟩
      rw [hg]
      simpa [upd] using hh
    | _ + 1, hrs, _ => simp at hrs

set_option maxRecDepth 20000 in
/-- **`bnot (bxor x y)`** (`lower.isle:1406`, → `eon x, y`), i8..i64. -/
theorem bnot_bxor_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1406 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
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
    rw [hres]; simp [ofClif_int_width]
  obtain ⟨e2, hpz, -⟩ := matchArgs_cons_inv hrest
  obtain ⟨j, infoj, fs', e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2383 term_2383_kind hpz
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdatj
  obtain ⟨ty1, x, y, rfl, -, rfl⟩ := instData_binary_inv variantNames_Bxor (cop := .bxor) rfl hdatj
  rw [match_1406 hp ctx st tr m' hi hhead hw hd hj hij hdj] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨mi, rfl, rfl, hone⟩ := notRoot_rhs hp hctx hco (k := 8) rfl (.inr (.inr rfl)) hw rfl
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
