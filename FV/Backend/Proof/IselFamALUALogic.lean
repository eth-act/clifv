import FV.Backend.Proof.IselTermsLogic
import FV.Backend.Proof.IselFamilyALU

/-!
# Term contract of `alu_rs_imm_logic_commutative`, and the `band`/`bor`/`bxor` root rules

`aluRsImmLogicComm_ok`: whatever rule of `alu_rs_imm_logic_commutative op ty x y` fires
(register-register, logical immediate on either side, `ishl` by a constant on either side),
it emits one instruction computing `x op y` into a fresh vreg (`LogicOut`). The case lemmas
(`logic_39xx`) invert the rule's match (look-through facts), fix the environment by the forward
lemmas (`IselTermsLogic`), and prove the value-level meaning with `DFGCons`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000 in
theorem variantNames_Ishl : (variantNames 151)[103]? = some "Ishl" := rfl

/-- What an instruction-emitting term contract concludes: the value is the fresh vreg, the
state emitted one instruction `mi`, which computes `g x y` (`OneInstOk`). -/
def LogicOut (ctx : Ctx) (st : LState) (ty : Clif.Ty) (x y : Nat)
    (g : BitVec ty.width → BitVec ty.width → BitVec ty.width) (a : V) (st2 : LState) : Prop :=
  ∃ mi, a = .reg (.vreg st.nextVreg .int) ∧ st2 = (st.fresh .int).2.emit mi ∧
    OneInstOk ctx st ty x y g mi

/-- The commutative logical operations and their CLIF opcodes. -/
def LogicPair (op : ALUOp) (cop : Clif.BinaryOp) : Prop :=
  (op, cop) = (.and, .band) ∨ (op, cop) = (.orr, .bor) ∨ (op, cop) = (.eor, .bxor)

theorem LogicPair.alu {op : ALUOp} {cop : Clif.BinaryOp} (h : LogicPair op cop) :
    (op, cop) = (.add, .iadd) ∨ (op, cop) = (.sub, .isub) ∨ (op, cop) = (.and, .band) ∨
      (op, cop) = (.orr, .bor) ∨ (op, cop) = (.eor, .bxor) :=
  .inr (.inr h)

theorem LogicPair.op8 {op : ALUOp} {cop : Clif.BinaryOp} (h : LogicPair op cop) :
    op = .add ∨ op = .sub ∨ op = .and ∨ op = .orr ∨ op = .eor ∨ op = .andNot ∨ op = .orrNot ∨
      op = .eorNot := by
  rcases h with h | h | h <;> simp only [Prod.mk.injEq] at h <;> simp [h.1]

theorem LogicPair.op6 {op : ALUOp} {cop : Clif.BinaryOp} (h : LogicPair op cop) :
    op = .and ∨ op = .orr ∨ op = .eor ∨ op = .andNot ∨ op = .orrNot ∨ op = .eorNot := by
  rcases h with h | h | h <;> simp only [Prod.mk.injEq] at h <;> simp [h.1]

theorem LogicPair.comm {op : ALUOp} {cop : Clif.BinaryOp} (h : LogicPair op cop) {w : Nat}
    (u v : BitVec w) : Clif.Sem.binary cop u v = Clif.Sem.binary cop v u := by
  rcases h with h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;>
    simp only [Clif.Sem.binary, Clif.Sem.band, Clif.Sem.bor, Clif.Sem.bxor]
  · exact BitVec.and_comm u v
  · exact BitVec.or_comm u v
  · exact BitVec.xor_comm u v

theorem immLogicOf_spec {ty : Clif.Ty} (hw : ty.width ≤ 64) {c : BitVec ty.width} {imm : ImmLogic}
    (h : immLogicOf? ty.width (imm64OfIconst ty c) = some imm) :
    imm.value = c.toNat ∧ ImmLogic.ofNat? imm.value (szOf ty.width) = some imm := by
  unfold immLogicOf? at h
  rw [u64_imm64OfIconst hw] at h
  split at h
  · rename_i h32
    have heq := immLogic_ofNat_eq h
    subst heq
    have hs : szOf ty.width = .size32 := by simp [szOf, h32]
    exact ⟨rfl, by rw [hs]; exact h⟩
  · split at h
    · rename_i h32 h64
      have heq := immLogic_ofNat_eq h
      subst heq
      have hs : szOf ty.width = .size64 := by simp [szOf, h32]
      exact ⟨rfl, by rw [hs]; exact h⟩
    · cases h

section Cases
variable {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
  {cfg : Config} (hc : cfg.checkOverlap = false) {k : Nat} {op : ALUOp} {cop : Clif.BinaryOp}
  (hk : ALUOp.ofIdx? k = some op) (hop : LogicPair op cop) {ty : Clif.Ty} (hw : ty.width ≤ 64)
  {x y m n : Nat} {st st2 : LState} {tr tr2 : Array RuleId} {env : Interp.Env V}
  {s1 : LState × Array RuleId} {a : V}

include hp hctx hc hk hop hw in
theorem logic_3916
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3916
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3916.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (Clif.Sem.binary cop) a st2 := by
  rw [match_3916 hp ctx st tr (m + 8)] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_3916_none hp ctx st tr n (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_3916_none hp ctx st tr n (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
  obtain ⟨tr', he⟩ := rhs_3916 hp ctx hc st tr n hk hrx hry hw
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
  · obtain ⟨r, hr, hh⟩ := aluVal_holds_B hop.alu (szOf_bits hw) (hvals x _ (getAs_ok hx))
      (opnd_setWidth_eq (szOf_bits hw) (hvals y _ (getAs_ok hy)))
    exact ⟨_, ispec_aluRRR' hop.op8 hr, hh⟩

include hp hctx hc hk hop hw in
theorem logic_3920
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3920
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3920.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (Clif.Sem.binary cop) a st2 := by
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
  | none => rw [match_3920_none hp ctx st tr m hj hij hdj himm] at hmatch; cases hmatch
  | some imm =>
  rw [match_3920 hp ctx st tr m hj hij hdj himm] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_3920_none hp ctx st tr n hrx _ _)
  | some rx =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain ⟨tr', he⟩ := rhs_3920 hp ctx hc st tr n hk hrx hw
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
  · obtain ⟨r, hr, hh⟩ := aluVal_holds_B hop.alu (szOf_bits hw) (hvals x _ (getAs_ok hx))
      (show (BitVec.ofNat (szOf ty.width).bits imm.value).setWidth ty.width = v by
        rw [hiv]; exact setWidth_ofNat_toNat (szOf_bits hw) v)
    exact ⟨_, ispec_aluRRImmLogic hio hop.op6 hr, hh⟩

include hp hctx hc hk hop hw in
theorem logic_3923
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3923
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3923.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (Clif.Sem.binary cop) a st2 := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e2, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e3, hpx, -⟩ := matchArgs_cons_inv ha
  obtain ⟨j, infoj, fs, e5, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpx
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  cases himm : immLogicOf? ty.width (imm64OfIconst ty' c) with
  | none => rw [match_3923_none hp ctx st tr m hj hij hdj himm] at hmatch; cases hmatch
  | some imm =>
  rw [match_3923 hp ctx st tr m hj hij hdj himm] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_3923_none hp ctx st tr n hry _ _)
  | some ry =>
  obtain rfl := hctx.valueReg y ry hry
  obtain ⟨tr', he⟩ := rhs_3923 hp ctx hc st tr n hk hry hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨.aluRRImmLogic op (szOf ty.width) (.vreg st.nextVreg .int) (.vreg y .int) imm,
    by rw [fresh_fst], by rw [fresh_fst], _, operands_aluRRImmLogic _ _ _ _ _, rfl, ?_⟩
  intro fr ρ w hvals hdfg u v hx hy
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hx) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hiv, hio⟩ := immLogicOf_spec hw himm
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [vuseNums_aluRRImmLogic, List.mem_singleton] at hz
    subst hz
    exact getAs_isSome hy
  · obtain ⟨r, hr, hh⟩ := aluVal_holds_B hop.alu (szOf_bits hw) (hvals y _ (getAs_ok hy))
      (show (BitVec.ofNat (szOf ty.width).bits imm.value).setWidth ty.width = u by
        rw [hiv]; exact setWidth_ofNat_toNat (szOf_bits hw) u)
    refine ⟨_, ispec_aluRRImmLogic hio hop.op6 hr, ?_⟩
    rw [hop.comm]
    exact hh

/-- The looked-through `ishl z (iconst k)` defining `y`: `y`'s value is `z`'s value shifted by
the constant, the constant is `< 64`, and the rule's shift amount is it modulo the width. -/
theorem ishl_const_value {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {ty : Clif.Ty}
    (hw : ty.width ≤ 64) {y z b j1 j2 : Nat} {info1 info2 : IInfo} {ty1 ty3 : Clif.Ty}
    {c3 : BitVec ty3.width} {v : BitVec ty.width} {sh : ShiftOpAndAmt}
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hcl1 : info1.clif = some (.binary .ishl ty1 z b))
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hcl2 : info2.clif = some (.iconst ty3 c3)) (he3 : eTy ty3 = true)
    (hy : fr.getAs y ty = .ok v) (hsh : lshlOf? ty.width (imm64OfIconst ty3 c3) = some sh) :
    ∃ u', fr.getAs z ty = .ok u' ∧ sh.op = .lsl ∧ sh.amt < ty.width ∧ v = u' <<< sh.amt := by
  obtain ⟨vals, hev, hl⟩ := hdfg.1 y j1 info1 _ _ hj1 hij1 hcl1 rfl (getAs_ok hy)
  obtain ⟨u', bv, r', hz, hb, hr', rfl⟩ := evalInst_shift_inv rfl (hev default)
  have hv := lookup_zip_single hl
  cases hv
  have hbv := dfg_single hdfg hj2 hij2 hcl2 rfl (get_ok hb) (a := ⟨ty3, c3⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  subst hbv
  simp only [Clif.Sem.shift, Option.some.injEq] at hr'
  subst hr'
  unfold lshlOf? at hsh
  rw [u64_imm64OfIconst (eTy_width he3)] at hsh
  split at hsh
  · rename_i s hs
    obtain ⟨rfl, h63⟩ := shiftImm_some hs
    split at hsh
    · cases hsh
      refine ⟨u', hz, rfl, ?_, ?_⟩
      · show Nat.land c3.toNat (ty.width - 1) < ty.width
        rw [land_width_sub_one hw]
        exact Nat.mod_lt _ (clif_width_pos ty)
      · show Clif.Sem.ishl u' c3 = u' <<< Nat.land c3.toNat (ty.width - 1)
        rw [land_width_sub_one hw]
        rfl
    · cases hsh
  · cases hsh

include hp hctx hc hk hop hw in
theorem logic_3928
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3928
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3928.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (Clif.Sem.binary cop) a st2 := by
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
  | none => rw [match_3928_none hp ctx st tr m hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch; cases hmatch
  | some sh =>
  rw [match_3928 hp ctx st tr m hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_3928_none hp ctx st tr n (.inl hrx) _ _)
  | some rx =>
  cases hrz : ctx.valueReg? z with
  | none => exact absurd heval (rhs_3928_none hp ctx st tr n (.inr hrz) _ _)
  | some rz =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg z rz hrz
  obtain ⟨tr', he⟩ := rhs_3928 hp ctx hc st tr n hk hrx hrz hw
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
    obtain ⟨r, hr, hh⟩ := aluVal_holds_B hop.alu (szOf_bits hw) (hvals x _ (getAs_ok hx)) hB
    exact ⟨_, ispec_aluRRRShift hop.op8 hshl (Nat.lt_of_lt_of_le hamt (szOf_bits hw)) hr, hh⟩

include hp hctx hc hk hop hw in
theorem logic_3931
    (hmatch : (matchRule p (sem ctx) cfg (m + 10) rule_inst_3931
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) = .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg (n + 40) rule_inst_3931.rhs env).run s1 =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (Clif.Sem.binary cop) a st2 := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e2, -, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨e3, hpx, -⟩ := matchArgs_cons_inv ha
  obtain ⟨j1, info1, fs1, e5, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpx
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
  | none => rw [match_3931_none hp ctx st tr m hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch; cases hmatch
  | some sh =>
  rw [match_3931 hp ctx st tr m hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_3931_none hp ctx st tr n (.inl hry) _ _)
  | some ry =>
  cases hrz : ctx.valueReg? z with
  | none => exact absurd heval (rhs_3931_none hp ctx st tr n (.inr hrz) _ _)
  | some rz =>
  obtain rfl := hctx.valueReg y ry hry
  obtain rfl := hctx.valueReg z rz hrz
  obtain ⟨tr', he⟩ := rhs_3931 hp ctx hc st tr n hk hry hrz hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨.aluRRRShift op (szOf ty.width) (.vreg st.nextVreg .int) (.vreg y .int) (.vreg z .int) sh,
    by rw [fresh_fst], by rw [fresh_fst], _, operands_aluRRRShift _ _ _ _ _ _, rfl, ?_⟩
  intro fr ρ w hvals hdfg u v hx hy
  obtain ⟨u', hz, hshl, hamt, rfl⟩ :=
    ishl_const_value hdfg hw hj1 hij1 hcl1 hj2 hij2 hcl2 he3 hx hsh
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [vuseNums_aluRRRShift] at hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · exact getAs_isSome hy
    · exact getAs_isSome hz
  · have hB : (opnd (szOf ty.width) (ρ z) <<< sh.amt).setWidth ty.width = u' <<< sh.amt := by
      rw [BitVec.setWidth_shiftLeft_of_le (szOf_bits hw),
        opnd_setWidth_eq (szOf_bits hw) (hvals z _ (getAs_ok hz))]
    obtain ⟨r, hr, hh⟩ := aluVal_holds_B hop.alu (szOf_bits hw) (hvals y _ (getAs_ok hy)) hB
    refine ⟨_, ispec_aluRRRShift hop.op8 hshl (Nat.lt_of_lt_of_le hamt (szOf_bits hw)) hr, ?_⟩
    rw [hop.comm]
    exact hh

end Cases

/-- **Term contract of `alu_rs_imm_logic_commutative op ty x y`** (`op` = `and`/`orr`/`eor`):
whichever of its five rules fires, it emits one instruction computing `x cop y` into the fresh
vreg. -/
theorem aluRsImmLogicComm_ok {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {cfg : Config} (hc : cfg.checkOverlap = false) {k : Nat} {op : ALUOp}
    {cop : Clif.BinaryOp} (hk : ALUOp.ofIdx? k = some op) (hop : LogicPair op cop)
    {ty : Clif.Ty} (hw : ty.width ≤ 64) {x y n : Nat} {st st2 : LState} {tr tr2 : Array RuleId}
    {a : V}
    (h : (applyTerm p (sem ctx) cfg (n + 60) 27 565
      [.data 59 k [], .ty (.int ty.width), .value x, .value y]).run (st, tr) =
      .ok (some a, (st2, tr2))) :
    LogicOut ctx st ty x y (Clif.Sem.binary cop) a st2 := by
  obtain ⟨r, hr, m, env, s1, st', tr', hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some hc hp.t565 term_565_kind rfl h
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  rw [hp.r565] at hr hmn
  simp only [List.length_cons, List.length_nil] at hmn
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  have heval' : (evalExpr p (sem ctx) cfg ((n + 19) + 40) r.rhs env).run s1 =
      .ok (some a, (st2, tr')) := heval
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact logic_3923 hp hctx hc hk hop hw hmatch heval'
  · exact logic_3931 hp hctx hc hk hop hw hmatch heval'
  · exact logic_3920 hp hctx hc hk hop hw hmatch heval'
  · exact logic_3928 hp hctx hc hk hop hw hmatch heval'
  · exact logic_3916 hp hctx hc hk hop hw hmatch heval'

/-! ## The `band`/`bor`/`bxor` root rules -/

set_option maxRecDepth 20000 in
theorem variantNames_Band : (variantNames 151)[97]? = some "Band" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Bor : (variantNames 151)[98]? = some "Bor" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Bxor : (variantNames 151)[99]? = some "Bxor" := rfl

theorem LogicPair.noShift {op : ALUOp} {cop : Clif.BinaryOp} (h : LogicPair op cop) :
    cop.isShift = false := by
  rcases h with h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;> rfl

/-- **Template: a logic root rule** `(lower (cop (fits_in_64 (ty_int ty)) x y))` →
`(alu_rs_imm_logic_commutative op ty x y)`: its match and argument evaluation (forward lemmas)
plus the term contract give `LowerRuleOk`. -/
theorem logicRoot_ruleOk {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp} {op : ALUOp}
    {k : Nat} {n : String} {opT opT2 : TermId} {to : Term} {ko : Nat} {tyPat : Pattern}
    {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (hk : ALUOp.ofIdx? k = some op) (hop : LogicPair op cop)
    (hrhs : r.rhs = .term 25 172 [.term 27 565 [.term 59 opT2 [], .var 14 0, .var 15 1, .var 15 2]])
    (hmatchF : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x y st tr m,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] →
      (matchRule p (sem ctx) cfg (m + 2) r [.inst ii]).run (st, tr) =
        .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)))
    (hargsF : ∀ (ctx : Ctx) (cfg : Config) w x y st tr n,
      (evalArgs p (sem ctx) cfg (n+5) [.term 59 opT2 [], .var 14 0, .var 15 1, .var 15 2]
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some [.data 59 k [], .ty (.int w), .value x, .value y], (st, tr))) :
    ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
      Refines F isem → MRStable F MR → LowerRuleOk isem MR env cp p r := by
  intro F isem MR env cp hR hMR f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr'
    hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, -, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) hargs hto hko hname hcop hmatch
  rw [hmatchF ctx cfg ii info ty.width x y st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  rw [hrhs] at heval
  obtain ⟨vs, s2, a, s3, hvs, happ, hout⟩ := rhs_output_inv (n := N + 97) heval
  rw [show N + 97 = (N + 92) + 5 from rfl, hargsF ctx cfg ty.width x y st tr (N + 92)] at hvs
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hvs
  obtain ⟨rfl, rfl⟩ := hvs
  obtain ⟨st3, tr3⟩ := s3
  obtain ⟨mi, rfl, rfl, hone⟩ :=
    aluRsImmLogicComm_ok hp hctx hco hk hop hw (n := N + 37) happ
  rw [show N + 97 + 2 = (N + 89) + 10 from rfl, output_reg_run hp ctx hco] at hout
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hout
  obtain ⟨rfl, rfl, -⟩ := hout
  exact ⟨[mi], _, emitted_fresh_emit _ _, rfl,
    OneInstOk.lowerInstOk hR hMR hop.noShift (fun _ _ => rfl) hone⟩

set_option maxRecDepth 20000 in
/-- **`band_fits_in_64`** (`lower.isle:1412`), i8..i64: `and` / `and #imm` / `and …, lsl #k`. -/
theorem band_fits_in_64_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1412 :=
  logicRoot_ruleOk hp (cop := .band) (op := .and) (k := 4) rfl hp.t2381 term_2381_kind
    variantNames_Band rfl rfl (.inl rfl) rfl
    (fun ctx _ _ _ _ _ _ st tr m hi hty hw hd => match_1412 hp ctx hi hty hw hd st tr m)
    (fun ctx _ w x y st tr n => args_1412 hp ctx w x y st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bor_fits_in_64`** (`lower.isle:1449`), i8..i64: `orr` / `orr #imm` / `orr …, lsl #k`. -/
theorem bor_fits_in_64_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1449 :=
  logicRoot_ruleOk hp (cop := .bor) (op := .orr) (k := 2) rfl hp.t2382 term_2382_kind
    variantNames_Bor rfl rfl (.inr (.inl rfl)) rfl
    (fun ctx _ _ _ _ _ _ st tr m hi hty hw hd => match_1449 hp ctx hi hty hw hd st tr m)
    (fun ctx _ w x y st tr n => args_1449 hp ctx w x y st tr n) F isem MR env cp hR hMR

set_option maxRecDepth 20000 in
/-- **`bxor_fits_in_64`** (`lower.isle:1516`), i8..i64: `eor` / `eor #imm` / `eor …, lsl #k`. -/
theorem bxor_fits_in_64_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1516 :=
  logicRoot_ruleOk hp (cop := .bxor) (op := .eor) (k := 7) rfl hp.t2383 term_2383_kind
    variantNames_Bxor rfl rfl (.inr (.inr rfl)) rfl
    (fun ctx _ _ _ _ _ _ st tr m hi hty hw hd => match_1516 hp ctx hi hty hw hd st tr m)
    (fun ctx _ w x y st tr n => args_1516 hp ctx w x y st tr n) F isem MR env cp hR hMR

/-- **iadd_ishl_right** (`lower.isle:116`, `iadd x (ishl y (iconst k))` → `add x, y, lsl #k`), i8..i64. -/
theorem iadd_ishl_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_116 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, -, hsh0⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e5, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hsh0
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
  | none =>
    rw [match_116_none hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
    cases hmatch
  | some sh =>
  rw [match_116 hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrr : ctx.valueReg? x with
  | none => exact absurd heval (rhs_116_none hp ctx st tr n' (.inl hrr) _ _)
  | some rr =>
  cases hrz : ctx.valueReg? z with
  | none => exact absurd heval (rhs_116_none hp ctx st tr n' (.inr hrz) _ _)
  | some rz =>
  obtain rfl := hctx.valueReg x rr hrr
  obtain rfl := hctx.valueReg z rz hrz
  obtain ⟨tr'', he⟩ := rhs_116 hp ctx hco st tr n' hrr hrz hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine OneInstOk.lowerInstOk hR hMR rfl (fun _ _ => rfl)
    ⟨_, operands_aluRRRShift _ _ _ _ _ _, rfl, ?_⟩
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
    obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .add) (cop := .iadd) (by simp)
      (szOf_bits hw) (hvals x _ (getAs_ok hx)) hB
    refine ⟨_, ispec_aluRRRShift (by simp) hshl (Nat.lt_of_lt_of_le hamt (szOf_bits hw)) hr, ?_⟩
    exact hh

/-- **iadd_ishl_left** (`lower.isle:120`, `iadd (ishl x (iconst k)) y` → `add y, x, lsl #k`), i8..i64. -/
theorem iadd_ishl_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_120 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hsh0, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e5, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hsh0
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
  | none =>
    rw [match_120_none hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
    cases hmatch
  | some sh =>
  rw [match_120 hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrr : ctx.valueReg? y with
  | none => exact absurd heval (rhs_120_none hp ctx st tr n' (.inl hrr) _ _)
  | some rr =>
  cases hrz : ctx.valueReg? z with
  | none => exact absurd heval (rhs_120_none hp ctx st tr n' (.inr hrz) _ _)
  | some rz =>
  obtain rfl := hctx.valueReg y rr hrr
  obtain rfl := hctx.valueReg z rz hrz
  obtain ⟨tr'', he⟩ := rhs_120 hp ctx hco st tr n' hrr hrz hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine OneInstOk.lowerInstOk hR hMR rfl (fun _ _ => rfl)
    ⟨_, operands_aluRRRShift _ _ _ _ _ _, rfl, ?_⟩
  intro fr ρ w hvals hdfg u v hx hy
  obtain ⟨u', hz, hshl, hamt, rfl⟩ :=
    ishl_const_value hdfg hw hj1 hij1 hcl1 hj2 hij2 hcl2 he3 hx hsh
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [vuseNums_aluRRRShift] at hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · exact getAs_isSome hy
    · exact getAs_isSome hz
  · have hB : (opnd (szOf ty.width) (ρ z) <<< sh.amt).setWidth ty.width = u' <<< sh.amt := by
      rw [BitVec.setWidth_shiftLeft_of_le (szOf_bits hw),
        opnd_setWidth_eq (szOf_bits hw) (hvals z _ (getAs_ok hz))]
    obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .add) (cop := .iadd) (by simp)
      (szOf_bits hw) (hvals y _ (getAs_ok hy)) hB
    refine ⟨_, ispec_aluRRRShift (by simp) hshl (Nat.lt_of_lt_of_le hamt (szOf_bits hw)) hr, ?_⟩
    show VHolds ⟨ty, _ + _⟩ _
    rw [BitVec.add_comm]
    exact hh

/-- **isub_ishl** (`lower.isle:821`, `isub x (ishl y (iconst k))` → `sub x, y, lsl #k`), i8..i64. -/
theorem isub_ishl_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_821 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, -, hsh0⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e5, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hsh0
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
  | none =>
    rw [match_821_none hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
    cases hmatch
  | some sh =>
  rw [match_821 hp ctx st tr m' hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hsh] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrr : ctx.valueReg? x with
  | none => exact absurd heval (rhs_821_none hp ctx st tr n' (.inl hrr) _ _)
  | some rr =>
  cases hrz : ctx.valueReg? z with
  | none => exact absurd heval (rhs_821_none hp ctx st tr n' (.inr hrz) _ _)
  | some rz =>
  obtain rfl := hctx.valueReg x rr hrr
  obtain rfl := hctx.valueReg z rz hrz
  obtain ⟨tr'', he⟩ := rhs_821 hp ctx hco st tr n' hrr hrz hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine OneInstOk.lowerInstOk hR hMR rfl (fun _ _ => rfl)
    ⟨_, operands_aluRRRShift _ _ _ _ _ _, rfl, ?_⟩
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
    obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .sub) (cop := .isub) (by simp)
      (szOf_bits hw) (hvals x _ (getAs_ok hx)) hB
    refine ⟨_, ispec_aluRRRShift (by simp) hshl (Nat.lt_of_lt_of_le hamt (szOf_bits hw)) hr, ?_⟩
    exact hh

end Backend.Proof
