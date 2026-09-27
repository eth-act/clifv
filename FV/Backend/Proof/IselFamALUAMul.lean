import FV.Backend.Proof.IselTermsALUAMul
import FV.Backend.Proof.IselFamALUALogicNot
import FV.Backend.Proof.IselFamALUARules

/-!
# Multiplication root rules of family A: `LowerRuleOk`

`smulhi_64` (1056), `umulhi_64` (1068): one `smulh`/`umulh` at I64 (the rules' type pattern is
the constant `I64`; at any other width the match fails, `match_*_ne`). `imul_base_case` (871):
`madd x, y, xzr` at every width i8..i64. The fusions `iadd_imul_right` (125), `iadd_imul_left`
(128), `isub_imul` (132) look through the `imul` defining an operand (`binary_value`) and emit
one `madd`/`msub`. Width lemmas: `holds_madd`, `holds_msub`, `holds_mul0` (low bits of a product
depend only on the low bits of the factors), `smulh_holds`/`umulh_holds` (64-bit, exact).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000 in
theorem variantNames_Smulhi : (variantNames 151)[79]? = some "Smulhi" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Umulhi : (variantNames 151)[78]? = some "Umulhi" := rfl

/-! ## Instruction forms -/

theorem operands_aluRRRR (op : ALUOp3) (sz : OperandSize) (d x y z : Nat) :
    (MInst.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) (.vreg z .int)).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩,
        ⟨y, .int, .use, .early, .reg⟩, ⟨z, .int, .use, .early, .reg⟩] := rfl

theorem vuseNums_aluRRRR (op : ALUOp3) (sz : OperandSize) (d x y z : Nat) :
    vuseNums (.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) (.vreg z .int)) =
      [x, y, z] := rfl

theorem operands_aluRRRR_xzr (op : ALUOp3) (sz : OperandSize) (d x y : Nat) :
    (MInst.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) .xzr).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩,
        ⟨y, .int, .use, .early, .reg⟩] := rfl

theorem vuseNums_aluRRRR_xzr (op : ALUOp3) (sz : OperandSize) (d x y : Nat) :
    vuseNums (.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) .xzr) = [x, y] := rfl

theorem ispec_aluRRRR {op : ALUOp3} {sz : OperandSize} {d : Nat} {rn rm ra : Reg} {a b c : CV}
    {w : Arm.ArmState} {r : BitVec sz.bits}
    (hv : mulAddVal op (opnd sz a) (opnd sz b) (opnd sz c) = some r) :
    ispec (.aluRRRR op sz (.vreg d .int) rn rm ra) [a, b, c] w = some ([resX sz r], w, .next) := by
  simp only [ispec, hv, Option.map_some]
  rfl

theorem ispec_aluRRRR_xzr {op : ALUOp3} {sz : OperandSize} {d x y : Nat} {a b : CV}
    {w : Arm.ArmState} {r : BitVec sz.bits}
    (hv : mulAddVal op (opnd sz a) (opnd sz b) 0 = some r) :
    ispec (.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) .xzr) [a, b] w =
      some ([resX sz r], w, .next) := by
  simp only [ispec, hv, Option.map_some]
  rfl

/-! ## Width lemmas -/

theorem holds_madd {ty : Clif.Ty} {sz : OperandSize} (hw : ty.width ≤ sz.bits) {a b c : CV}
    {u v t : BitVec ty.width} (ha : VHolds ⟨ty, u⟩ a) (hb : VHolds ⟨ty, v⟩ b)
    (hc : VHolds ⟨ty, t⟩ c) :
    VHolds ⟨ty, t + u * v⟩ (resX sz (opnd sz c + opnd sz a * opnd sz b)) := by
  have h64 := opSize_bits_le sz
  simp only [VHolds] at ha hb hc ⊢
  rw [resX_setWidth hw h64, BitVec.setWidth_add _ _ hw, BitVec.setWidth_mul _ _ hw,
    opnd_setWidth hw h64, opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb, hc]

theorem holds_msub {ty : Clif.Ty} {sz : OperandSize} (hw : ty.width ≤ sz.bits) {a b c : CV}
    {u v t : BitVec ty.width} (ha : VHolds ⟨ty, u⟩ a) (hb : VHolds ⟨ty, v⟩ b)
    (hc : VHolds ⟨ty, t⟩ c) :
    VHolds ⟨ty, t - u * v⟩ (resX sz (opnd sz c - opnd sz a * opnd sz b)) := by
  have h64 := opSize_bits_le sz
  simp only [VHolds] at ha hb hc ⊢
  rw [resX_setWidth hw h64, setWidth_sub_of_le hw, BitVec.setWidth_mul _ _ hw,
    opnd_setWidth hw h64, opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb, hc]

theorem holds_mul0 {ty : Clif.Ty} {sz : OperandSize} (hw : ty.width ≤ sz.bits) {a b : CV}
    {u v : BitVec ty.width} (ha : VHolds ⟨ty, u⟩ a) (hb : VHolds ⟨ty, v⟩ b) :
    VHolds ⟨ty, u * v⟩ (resX sz (0 + opnd sz a * opnd sz b)) := by
  have h64 := opSize_bits_le sz
  simp only [VHolds] at ha hb ⊢
  have h0 : (0 : BitVec sz.bits) + opnd sz a * opnd sz b = opnd sz a * opnd sz b := by simp
  rw [resX_setWidth hw h64, h0, BitVec.setWidth_mul _ _ hw,
    opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb]

theorem opnd64_eq {a : CV} {u : BitVec 64} (ha : a.setWidth 64 = u) : opnd .size64 a = u := by
  show (a.setWidth 64).setWidth 64 = u
  rw [BitVec.setWidth_eq, ha]

theorem resX64_setWidth (r : BitVec 64) : (resX .size64 r).setWidth 64 = r := by
  show ((r.setWidth 64).setWidth 128).setWidth 64 = r
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [BitVec.setWidth_eq]

theorem smulh_holds {a b : CV} {u v : BitVec 64} (ha : a.setWidth 64 = u) (hb : b.setWidth 64 = v) :
    (resX .size64 (((opnd .size64 a).signExtend 128 * (opnd .size64 b).signExtend 128).extractLsb'
      64 64)).setWidth 64 = Clif.Sem.smulhi u v := by
  rw [resX64_setWidth]
  have e1 := opnd64_eq ha
  have e2 := opnd64_eq hb
  simp only [OperandSize.bits] at e1 e2
  rw [e1, e2]
  rfl

theorem umulh_holds {a b : CV} {u v : BitVec 64} (ha : a.setWidth 64 = u) (hb : b.setWidth 64 = v) :
    (resX .size64 (((opnd .size64 a).zeroExtend 128 * (opnd .size64 b).zeroExtend 128).extractLsb'
      64 64)).setWidth 64 = Clif.Sem.umulhi u v := by
  rw [resX64_setWidth]
  have e1 := opnd64_eq ha
  have e2 := opnd64_eq hb
  simp only [OperandSize.bits] at e1 e2
  rw [e1, e2]
  rfl

/-- **The value of a looked-through two-operand instruction** `cop a b` (not a shift) read at
the instruction's type. -/
theorem binary_value {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {y j a b : Nat}
    {infoj : IInfo} {cop : Clif.BinaryOp} {ty1 ty : Clif.Ty} {v : BitVec ty.width}
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hcl : infoj.clif = some (.binary cop ty1 a b)) (hs : cop.isShift = false)
    (hy : fr.getAs y ty = .ok v) :
    ∃ u w, fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok w ∧ v = Clif.Sem.binary cop u w := by
  obtain ⟨vals, hev, hl⟩ := hdfg.1 y j infoj _ _ hj hij hcl rfl (getAs_ok hy)
  obtain ⟨u, w, ha, hb, rfl⟩ := evalInst_binary_inv hs (hev default)
  have hv := lookup_zip_single hl
  cases hv
  exact ⟨u, w, ha, hb, rfl⟩

theorem ty_i64_of_width {ty : Clif.Ty} (h : ty.width = 64) : ty = .i64 := by
  cases ty <;> simp [Clif.Ty.width] at h ⊢

/-! ## `smulhi_64`, `umulhi_64` -/

set_option maxRecDepth 20000 in
/-- **`smulhi_64`** (`lower.isle:1056`, `smulhi.i64 x y` → `smulh`). -/
theorem smulhi_64_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1056 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, -, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .smulhi) rfl hp.t2363 term_2363_kind
      variantNames_Smulhi rfl hmatch
  by_cases h64 : ty.width ≠ 64
  · rw [match_1056_ne hp ctx st tr m' hi hhead h64 hd] at hmatch; cases hmatch
  obtain rfl := ty_i64_of_width (Decidable.of_not_not h64)
  rw [match_1056 hp ctx st tr m' hi hhead hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_1056_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_1056_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
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
theorem umulhi_64_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1068 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, -, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .umulhi) rfl hp.t2362 term_2362_kind
      variantNames_Umulhi rfl hmatch
  by_cases h64 : ty.width ≠ 64
  · rw [match_1068_ne hp ctx st tr m' hi hhead h64 hd] at hmatch; cases hmatch
  obtain rfl := ty_i64_of_width (Decidable.of_not_not h64)
  rw [match_1068 hp ctx st tr m' hi hhead hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_1068_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_1068_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
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

/-! ## `imul_base_case` -/

/-- **`imul_base_case`** (`lower.isle:871`, `imul x y` → `madd x, y, xzr`), i8..i64. -/
theorem imul_base_case_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_871 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, -, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .imul) rfl hp.t2361 term_2361_kind
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
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
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

/-! ## Multiply-add fusions -/

/-- **`iadd_imul_right`** (`lower.isle:125`, `iadd x (imul y z)` → `madd y, z, x`), i8..i64. -/
theorem iadd_imul_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_125 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2361 term_2361_kind hpy
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clif hctx hj hij
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
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg a ra hra
  obtain rfl := hctx.valueReg b rb hrb
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
theorem iadd_imul_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_128 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2361 term_2361_kind hpx
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clif hctx hj hij
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
  obtain rfl := hctx.valueReg a ra hra
  obtain rfl := hctx.valueReg b rb hrb
  obtain rfl := hctx.valueReg y ry hry
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
theorem isub_imul_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_132 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2361 term_2361_kind hpy
  obtain ⟨cl, hcl, hdatj⟩ := ctxInv_clif hctx hj hij
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
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg a ra hra
  obtain rfl := hctx.valueReg b rb hrb
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
