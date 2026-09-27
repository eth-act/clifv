import FV.Backend.Proof.IselTermsALUAExtr
import FV.Backend.Proof.IselFamALUAExt

/-!
# `extr_32_or_64` root rules (1501, 1507): `LowerRuleOk`

`bor (ishl x (iconst xs)) (ushr y (iconst ys))` (and the mirrored `bor`) at I32/I64 with
`xs + ys = w`, `xs, ys > 0` → `extr x, y, #ys`. The looked-through shifts are evaluated by
`DFGCons` (`shift_const_value`); `extr_bits` is the bit-level identity
`((u ++ v) >>> ys).setWidth w = (u <<< xs) ||| (v >>> ys)`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000 in
theorem variantNames_Ushr : (variantNames 151)[104]? = some "Ushr" := rfl

/-- **The value of a looked-through shift by a constant** `cop z (iconst c)` read at the
instruction's type. -/
theorem shift_const_value {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {y z b j1 j2 : Nat}
    {info1 info2 : IInfo} {cop : Clif.BinaryOp} {ty1 ty3 ty : Clif.Ty} {c3 : BitVec ty3.width}
    {v : BitVec ty.width} (hs : cop.isShift = true)
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hcl1 : info1.clif = some (.binary cop ty1 z b))
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hcl2 : info2.clif = some (.iconst ty3 c3)) (hy : fr.getAs y ty = .ok v) :
    ∃ u', fr.getAs z ty = .ok u' ∧ Clif.Sem.shift cop u' c3 = some v := by
  obtain ⟨vals, hev, hl⟩ := hdfg.1 y j1 info1 _ _ hj1 hij1 hcl1 rfl (getAs_ok hy)
  obtain ⟨u', bv, r', hz, hb, hr', rfl⟩ := evalInst_shift_inv hs (hev default)
  have hv := lookup_zip_single hl
  cases hv
  have hbv := dfg_single hdfg hj2 hij2 hcl2 rfl (get_ok hb) (a := ⟨ty3, c3⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  subst hbv
  exact ⟨u', hz, hr'⟩

theorem extr_bits {w : Nat} (u v : BitVec w) {X Y : Nat} (hs : X + Y = w) :
    ((u ++ v) >>> Y).setWidth w = (u <<< X) ||| (v >>> Y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases h1 : Y + i < w
  · have h2 : i < X := by omega
    simp [h1, h2]
  · have h2 : ¬ i < X := by omega
    have h3 : v.getLsbD (Y + i) = false := BitVec.getLsbD_of_ge v _ (by omega)
    have h4 : Y + i - w = i - X := by omega
    simp [h1, h2, h3, h4]

theorem ispec_extr {sz : OperandSize} {d : Nat} {rn rm : Reg} {sh : ShiftOpAndAmt} {a b : CV}
    {w : Arm.ArmState} (h : sh.amt < sz.bits) :
    ispec (.aluRRRShift .extr sz (.vreg d .int) rn rm sh) [a, b] w =
      some ([resX sz (((opnd sz a ++ opnd sz b) >>> sh.amt).setWidth sz.bits)], w, .next) := by
  simp only [ispec, h, ↓reduceIte]
  rfl

theorem extr_holds {ty : Clif.Ty} (hw : ty.width = 32 ∨ ty.width = 64) {a b : CV}
    {u v : BitVec ty.width} (ha : VHolds ⟨ty, u⟩ a) (hb : VHolds ⟨ty, v⟩ b) {X Y : Nat}
    (hs : X + Y = ty.width) :
    VHolds ⟨ty, (u <<< X) ||| (v >>> Y)⟩
      (resX (szOf ty.width) (((opnd (szOf ty.width) a ++ opnd (szOf ty.width) b) >>> Y).setWidth
        (szOf ty.width).bits)) := by
  have hsz : (szOf ty.width).bits = ty.width := by
    rcases hw with h | h <;> simp [szOf, h, OperandSize.bits]
  have hle : ty.width ≤ (szOf ty.width).bits := by omega
  have ea := opnd_setWidth_eq hle ha
  have eb := opnd_setWidth_eq hle hb
  simp only [VHolds] at ha hb ⊢
  rw [resX_setWidth hle (opSize_bits_le _)]
  generalize opnd (szOf ty.width) a = A at ea ⊢
  generalize opnd (szOf ty.width) b = B at eb ⊢
  generalize (szOf ty.width).bits = n at hsz hle A B ea eb ⊢
  subst hsz
  simp only [BitVec.setWidth_eq] at ea eb ⊢
  subst ea eb
  exact extr_bits A B hs

theorem u64_small {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) : ((u64 z : Nat) : Int) = z := by
  unfold u64
  rw [Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

/-- The arithmetic the `extr` conditions give: `X + Y = w` as naturals, both positive. -/
theorem extrOk_nat {w : Nat} {X Y : Int} (hw64 : w ≤ 64) (h : ExtrOk w X Y) :
    X.toNat + Y.toNat = w ∧ 0 < X.toNat ∧ 0 < Y.toNat ∧ Y < 64 ∧ X = X.toNat ∧ Y = Y.toNat := by
  obtain ⟨⟨hx0, hx8⟩, ⟨hy0, hy8⟩, hsum, hxp, hyp⟩ := h
  have hs := beq_iff_eq.mp hsum
  rw [u64_small (by omega) (by omega)] at hs
  omega

set_option maxRecDepth 20000 in
/-- **`extr_32_or_64`** (`lower.isle:1501`, `bor (ishl x (iconst xs)) (ushr y (iconst ys))` → `extr x, y, #ys`), I32/I64. -/
theorem extr_32_or_64_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1501 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
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
  obtain ⟨hsum, hXp, hYp, hY64, -, -⟩ := extrOk_nat (by omega) hok
  have hX : ((u64 (imm64OfIconst ty3 k3) : Nat) : Int).toNat = k3.toNat := by
    rw [Int.toNat_natCast, u64_imm64OfIconst (eTy_width he3)]
  have hY : ((u64 (imm64OfIconst ty4 k4) : Nat) : Int).toNat = k4.toNat := by
    rw [Int.toNat_natCast, u64_imm64OfIconst (eTy_width he4)]
  rw [hX, hY] at hsum
  rw [hX] at hXp
  rw [hY] at hYp
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_1501_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_1501_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
  obtain ⟨tr'', sh, hsh, he'⟩ := rhs_1501 hp ctx hco st tr n' hrx hry hw hY64
  rw [hY] at hsh
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨u1, hz1, hs1⟩ := shift_const_value hdfg rfl hj1 hij1 hcl1 hj2 hij2 hcl2 hx
  obtain ⟨u2, hz2, hs2⟩ := shift_const_value hdfg rfl hj3 hij3 hcl3 hj4 hij4 hcl4 hy
  simp only [Clif.Sem.shift, Option.some.injEq] at hs1 hs2
  subst hs1 hs2
  have hsz : (szOf ty.width).bits = ty.width := by
    rcases hw with h | h <;> simp [szOf, h, OperandSize.bits]
  refine ⟨fun q hq => ?_, _, ispec_extr (by rw [hsh, hsz]; omega), ?_⟩
  · rw [vuseNums_aluRRRShift] at hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · first | exact getAs_isSome hz1 | exact getAs_isSome hz2
    · first | exact getAs_isSome hz1 | exact getAs_isSome hz2
  · have hmX : k3.toNat % ty.width = k3.toNat := Nat.mod_eq_of_lt (by omega)
    have hmY : k4.toNat % ty.width = k4.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hsh]
    show VHolds ⟨ty, Clif.Sem.bor _ _⟩ _
    simp only [Clif.Sem.bor, Clif.Sem.ishl, Clif.Sem.ushr, Clif.Sem.shiftAmt, hmX, hmY]
    exact extr_holds hw (hvals x _ (getAs_ok hz1)) (hvals y _ (getAs_ok hz2)) hsum

set_option maxRecDepth 20000 in
/-- **`extr_32_or_64_2`** (`lower.isle:1507`, `bor (ushr y (iconst ys)) (ishl x (iconst xs))` → `extr x, y, #ys`), I32/I64. -/
theorem extr_32_or_64_2_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1507 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
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
  obtain ⟨hsum, hXp, hYp, hY64, -, -⟩ := extrOk_nat (by omega) hok
  have hX : ((u64 (imm64OfIconst ty3 k3) : Nat) : Int).toNat = k3.toNat := by
    rw [Int.toNat_natCast, u64_imm64OfIconst (eTy_width he3)]
  have hY : ((u64 (imm64OfIconst ty4 k4) : Nat) : Int).toNat = k4.toNat := by
    rw [Int.toNat_natCast, u64_imm64OfIconst (eTy_width he4)]
  rw [hX, hY] at hsum
  rw [hX] at hXp
  rw [hY] at hYp
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_1507_none hp ctx st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_1507_none hp ctx st tr n' (.inr hry) _ _)
  | some ry =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
  obtain ⟨tr'', sh, hsh, he'⟩ := rhs_1507 hp ctx hco st tr n' hrx hry hw hY64
  rw [hY] at hsh
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨u1, hz1, hs1⟩ := shift_const_value hdfg rfl hj1 hij1 hcl1 hj2 hij2 hcl2 hx
  obtain ⟨u2, hz2, hs2⟩ := shift_const_value hdfg rfl hj3 hij3 hcl3 hj4 hij4 hcl4 hy
  simp only [Clif.Sem.shift, Option.some.injEq] at hs1 hs2
  subst hs1 hs2
  have hsz : (szOf ty.width).bits = ty.width := by
    rcases hw with h | h <;> simp [szOf, h, OperandSize.bits]
  refine ⟨fun q hq => ?_, _, ispec_extr (by rw [hsh, hsz]; omega), ?_⟩
  · rw [vuseNums_aluRRRShift] at hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · first | exact getAs_isSome hz1 | exact getAs_isSome hz2
    · first | exact getAs_isSome hz1 | exact getAs_isSome hz2
  · have hmX : k3.toNat % ty.width = k3.toNat := Nat.mod_eq_of_lt (by omega)
    have hmY : k4.toNat % ty.width = k4.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hsh]
    show VHolds ⟨ty, Clif.Sem.bor _ _⟩ _
    simp only [Clif.Sem.bor, Clif.Sem.ishl, Clif.Sem.ushr, Clif.Sem.shiftAmt, hmX, hmY]
    rw [BitVec.or_comm]
    exact extr_holds hw (hvals x _ (getAs_ok hz2)) (hvals y _ (getAs_ok hz1)) hsum

end Backend.Proof
