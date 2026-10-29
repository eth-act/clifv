module

public import FV.Backend.Proof.IselFamALUAExtr
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamALUATI

@[expose] public section

/-!
# `IselFamALUAExtr` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamALUAExtr`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000 in
/-- **`extr_32_or_64`** (`lower.isle:1501`, `bor (ishl x (iconst xs)) (ushr y (iconst ys))` → `extr x, y, #ys`), I32/I64. -/
theorem extr_32_or_64_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1501 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
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
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI y ry hry
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
theorem extr_32_or_64_2_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1507 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
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
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI y ry hry
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
