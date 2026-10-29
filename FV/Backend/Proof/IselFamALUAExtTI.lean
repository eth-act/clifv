module

public import FV.Backend.Proof.IselFamALUAExt
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamALUATI

@[expose] public section

/-!
# `IselFamALUAExt` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamALUAExt`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
/-- **`iadd_extend_right`** (`lower.isle:108`, `iadd x (extend y)` → `add x, y, {u,s}xt*`), i8..i64. -/
theorem iadd_extend_right_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_108 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨fs, hx0, -⟩ := matchPat_extract_inv hp.t345 term_345_kind rfl hpy
  rw [sem_extract] at hx0
  obtain ⟨op, ty', x', b, e, hdc, hvt, he, rfl⟩ := ext_extended_inv ctx _ hx0
  rw [match_108 hp ctx st tr m' hi hhead hw hd hdc hvt he] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_108_none hp ctx hco st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hrx' : ctx.valueReg? x' with
  | none => exact absurd heval (rhs_108_none hp ctx hco st tr n' (.inr hrx') _ _)
  | some rx' =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI x' rx' hrx'
  obtain ⟨tr'', he'⟩ := rhs_108 hp ctx hco st tr n' hrx hrx' hw
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨a, ha, hab, rfl⟩ := extend_value hdfg hdc hvt hy
  have hB := extendVal_holds he hab (hvals x' a ha) (n := (szOf ty.width).bits) (szOf_bits hw)
  obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .add) (cop := .iadd) (by simp) (szOf_bits hw)
    (hvals x _ (getAs_ok hx)) hB
  refine ⟨fun z hz => ?_, _, ispec_aluRRRExtend (.inl rfl) hr, hh⟩
  rw [vuseNums_aluRRRExtend] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl
  · exact getAs_isSome hx
  · simp [ha]

/-- **`iadd_extend_left`** (`lower.isle:111`, `iadd (extend x) y` → `add y, x, {u,s}xt*`), i8..i64. -/
theorem iadd_extend_left_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_111 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨fs, hx0, -⟩ := matchPat_extract_inv hp.t345 term_345_kind rfl hpx
  rw [sem_extract] at hx0
  obtain ⟨op, ty', x', b, e, hdc, hvt, he, rfl⟩ := ext_extended_inv ctx _ hx0
  rw [match_111 hp ctx st tr m' hi hhead hw hd hdc hvt he] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_111_none hp ctx hco st tr n' (.inl hry) _ _)
  | some ry =>
  cases hrx' : ctx.valueReg? x' with
  | none => exact absurd heval (rhs_111_none hp ctx hco st tr n' (.inr hrx') _ _)
  | some rx' =>
  obtain rfl := hctx.valueRegI y ry hry
  obtain rfl := hctx.valueRegI x' rx' hrx'
  obtain ⟨tr'', he'⟩ := rhs_111 hp ctx hco st tr n' hry hrx' hw
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨a, ha, hab, rfl⟩ := extend_value hdfg hdc hvt hx
  have hB := extendVal_holds he hab (hvals x' a ha) (n := (szOf ty.width).bits) (szOf_bits hw)
  obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .add) (cop := .iadd) (by simp) (szOf_bits hw)
    (hvals y _ (getAs_ok hy)) hB
  refine ⟨fun z hz => ?_, _, ispec_aluRRRExtend (.inl rfl) hr, ?_⟩
  · rw [vuseNums_aluRRRExtend] at hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact getAs_isSome hy
    · simp [ha]
  · show VHolds ⟨ty, _ + _⟩ _
    rw [BitVec.add_comm]
    exact hh

/-- **`isub_extend`** (`lower.isle:816`, `isub x (extend y)` → `sub x, y, {u,s}xt*`), i8..i64. -/
theorem isub_extend_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_816 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 9) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨fs, hx0, -⟩ := matchPat_extract_inv hp.t345 term_345_kind rfl hpy
  rw [sem_extract] at hx0
  obtain ⟨op, ty', x', b, e, hdc, hvt, he, rfl⟩ := ext_extended_inv ctx _ hx0
  rw [match_816 hp ctx st tr m' hi hhead hw hd hdc hvt he] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_816_none hp ctx hco st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hrx' : ctx.valueReg? x' with
  | none => exact absurd heval (rhs_816_none hp ctx hco st tr n' (.inr hrx') _ _)
  | some rx' =>
  obtain rfl := hctx.valueRegI x rx hrx
  obtain rfl := hctx.valueRegI x' rx' hrx'
  obtain ⟨tr'', he'⟩ := rhs_816 hp ctx hco st tr n' hrx hrx' hw
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨a, ha, hab, rfl⟩ := extend_value hdfg hdc hvt hy
  have hB := extendVal_holds he hab (hvals x' a ha) (n := (szOf ty.width).bits) (szOf_bits hw)
  obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .sub) (cop := .isub) (by simp) (szOf_bits hw)
    (hvals x _ (getAs_ok hx)) hB
  refine ⟨fun z hz => ?_, _, ispec_aluRRRExtend (.inr rfl) hr, hh⟩
  rw [vuseNums_aluRRRExtend] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl
  · exact getAs_isSome hx
  · simp [ha]

end Backend.Proof
