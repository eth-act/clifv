import FV.Backend.Proof.IselFamAluBPopcnt
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamAluBBaseTI

/-!
# `IselFamAluBPopcnt` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBPopcnt`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Ctor
variable (ctx : Ctx) (st : LState)
end Ctor
section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end Terms
section Run
variable {F : BitVec 64 → Prop} {isem : Sem}
end Run
section Shapes
variable {d x y : Nat} {c1 c2 c3 : RegClass}
end Shapes
section Rules
variable {F : BitVec 64 → Prop} {isem : Sem}
set_option maxHeartbeats 1000000 in
/-- **`popcnt_64`** (`lower.isle:2092`). -/
theorem popcnt_64_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2092 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, rfl, hety, -, hd, hhead⟩ := unary_frontTI hp (cop := .popcnt) rfl hp.t2395
    term_2395_kind variantNames_Popcnt_fb rfl hctx hi hc (m := m' + 9) hmatch
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_2092] at hmatch heval
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 29 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
  subst hdat
  have hty := ‹CTy.int 64 = CTy.int ty.width›
  simp only [CTy.int.injEq] at hty
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_reg _ _ = _›
  obtain rfl := hctx.valueRegI x _ hrx
  have hxlt := vreg_lt hvb hrx
  have h1 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
  obtain ⟨rfl, m1, hm1, hs1⟩ := mov_to_fpu_ok hp' hco (by omega) (.inr rfl) h1
  have h2 := ‹ApplyInternal _ _ _ _ 27 524 _ _ _ _›
  obtain ⟨rfl, m2, hm2, hs2⟩ := vec_cnt_ok hp' hco (by omega) h2
  have h3 := ‹ApplyInternal _ _ _ _ 27 473 _ _ _ _›
  obtain ⟨rfl, m3, hm3, hs3⟩ := addv_ok hp' hco (by omega) h3
  have h4 := ‹ApplyInternal _ _ _ _ 27 414 _ _ _ _›
  obtain ⟨rfl, m4, hm4, hs4⟩ := mov_from_vec_ok hp' hco (by omega) h4
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  rw [hs3] at hm4 hs4
  rw [hs2] at hm3 hs3 hm4 hs4
  rw [hs1] at hm2 hs2 hm3 hs3 hm4 hs4
  rename LState => st0
  have e1 : m1 = .movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size64 :=
    Option.some.inj (hm1.symm.trans rfl)
  subst e1
  have e2 : m2 = .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float)
      .size8x8 := Option.some.inj (hm2.symm.trans rfl)
  subst e2
  have e3 : m3 = .vecLanes .addv (.vreg (st0.nextVreg + 2) .float)
      (.vreg (st0.nextVreg + 1) .float) .size8x8 := Option.some.inj (hm3.symm.trans rfl)
  subst e3
  have e4 : m4 = .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0
      .size8 := Option.some.inj (hm4.symm.trans rfl)
  subst e4
  have hst' := hst.trans hs4
  simp only at hst'
  rw [hs3]
  have hsh : CodeShapeU st0 st'
      [.movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size64,
       .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float) .size8x8,
       .vecLanes .addv (.vreg (st0.nextVreg + 2) .float) (.vreg (st0.nextVreg + 1) .float) .size8x8,
       .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0 .size8]
      (st0.nextVreg + 3) [x] :=
    codeShapeU_of (k := 4) (by rw [hst']; simp only [LState.emit, LState.fresh]; apply Array.ext'; simp)
      (by rw [hst']; rfl) (by omega) (by vec_facts) (by vec_facts)
  refine ⟨_, hsh.emitted, _, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  have ho' : Clif.evalInst fr cm (.unary .popcnt ty x) = .ok (vals, cm') := ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho'
  refine ⟨rfl, usesOk_of [x] hsh.uses (by simp [getAs_ok hu]), .inl hsh.res, _, _, rfl,
    prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl)
      (prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl) (prun_nil _)))), ?_⟩
  have hX : (ρ x).setWidth ty.width = u := hvals x _ (getAs_ok hu)
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  simp only [VHolds, upd, Clif.Sem.unary, Clif.Sem.popcnt, ↓reduceIte, Nat.left_eq_add,
    Nat.add_right_cancel_iff, Nat.add_eq_left, Nat.succ_ne_self, LState.emit, LState.fresh,
    Nat.add_left_cancel_iff, show (1 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide, show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 3 by decide]
  rw [← hX]
  exact popcnt64_fin (ρ x)

set_option maxHeartbeats 1000000 in
/-- **`popcnt_32`** (`lower.isle:2086`). -/
theorem popcnt_32_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2086 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, rfl, hety, -, hd, hhead⟩ := unary_frontTI hp (cop := .popcnt) rfl hp.t2395
    term_2395_kind variantNames_Popcnt_fb rfl hctx hi hc (m := m' + 9) hmatch
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_2086] at hmatch heval
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 29 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
  subst hdat
  have hty := ‹CTy.int 32 = CTy.int ty.width›
  simp only [CTy.int.injEq] at hty
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_reg _ _ = _›
  obtain rfl := hctx.valueRegI x _ hrx
  have hxlt := vreg_lt hvb hrx
  have h1 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
  obtain ⟨rfl, m1, hm1, hs1⟩ := mov_to_fpu_ok hp' hco (by omega) (.inl rfl) h1
  have h2 := ‹ApplyInternal _ _ _ _ 27 524 _ _ _ _›
  obtain ⟨rfl, m2, hm2, hs2⟩ := vec_cnt_ok hp' hco (by omega) h2
  have h3 := ‹ApplyInternal _ _ _ _ 27 473 _ _ _ _›
  obtain ⟨rfl, m3, hm3, hs3⟩ := addv_ok hp' hco (by omega) h3
  have h4 := ‹ApplyInternal _ _ _ _ 27 414 _ _ _ _›
  obtain ⟨rfl, m4, hm4, hs4⟩ := mov_from_vec_ok hp' hco (by omega) h4
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  rw [hs3] at hm4 hs4
  rw [hs2] at hm3 hs3 hm4 hs4
  rw [hs1] at hm2 hs2 hm3 hs3 hm4 hs4
  rename LState => st0
  have e1 : m1 = .movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size32 :=
    Option.some.inj (hm1.symm.trans rfl)
  subst e1
  have e2 : m2 = .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float)
      .size8x8 := Option.some.inj (hm2.symm.trans rfl)
  subst e2
  have e3 : m3 = .vecLanes .addv (.vreg (st0.nextVreg + 2) .float)
      (.vreg (st0.nextVreg + 1) .float) .size8x8 := Option.some.inj (hm3.symm.trans rfl)
  subst e3
  have e4 : m4 = .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0
      .size8 := Option.some.inj (hm4.symm.trans rfl)
  subst e4
  have hst' := hst.trans hs4
  simp only at hst'
  rw [hs3]
  have hsh : CodeShapeU st0 st'
      [.movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size32,
       .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float) .size8x8,
       .vecLanes .addv (.vreg (st0.nextVreg + 2) .float) (.vreg (st0.nextVreg + 1) .float) .size8x8,
       .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0 .size8]
      (st0.nextVreg + 3) [x] :=
    codeShapeU_of (k := 4) (by rw [hst']; simp only [LState.emit, LState.fresh]; apply Array.ext'; simp)
      (by rw [hst']; rfl) (by omega) (by vec_facts) (by vec_facts)
  refine ⟨_, hsh.emitted, _, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  have ho' : Clif.evalInst fr cm (.unary .popcnt ty x) = .ok (vals, cm') := ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho'
  refine ⟨rfl, usesOk_of [x] hsh.uses (by simp [getAs_ok hu]), .inl hsh.res, _, _, rfl,
    prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl)
      (prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl) (prun_nil _)))), ?_⟩
  have hX : (ρ x).setWidth ty.width = u := hvals x _ (getAs_ok hu)
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  simp only [VHolds, upd, Clif.Sem.unary, Clif.Sem.popcnt, ↓reduceIte, Nat.left_eq_add,
    Nat.add_right_cancel_iff, Nat.add_eq_left, Nat.succ_ne_self, LState.emit, LState.fresh,
    Nat.add_left_cancel_iff, show (1 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide, show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 3 by decide]
  rw [← hX]
  exact popcnt32_fin (ρ x)

set_option maxHeartbeats 1000000 in
/-- **`popcnt_8`** (`lower.isle:2074`). -/
theorem popcnt_8_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2074 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, rfl, hety, -, hd, hhead⟩ := unary_frontTI hp (cop := .popcnt) rfl hp.t2395
    term_2395_kind variantNames_Popcnt_fb rfl hctx hi hc (m := m' + 9) hmatch
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_2074] at hmatch heval
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 29 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
  subst hdat
  have hty := ‹CTy.int 8 = CTy.int ty.width›
  simp only [CTy.int.injEq] at hty
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_reg _ _ = _›
  obtain rfl := hctx.valueRegI x _ hrx
  have hxlt := vreg_lt hvb hrx
  have h1 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
  obtain ⟨rfl, m1, hm1, hs1⟩ := mov_to_fpu_ok hp' hco (by omega) (.inl rfl) h1
  have h2 := ‹ApplyInternal _ _ _ _ 27 524 _ _ _ _›
  obtain ⟨rfl, m2, hm2, hs2⟩ := vec_cnt_ok hp' hco (by omega) h2
  have h4 := ‹ApplyInternal _ _ _ _ 27 414 _ _ _ _›
  obtain ⟨rfl, m4, hm4, hs4⟩ := mov_from_vec_ok hp' hco (by omega) h4
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  rw [hs2] at hm4 hs4
  rw [hs1] at hm2 hs2 hm4 hs4
  rename LState => st0
  have e1 : m1 = .movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size32 :=
    Option.some.inj (hm1.symm.trans rfl)
  subst e1
  have e2 : m2 = .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float)
      .size8x8 := Option.some.inj (hm2.symm.trans rfl)
  subst e2
  have e4 : m4 = .movFromVec (.vreg (st0.nextVreg + 2) .int) (.vreg (st0.nextVreg + 1) .float) 0
      .size8 := Option.some.inj (hm4.symm.trans rfl)
  subst e4
  have hst' := hst.trans hs4
  simp only at hst'
  rw [hs2]
  have hsh : CodeShapeU st0 st'
      [.movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size32,
       .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float) .size8x8,
       .movFromVec (.vreg (st0.nextVreg + 2) .int) (.vreg (st0.nextVreg + 1) .float) 0 .size8]
      (st0.nextVreg + 2) [x] :=
    codeShapeU_of (k := 3) (by rw [hst']; simp only [LState.emit, LState.fresh]; apply Array.ext'; simp)
      (by rw [hst']; rfl) (by omega) (by vec_facts) (by vec_facts)
  refine ⟨_, hsh.emitted, _, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  have ho' : Clif.evalInst fr cm (.unary .popcnt ty x) = .ok (vals, cm') := ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho'
  refine ⟨rfl, usesOk_of [x] hsh.uses (by simp [getAs_ok hu]), .inl hsh.res, _, _, rfl,
    prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl)
      (prun_rr_c hR rfl (fun w => rfl) (prun_nil _))), ?_⟩
  have hX : (ρ x).setWidth ty.width = u := hvals x _ (getAs_ok hu)
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  simp only [VHolds, upd, Clif.Sem.unary, Clif.Sem.popcnt, ↓reduceIte, Nat.left_eq_add,
    Nat.add_right_cancel_iff, Nat.add_eq_left, Nat.succ_ne_self, LState.emit, LState.fresh,
    Nat.add_left_cancel_iff, show (1 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide, show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 3 by decide]
  rw [← hX]
  exact popcnt8_fin (ρ x)

set_option maxHeartbeats 1000000 in
/-- **`popcnt_16`** (`lower.isle:2080`). -/
theorem popcnt_16_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2080 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, rfl, hety, -, hd, hhead⟩ := unary_frontTI hp (cop := .popcnt) rfl hp.t2395
    term_2395_kind variantNames_Popcnt_fb rfl hctx hi hc (m := m' + 9) hmatch
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_2080] at hmatch heval
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 29 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
  subst hdat
  have hty := ‹CTy.int 16 = CTy.int ty.width›
  simp only [CTy.int.injEq] at hty
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_reg _ _ = _›
  obtain rfl := hctx.valueRegI x _ hrx
  have hxlt := vreg_lt hvb hrx
  have h1 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
  obtain ⟨rfl, m1, hm1, hs1⟩ := mov_to_fpu_ok hp' hco (by omega) (.inl rfl) h1
  have h2 := ‹ApplyInternal _ _ _ _ 27 524 _ _ _ _›
  obtain ⟨rfl, m2, hm2, hs2⟩ := vec_cnt_ok hp' hco (by omega) h2
  have h3 := ‹ApplyInternal _ _ _ _ 27 469 _ _ _ _›
  obtain ⟨rfl, m3, hm3, hs3⟩ := addp_ok hp' hco (by omega) h3
  have h4 := ‹ApplyInternal _ _ _ _ 27 414 _ _ _ _›
  obtain ⟨rfl, m4, hm4, hs4⟩ := mov_from_vec_ok hp' hco (by omega) h4
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  rw [hs3] at hm4 hs4
  rw [hs2] at hm3 hs3 hm4 hs4
  rw [hs1] at hm2 hs2 hm3 hs3 hm4 hs4
  rename LState => st0
  have e1 : m1 = .movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size32 :=
    Option.some.inj (hm1.symm.trans rfl)
  subst e1
  have e2 : m2 = .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float)
      .size8x8 := Option.some.inj (hm2.symm.trans rfl)
  subst e2
  have e3 : m3 = .vecRRR .addp (.vreg (st0.nextVreg + 2) .float) (.vreg (st0.nextVreg + 1) .float)
      (.vreg (st0.nextVreg + 1) .float) .size8x8 := Option.some.inj (hm3.symm.trans rfl)
  subst e3
  have e4 : m4 = .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0
      .size8 := Option.some.inj (hm4.symm.trans rfl)
  subst e4
  have hst' := hst.trans hs4
  simp only at hst'
  rw [hs3]
  have hsh : CodeShapeU st0 st'
      [.movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size32,
       .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float) .size8x8,
       .vecRRR .addp (.vreg (st0.nextVreg + 2) .float) (.vreg (st0.nextVreg + 1) .float)
         (.vreg (st0.nextVreg + 1) .float) .size8x8,
       .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0 .size8]
      (st0.nextVreg + 3) [x] :=
    codeShapeU_of (k := 4) (by rw [hst']; simp only [LState.emit, LState.fresh]; apply Array.ext'; simp)
      (by rw [hst']; rfl) (by omega) (by vec_facts) (by vec_facts)
  refine ⟨_, hsh.emitted, _, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  have ho' : Clif.evalInst fr cm (.unary .popcnt ty x) = .ok (vals, cm') := ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho'
  refine ⟨rfl, usesOk_of [x] hsh.uses (by simp [getAs_ok hu]), .inl hsh.res, _, _, rfl,
    prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl)
      (prun_rrr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl) (prun_nil _)))), ?_⟩
  have hX : (ρ x).setWidth ty.width = u := hvals x _ (getAs_ok hu)
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  simp only [VHolds, upd, Clif.Sem.unary, Clif.Sem.popcnt, ↓reduceIte, Nat.left_eq_add,
    Nat.add_right_cancel_iff, Nat.add_eq_left, Nat.succ_ne_self, LState.emit, LState.fresh,
    Nat.add_left_cancel_iff, show (1 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide, show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 3 by decide]
  rw [← hX]
  exact popcnt16_fin (ρ x)

end Rules
end Backend.Proof
