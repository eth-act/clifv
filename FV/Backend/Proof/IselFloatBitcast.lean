module

public import FV.Backend.Proof.IselFamAluBPopcnt

@[expose] public section

/-!
# S11e4: scalar `bitcast` over float-capable contexts

The four scalar `bitcast` roots of `lower` (`lower.isle:2779–2803`), proven over `CtxInvT`
(class-aware vregs, `f32`/`f64` values):

* 1080 (`rule_lower_2779`, SIMD&FP → SIMD&FP) and 1085 (`rule_lower_2803`, GPR → GPR): the
  operand's vreg is the result (`output_value x`), no code;
* 1083 (`rule_lower_2793`, GPR → SIMD&FP): `mov_to_fpu` (`fmov s/d, w/x`) of the integer operand
  at its scalar size into a fresh float vreg;
* 1084 (`rule_lower_2798`, SIMD&FP → GPR): `mov_from_vec` (`umov w/x, v.s/d[0]`) of lane 0 at
  the result's scalar size into a fresh integer vreg.

CLIF's `bitcast` keeps the bits at a type of the same width (`Clif.evalInst`); the widths that
differ (e.g. `i8` → `f32`) make it stuck, so only `i32 ↔ f32` and `i64 ↔ f64` (and the
identities) need a run.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Extern facts -/

section Ext
variable (ctx : Ctx) (st : LState)

theorem ext_ty_float_or_vec_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.ty_float_or_vec (.ty ty) st = .ok fs ↔
      (ty.isFloat || ty.isVector) = true ∧ fs = [.ty ty] := by
  have : externExtract ctx T.ty_float_or_vec (.ty ty) st =
    if (ty.isFloat || ty.isVector) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim

theorem ctor_ty_int_ref_scalar_64_iff (ty : CTy) (v : V) (st' : LState) :
    externCtor ctx T.ty_int_ref_scalar_64 [.ty ty] st = .ok (v, st') ↔
      (decide (ty.bits ≤ 64) && !ty.isFloat && !ty.isVector) = true ∧ v = .ty ty ∧ st' = st := by
  have : externCtor ctx T.ty_int_ref_scalar_64 [.ty ty] st =
    if (decide (ty.bits ≤ 64) && !ty.isFloat && !ty.isVector) = true then .ok (.ty ty, st)
    else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h
    simp only [h, ExtResult.ok.injEq, Prod.mk.injEq, true_and]
    exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim

theorem ctor_temp_writable_reg_f32_iff (v : V) (st' : LState) :
    externCtor ctx T.temp_writable_reg [.ty (.float 32)] st = .ok (v, st') ↔
      v = .reg (st.fresh .float).1 ∧ st' = (st.fresh .float).2 := by
  have : externCtor ctx T.temp_writable_reg [.ty (.float 32)] st =
      .ok (.reg (st.fresh .float).1, (st.fresh .float).2) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_temp_writable_reg_f64_iff (v : V) (st' : LState) :
    externCtor ctx T.temp_writable_reg [.ty (.float 64)] st = .ok (v, st') ↔
      v = .reg (st.fresh .float).1 ∧ st' = (st.fresh .float).2 := by
  have : externCtor ctx T.temp_writable_reg [.ty (.float 64)] st =
      .ok (.reg (st.fresh .float).1, (st.fresh .float).2) := rfl
  rw [this]; simp [eq_comm]

end Ext

/-! ## Instruction data of `bitcast` -/

theorem variantNames_LoadNoOffset : (variantNames 152)[17]? = some "LoadNoOffset" := rfl
theorem variantNames_Bitcast : (variantNames 151)[128]? = some "Bitcast" := rfl

theorem instData_bitcast_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 17 (.data 151 128 [] :: fs))) :
    ∃ ty fl x, cl = .bitcast ty fl x ∧ valTyOk ty = true ∧ fs = [.value x, .op (.memFlags fl)] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [variantNames_LoadNoOffset] at hf
  rw [variantNames_Bitcast] at ho
  cases cl <;> simp [instNames] at hf ho
  all_goals first
    | (rename_i op _ _; cases op <;> simp [unaryOpcode, binaryOpcode] at ho)
    | (rename_i op _ _ _; cases op <;> simp [unaryOpcode, binaryOpcode] at ho)
    | skip
  rename_i ty fl x
  refine ⟨ty, fl, x, rfl, ?_⟩
  simp only [instData] at h
  split at h
  · rename_i he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq] at h3
    exact ⟨he, h3.2⟩
  · cases h

/-- The result type of a `bitcast.ty` (`CtxInvT.resTys`). -/
theorem bitcast_resTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {ty : Clif.Ty} {fl : Clif.MemFlags} {x : Nat} (hi : ctx.insts[ii]? = some info)
    (hic : info.clif = some (.bitcast ty fl x)) : info.resTys.head?.getD .invalid = CTy.ofClif ty := by
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres]; rfl

/-- CLIF `bitcast`: the operand's bits at the result type, the widths equal. -/
theorem evalInst_bitcast_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {x : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.bitcast ty fl x) = .ok (vals, cm')) :
    ∃ a, fr.regs x = some a ∧ ∃ hw : a.ty.width = ty.width, vals = [⟨ty, hw ▸ a.bits⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hx : fr.get x with
  | ok a =>
    rw [hx] at h
    simp only [bind, Clif.Res.bind] at h
    split at h
    · rename_i hw
      simp only [pure, Clif.Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨a, ?_, hw, rfl, rfl⟩
      unfold Clif.Frame.get at hx
      cases hr : fr.regs x <;> simp [hr, Clif.Res.ofOption] at hx
      rw [hx]
    · cases h
  | trap _ => rw [hx] at h; cases h
  | stuck _ => rw [hx] at h; cases h

/-- A value held by a register is held at any type of the same width (the `bitcast` value). -/
theorem vholds_cast {a : Clif.Val} {ty : Clif.Ty} (hw : a.ty.width = ty.width) {z : CV}
    (h : VHolds a z) : VHolds ⟨ty, hw ▸ a.bits⟩ z := by
  obtain ⟨aty, ab⟩ := a
  show z.setWidth ty.width = hw ▸ ab
  have h' : z.setWidth aty.width = ab := h
  have key : ∀ {n m : Nat} (e : n = m) (b : BitVec n), z.setWidth n = b → z.setWidth m = e ▸ b := by
    intro n m e b hb; subst e; exact hb
  exact key hw ab h'

/-! ## `LowerInstOk` of a one-result instruction, any result class -/

theorem lowerInstOk_one_c {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat} {st st' : LState}
    {ms : List MInst} {d : Nat} {c : RegClass} (hMR : MRStable F MR)
    (hmono : st.nextVreg ≤ st'.nextVreg)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg)
    (htrap : explicitTrapInst inst = false)
    (hrun : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) vals cm', fr.func = ctx.func →
      ValsHeld fr ρ → DFGCons ctx fr → instOutcome env cp fr cm inst = .ok (vals, cm') →
      cm' = cm ∧ UsesOk st fr ms ∧ (st.nextVreg ≤ d ∨ (fr.regs d).isSome) ∧
        ∃ v ρ', vals = [v] ∧ PRun F isem ms ρ ρ' ∧ VHolds v (ρ' d)) :
    LowerInstOk isem MR env cp ctx inst results st [[.vreg d c]] st' ms := by
  refine ⟨hmono, hdefs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  split
  · rename_i vals cm' ho
    obtain ⟨rfl, hu, hd, v, ρ', rfl, hp, hh⟩ := hrun fr cm ρ vals cm' hf hv hdfg ho
    obtain ⟨w', hs, hw⟩ := hp w
    refine ⟨hu, ρ', w', hs, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hw.nf hmr⟩
    intro j rs val hrs hval
    match j, hrs, hval with
    | 0, hrs, hval =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
      subst hrs; subst hval
      exact ⟨d, c, rfl, hd, hh⟩
    | _ + 1, hrs, _ => simp at hrs
  · intro h; rw [htrap] at h; cases h
  · trivial

/-! ## Internal terms: `scalar_size`, `mov_to_fpu`, `output_value` -/

/-- `ScalarSize` of an integer width (`scalar_size`). -/
def szIdxOf (w : Nat) : Nat := if w = 8 then 0 else if w = 16 then 1 else if w = 32 then 2 else 3

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
theorem scalar_size_int_ok {n : Nat} (hn : 40 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 307 [.ty (.int w)] s v s') :
    v = .data 95 (szIdxOf w) [] ∧ s'.1 = s.1 := by
  rcases hw with rfl | rfl | rfl | rfl
  all_goals
    isel_split hp hc h 307
    all_goals
      isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
        rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631, CTy.int.injEq,
        CTy.float.injEq] at hm he
    all_goals first
      | rfl
      | decide
      | exact ⟨rfl, rfl⟩
      | (exfalso; revert ‹CTy.int _ = CTy.int _›; decide)

set_option maxHeartbeats 2000000 in
include hp hc in
theorem scalar_size_float_ok {n : Nat} (hn : 40 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 307 [.ty (.float w)] s v s') :
    v = .data 95 (szIdxOf w) [] ∧ s'.1 = s.1 := by
  rcases hw with rfl | rfl
  all_goals
    isel_split hp hc h 307
    all_goals
      isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
        rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631, CTy.int.injEq,
        CTy.float.injEq] at hm he
    all_goals first
      | rfl
      | decide
      | exact ⟨rfl, rfl⟩
      | (exfalso; revert ‹CTy.float _ = CTy.float _›; decide)

theorem ctor_use_fp16_iff (ctx : Ctx) (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.use_fp16 [] st = .ok (v, st') ↔ v = .bool false ∧ st' = st := by
  have : externCtor ctx T.use_fp16 [] st = .ok (.bool false, st) := rfl
  rw [this]
  simp only [ExtResult.ok.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `size_for_mov_to_fpu`: `Size16` becomes `Size32` (FP16 is off), the others stay. -/
theorem size_for_mov_to_fpu_any {n : Nat} (hn : 40 ≤ n) {k : Nat}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 410 [.data 95 k []] s v s') :
    (v = .data 95 k [] ∨ (k = 1 ∧ v = .data 95 2 [])) ∧ s'.1 = s.1 := by
  isel_split hp hc h 410
  all_goals isel_inv [*, rule_inst_2941, rule_inst_2938] at hm he
  all_goals (try (obtain ⟨-, rfl⟩ :=
    (ctor_use_fp16_iff ctx _ _ _).mp ‹externCtor ctx T.use_fp16 _ _ = _›))
  all_goals first
    | exact ⟨.inl rfl, rfl⟩
    | exact ⟨.inr ⟨rfl, rfl⟩, rfl⟩
    | exact .inl rfl
    | exact .inr ⟨rfl, rfl⟩
    | rfl
    | simp

set_option maxHeartbeats 2000000 in
include hp hc in
theorem mov_to_fpu_any_ok {n : Nat} (hn : 50 ≤ n) {a : V} {k : Nat}
    {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 409 [a, .data 95 k []] st v st') :
    ∃ k', (k' = k ∨ (k = 1 ∧ k' = 2)) ∧
      EmitOutC .float st.1 st'.1 v (fun rd => .data 58 75 [.reg rd, a, .data 95 k' []]) := by
  have hp' := hp
  isel_split hp hc h 409
  isel_inv [*, rule_inst_2930, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  have hsz := ‹ApplyInternal _ _ _ _ 95 410 _ _ _ _›
  obtain ⟨hk', hs⟩ := size_for_mov_to_fpu_any hp' hc (by omega) hsz
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  rw [hs] at *
  rcases hk' with rfl | ⟨rfl, rfl⟩
  · exact ⟨k, .inl rfl, rfl, _, ‹_›, rfl⟩
  · exact ⟨2, .inr ⟨rfl, rfl⟩, rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 2000000 in
include hp hc in
theorem output_value_ok {n : Nat} (hn : 40 ≤ n) {x : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 25 173 [.value x] s v s') :
    ∃ r, ctx.valueReg? x = some r ∧ v = .regsVec [[r]] ∧ s'.1 = s.1 := by
  isel_split hp hc h 173
  isel_inv [*, rule_prelude_lower_109] at hm he
  obtain ⟨r, hr, rfl, rfl⟩ :=
    (ctor_put_in_regs_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_regs _ _ = _›
  obtain ⟨rfl, rfl⟩ := (ctor_output' ctx _ _ _ _).mp ‹externCtor ctx T.output _ _ = _›
  exact ⟨r, hr, rfl, rfl⟩

end Terms

/-! ## Facts of the types -/

theorem ofClif_float_or_vec {ty : Clif.Ty}
    (h : ((CTy.ofClif ty).isFloat || (CTy.ofClif ty).isVector) = true) : ty = .f32 ∨ ty = .f64 := by
  cases ty <;> simp_all [CTy.ofClif, CTy.isFloat, CTy.isVector]

theorem ofClif_int_le64 {ty : Clif.Ty}
    (h : (decide ((CTy.ofClif ty).bits ≤ 64) && !(CTy.ofClif ty).isFloat &&
      !(CTy.ofClif ty).isVector) = true) : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64 := by
  cases ty <;> simp_all [CTy.ofClif, CTy.isFloat, CTy.isVector, CTy.bits]

theorem mCTys_cases {t : CTy} (h : t ∈ mCTys) :
    t = .int 8 ∨ t = .int 16 ∨ t = .int 32 ∨ t = .int 64 ∨ t = .float 32 ∨ t = .float 64 := by
  simpa [mCTys, eCTys] using h

/-! ## The matched `bitcast` -/

/-- The instruction a `bitcast` root matched (`InstructionData::LoadNoOffset`, `Bitcast`). -/
theorem bitcast_front {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst) {r : Rule} {tyPat xPat : Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2464 [.term 151 2412 [], xPat, .wildcard 137]]])
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty fl x, inst = .bitcast ty fl x ∧
      info.data = .data 152 17 [.data 151 128 [], .value x, .op (.memFlags fl)] := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2464 term_2464_kind hp.t2412
    term_2412_kind h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨ty, fl, x, rfl, -, rfl⟩ := instData_bitcast_inv hdat
  exact ⟨ty, fl, x, rfl, hd⟩

/-- `LowerInstOk` of a `bitcast` whose result is its operand's vreg (no code). -/
theorem lowerInstOk_bitcast_id {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {ctx : Ctx} {results : List Nat} {st : LState} {ty : Clif.Ty} {fl : Clif.MemFlags} {x : Nat}
    {c : RegClass} : LowerInstOk isem MR env cp ctx (.bitcast ty fl x) results st [[.vreg x c]] st [] := by
  refine ⟨Nat.le_refl _, by simp, ?_⟩
  intro fr cm ρ w _ hv _ hmr
  split
  · rename_i vals cm' ho
    have ho' : Clif.evalInst fr cm (.bitcast ty fl x) = .ok (vals, cm') := ho
    obtain ⟨a, hx, hw, rfl, rfl⟩ := evalInst_bitcast_ok ho'
    refine ⟨by simp [UsesOk], ρ, w, rfl, .inr ⟨rfl, ?_⟩, hmr⟩
    intro j rs v hrs hval
    match j, hrs, hval with
    | 0, hrs, hval =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
      subst hrs; subst hval
      exact ⟨x, c, rfl, .inr (by rw [hx]; rfl), vholds_cast hw (hv x a hx)⟩
    | _ + 1, hrs, _ => simp at hrs
  · intro h; simp [explicitTrapInst] at h
  · trivial

/-- The matched data's operand is the `bitcast`'s (`inst_data_value` returned `info`). -/
theorem bitcast_data_eq {ctx : Ctx} {ii : Nat} {info info' : IInfo} {x : Nat}
    {fl : Clif.MemFlags} {w1 w2 : V} (hi : ctx.insts[ii]? = some info)
    (hd : info.data = .data 152 17 [.data 151 128 [], .value x, .op (.memFlags fl)])
    (hi' : ctx.insts[ii]? = some info') (hw : V.data 152 17 [.data 151 128 [], w1, w2] = info'.data) :
    info' = info ∧ w1 = .value x ∧ w2 = .op (.memFlags fl) := by
  rw [hi] at hi'
  cases hi'
  rw [hd] at hw
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw
  exact ⟨rfl, hw.1, hw.2⟩

/-! ## Values of the moves -/

theorem setW_lo32 (z : CV) : (((lo64 z).setWidth 32).setWidth 128).setWidth 32 = z.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo64, BitVec.toNat_setWidth]
  omega

theorem setW_lo64 (z : CV) : ((lo64 z).setWidth 128).setWidth 64 = z.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo64, BitVec.toNat_setWidth]
  omega

theorem setW_umov32 (z : CV) :
    (ofX ((z.extractLsb' (32 * 0) 32).setWidth 64)).setWidth 32 = z.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [ofX, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.mul_zero, Nat.shiftRight_zero]
  omega

theorem setW_umov64 (z : CV) : (ofX (z.extractLsb' (64 * 0) 64)).setWidth 64 = z.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [ofX, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.mul_zero, Nat.shiftRight_zero]
  omega

/-- A value of width `n` held by `z` is held by any `r` agreeing with `z` on the low `n` bits. -/
theorem vholds_of_low {a : Clif.Val} {z r : CV} {n : Nat} (hn : a.ty.width = n)
    (hr : r.setWidth n = z.setWidth n) (h : VHolds a z) : VHolds a r := by
  obtain ⟨aty, ab⟩ := a
  simp only at hn
  show r.setWidth aty.width = ab
  have h' : z.setWidth aty.width = ab := h
  rw [← h']
  subst hn
  exact hr

/-- A value whose `CTy` is `t`, with width `n`: the scalar types of `n` bits. -/
theorem width_of_ofClif {aty : Clif.Ty} {w : Nat} (h : CTy.ofClif aty = .int w) : aty.width = w := by
  cases aty <;> simp [CTy.ofClif] at h <;> subst h <;> rfl

theorem width_of_ofClif_f {aty : Clif.Ty} {w : Nat} (h : CTy.ofClif aty = .float w) :
    aty.width = w := by
  cases aty <;> simp [CTy.ofClif] at h <;> subst h <;> rfl

/-! ## The four roots -/

set_option maxHeartbeats 4000000 in
/-- **`bitcast` SIMD&FP → SIMD&FP** (`rule_lower_2779`, `lower.isle:2779`): the operand's
vreg, no code. -/
theorem bitcast_fp_fp_okT {p : Program} (hp : Data p) {isem : Sem} (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) : LowerRuleOkT isem MR env cp p rule_lower_2779 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, fl, x, rfl, hd⟩ := bitcast_front hp hctx hi hic rfl (m := m' + 9) hmatch
  have hp' := hp
  isel_inv' hp [ext_ty_float_or_vec_iff] at hmatch heval
  obtain ⟨rfl, rfl, rfl⟩ := bitcast_data_eq hi hd ‹ctx.insts[ii]? = some _› ‹V.data 152 17 _ = _›
  have hO := ‹ApplyInternal _ _ _ _ 25 173 _ _ _ _›
  obtain ⟨r, hr, rfl, hs⟩ := output_value_ok hp' hco (by omega) hO
  try simp only at hs
  subst hs
  rw [hctx.valueReg x r hr]
  first
    | refine ⟨[], ?_, [[.vreg x (valClassOf ctx x)]], rfl, ?_⟩
    | refine ⟨[], [[.vreg x (valClassOf ctx x)]], ?_, rfl, ?_⟩
  · simp
  · exact lowerInstOk_bitcast_id

set_option maxHeartbeats 4000000 in
/-- **`bitcast` GPR → GPR** (`rule_lower_2803`, `lower.isle:2803`): the operand's vreg, no
code. -/
theorem bitcast_gpr_gpr_okT {p : Program} (hp : Data p) {isem : Sem} (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) : LowerRuleOkT isem MR env cp p rule_lower_2803 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, fl, x, rfl, hd⟩ := bitcast_front hp hctx hi hic rfl (m := m' + 9) hmatch
  have hp' := hp
  isel_inv' hp [ctor_ty_int_ref_scalar_64_iff] at hmatch heval
  obtain ⟨rfl, rfl, rfl⟩ := bitcast_data_eq hi hd ‹ctx.insts[ii]? = some _› ‹V.data 152 17 _ = _›
  obtain ⟨t, -, htw⟩ := (ext_value_type_iff ctx _ x _).mp ‹externExtract ctx T.value_type _ _ = _›
  simp only [List.cons.injEq, and_true] at htw
  subst htw
  obtain ⟨-, rfl, rfl⟩ :=
    (ctor_ty_int_ref_scalar_64_iff ctx _ t _ _).mp ‹externCtor ctx T.ty_int_ref_scalar_64 _ _ = _›
  have hO := ‹ApplyInternal _ _ _ _ 25 173 _ _ _ _›
  obtain ⟨r, hr, rfl, hs⟩ := output_value_ok hp' hco (by omega) hO
  try simp only at hs
  subst hs
  rw [hctx.valueReg x r hr]
  first
    | refine ⟨[], ?_, [[.vreg x (valClassOf ctx x)]], rfl, ?_⟩
    | refine ⟨[], [[.vreg x (valClassOf ctx x)]], ?_, rfl, ?_⟩
  · simp
  · exact lowerInstOk_bitcast_id

/-- An equation the inversion tactics leave alone (`subst_vars` would eliminate the name). -/
def KeepEq (a b : Nat) : Prop := a = b

/-- The `movToFpu` a `mov_to_fpu` of size index `k ≤ 3` emitted. -/
theorem ofV_movToFpu {d x k : Nat} {m : MInst} (hk : k ≤ 3)
    (h : MInst.ofV (.data 58 75 [.reg (.vreg d .float), .reg (.vreg x .int), .data 95 k []]) = some m) :
    ∃ sz, m = .movToFpu (.vreg d .float) (.vreg x .int) sz ∧ (k = 2 → sz = .size32) ∧
      (k = 3 → sz = .size64) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact ⟨.size8, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩
  · exact ⟨.size16, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩
  · exact ⟨.size32, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩
  · exact ⟨.size64, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩

/-- The `movFromVec` a `mov_from_vec` of lane 0 at the scalar size of `i8..i64` emitted. -/
theorem ofV_movFromVec {d x w : Nat} {m : MInst} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (h : MInst.ofV (.data 58 78 [.reg (.vreg d .int), .reg (.vreg x .float), .int 0,
      .data 95 (szIdxOf w) []]) = some m) :
    ∃ sz, m = .movFromVec (.vreg d .int) (.vreg x .float) 0 sz ∧ (w = 32 → sz = .size32) ∧
      (w = 64 → sz = .size64) := by
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨.size8, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩
  · exact ⟨.size16, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩
  · exact ⟨.size32, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩
  · exact ⟨.size64, Option.some.inj (h.symm.trans rfl), by decide, by decide⟩

set_option maxHeartbeats 8000000 in
/-- **`bitcast` GPR → SIMD&FP** (`rule_lower_2793`, `lower.isle:2793`): `fmov s/d, w/x`
(`mov_to_fpu` at the operand's scalar size) into a fresh float vreg. -/
theorem bitcast_gpr_fp_okT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkT isem MR env cp p rule_lower_2793 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
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
  first
    | refine ⟨[.movToFpu (.vreg d0 .float) (.vreg x .int) sz], ?_, [[.vreg d0 .float]], ?_, ?_⟩
    | refine ⟨[.movToFpu (.vreg d0 .float) (.vreg x .int) sz], [[.vreg d0 .float]], ?_, ?_, ?_⟩
  · simp [LState.emit, LState.fresh]
  · simp [LState.fresh, hs1, hd0]
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    simp only [vd_movToFpu, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he
    simp [LState.emit, LState.fresh, hd0]
  · intro fr cm ρ vals cm' _ hvals hdfg ho
    have ho' : Clif.evalInst fr cm (.bitcast ty fl x) = .ok (vals, cm') := ho
    obtain ⟨a, hx, hwa, rfl, rfl⟩ := evalInst_bitcast_ok ho'
    have hat := width_of_ofClif (hdfg.2 x (.int w) a ht hx)
    have hfv : ((CTy.ofClif ty).isFloat || (CTy.ofClif ty).isVector) = true := by
      rw [← bitcast_resTy hctx hi hic]; assumption
    have hu : ∀ S : LState, UsesOk S fr [.movToFpu (.vreg d0 .float) (.vreg x .int) sz] := by
      intro S
      refine usesOk_of [x] ?_ (by simp [hx])
      intro mi hmi u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
      subst hmi
      simp only [vu_movToFpu, List.mem_cons, List.mem_nil_iff, or_false] at hu
      exact .inr (by simp [hu])
    rcases ofClif_float_or_vec hfv with rfl | rfl
    · have hw32 : w = 32 := by rw [← hat, hwa]; rfl
      subst hw32
      obtain rfl := hsz2 (by rcases hk' with h | ⟨h, -⟩ <;> simp [szIdxOf] at h <;> omega)
      refine ⟨rfl, hu _, .inl (by omega), _, _, rfl,
        prun_rr_c hR rfl (fun w => rfl) (prun_nil _), ?_⟩
      simp only [upd, ↓reduceIte]
      exact vholds_cast hwa (vholds_of_low hat (setW_lo32 (ρ x)) (hvals x a hx))
    · have hw64 : w = 64 := by rw [← hat, hwa]; rfl
      subst hw64
      obtain rfl := hsz3 (by rcases hk' with h | ⟨h, -⟩ <;> simp [szIdxOf] at h <;> omega)
      refine ⟨rfl, hu _, .inl (by omega), _, _, rfl,
        prun_rr_c hR rfl (fun w => rfl) (prun_nil _), ?_⟩
      simp only [upd, ↓reduceIte]
      exact vholds_cast hwa (vholds_of_low hat (setW_lo64 (ρ x)) (hvals x a hx))

set_option maxHeartbeats 8000000 in
/-- **`bitcast` SIMD&FP → GPR** (`rule_lower_2798`, `lower.isle:2798`): `umov w/x, v.s/d[0]`
(`mov_from_vec` of lane 0 at the result's scalar size) into a fresh integer vreg. -/
theorem bitcast_fp_gpr_okT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkT isem MR env cp p rule_lower_2798 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
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
  obtain ⟨-, htw⟩ := (ext_fits_in_64_iff ctx _ t _).mp ‹externExtract ctx T.fits_in_64 _ _ = _›
  simp only [List.cons.injEq, and_true] at htw
  subst htw
  obtain ⟨hfl, -⟩ :=
    (ext_ty_float_or_vec_iff ctx _ t _).mp ‹externExtract ctx T.ty_float_or_vec _ _ = _›
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ x _ _).mp ‹externCtor ctx T.put_in_reg _ _ = _›
  have hres := bitcast_resTy hctx hi hic
  have hint : (decide ((CTy.ofClif ty).bits ≤ 64) && !(CTy.ofClif ty).isFloat &&
      !(CTy.ofClif ty).isVector) = true := by rw [← hres]; assumption
  obtain ⟨w, hwty, hw, hwidth⟩ : ∃ w, CTy.ofClif ty = .int w ∧
      (w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) ∧ ty.width = w := by
    rcases ofClif_int_le64 hint with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, by decide, rfl⟩
  obtain ⟨wt, rfl, hwt⟩ : ∃ wt, t = .float wt ∧ (wt = 32 ∨ wt = 64) := by
    rcases mCTys_cases (hctx.valTyM x t ht) with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ⟨_, rfl, by decide⟩ | (simp [CTy.isFloat, CTy.isVector] at hfl)
  have hcls : (CTy.float wt).valClass = .float := by rcases hwt with rfl | rfl <;> rfl
  have hrx' := hctx.typedReg x _ ht
  rw [hcls, hrx] at hrx'
  obtain rfl := Option.some.inj hrx'
  have h1 := ‹ApplyInternal _ _ _ _ 95 307 _ _ _ _›
  rw [hres, hwty] at h1
  obtain ⟨rfl, hs1⟩ := scalar_size_int_ok hp' hco (by omega) hw h1
  have h2 := ‹ApplyInternal _ _ _ _ 27 414 _ _ _ _›
  obtain ⟨rfl, m1, hm1, hs2⟩ := mov_from_vec_ok hp' hco (by omega) h2
  have h3 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp' hco (by omega) h3
  try simp only at hs1 hs3
  rw [hs1] at hs2 hm1
  rw [hs2] at hs3
  subst hs3
  simp only [LState.fresh, hd0] at hm1
  obtain ⟨sz, rfl, hsz32, hsz64⟩ := ofV_movFromVec hw hm1
  first
    | refine ⟨[.movFromVec (.vreg d0 .int) (.vreg x .float) 0 sz], ?_, [[.vreg d0 .int]], ?_, ?_⟩
    | refine ⟨[.movFromVec (.vreg d0 .int) (.vreg x .float) 0 sz], [[.vreg d0 .int]], ?_, ?_, ?_⟩
  · simp [LState.emit, LState.fresh]
  · simp [LState.fresh, hs1, hd0]
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    simp only [vd_movFromVec, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he
    simp [LState.emit, LState.fresh, hd0]
  · intro fr cm ρ vals cm' _ hvals hdfg ho
    have ho' : Clif.evalInst fr cm (.bitcast ty fl x) = .ok (vals, cm') := ho
    obtain ⟨a, hx, hwa, rfl, rfl⟩ := evalInst_bitcast_ok ho'
    have hat := width_of_ofClif_f (hdfg.2 x (.float wt) a ht hx)
    have hu : ∀ S : LState, UsesOk S fr [.movFromVec (.vreg d0 .int) (.vreg x .float) 0 sz] := by
      intro S
      refine usesOk_of [x] ?_ (by simp [hx])
      intro mi hmi u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
      subst hmi
      simp only [vu_movFromVec, List.mem_cons, List.mem_nil_iff, or_false] at hu
      exact .inr (by simp [hu])
    have hww : w = wt := by rw [← hwidth, ← hwa, hat]
    subst hww
    rcases hwt with rfl | rfl
    · obtain rfl := hsz32 rfl
      refine ⟨rfl, hu _, .inl (by omega), _, _, rfl,
        prun_rr_c hR rfl (fun w => rfl) (prun_nil _), ?_⟩
      simp only [upd, ↓reduceIte]
      exact vholds_cast hwa (vholds_of_low hat (setW_umov32 (ρ x)) (hvals x a hx))
    · obtain rfl := hsz64 rfl
      refine ⟨rfl, hu _, .inl (by omega), _, _, rfl,
        prun_rr_c hR rfl (fun w => rfl) (prun_nil _), ?_⟩
      simp only [upd, ↓reduceIte]
      exact vholds_cast hwa (vholds_of_low hat (setW_umov64 (ρ x)) (hvals x a hx))

end Backend.Proof
