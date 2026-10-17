import FV.Backend.Proof.IselFamAluBPopcnt

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
  rw [this]; split <;> simp_all [eq_comm]

theorem ctor_ty_int_ref_scalar_64_iff (ty : CTy) (v : V) (st' : LState) :
    externCtor ctx T.ty_int_ref_scalar_64 [.ty ty] st = .ok (v, st') ↔
      (decide (ty.bits ≤ 64) && !ty.isFloat && !ty.isVector) = true ∧ v = .ty ty ∧ st' = st := by
  have : externCtor ctx T.ty_int_ref_scalar_64 [.ty ty] st =
    if (decide (ty.bits ≤ 64) && !ty.isFloat && !ty.isVector) = true then .ok (.ty ty, st)
    else .fail := rfl
  rw [this]; split <;> simp_all [eq_comm]

end Ext

/-! ## Instruction data of `bitcast` -/

theorem variantNames_LoadNoOffset : (variantNames 152)[17]? = some "LoadNoOffset" := rfl
theorem variantNames_Bitcast : (variantNames 151)[128]? = some "Bitcast" := rfl

theorem instData_bitcast_inv {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V}
    (h : instData f cl = .ok (.data 152 17 [.data 151 128 [], w1, w2])) :
    ∃ ty fl x, cl = .bitcast ty fl x ∧ valTyOk ty = true ∧ w1 = .value x ∧
      w2 = .op (.memFlags fl) := by
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
    exact ⟨he, h3.2.1, h3.2.2.1⟩
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
  revert hw ab
  generalize ty.width = n
  intro ab h' hw
  subst hw
  exact h'

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
    all_goals first
      | (isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
          rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he; done)
      | (isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
          rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
         exact ⟨rfl, rfl⟩)

set_option maxHeartbeats 2000000 in
include hp hc in
theorem scalar_size_float_ok {n : Nat} (hn : 40 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 307 [.ty (.float w)] s v s') :
    v = .data 95 (szIdxOf w) [] ∧ s'.1 = s.1 := by
  rcases hw with rfl | rfl
  all_goals
    isel_split hp hc h 307
    all_goals first
      | (isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
          rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he; done)
      | (isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
          rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
         exact ⟨rfl, rfl⟩)

/-- `size_for_mov_to_fpu`: `Size16` becomes `Size32` (no FP16), the others stay. -/
def movFpuSz (k : Nat) : Nat := if k = 1 then 2 else k

set_option maxHeartbeats 2000000 in
include hp hc in
theorem size_for_mov_to_fpu_any {n : Nat} (hn : 40 ≤ n) {k : Nat} (hk : k ≤ 3)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 410 [.data 95 k []] s v s') :
    v = .data 95 (movFpuSz k) [] ∧ s'.1 = s.1 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  all_goals
    isel_split hp hc h 410
    all_goals first
      | (isel_inv [*, rule_inst_2941] at hm he; done)
      | (isel_inv [*, rule_inst_2938] at hm he; done)
      | (isel_inv [*, rule_inst_2941] at hm he; exact ⟨rfl, rfl⟩)
      | (isel_inv [*, rule_inst_2938] at hm he; exact ⟨rfl, rfl⟩)
      | skip

set_option maxHeartbeats 2000000 in
include hp hc in
theorem mov_to_fpu_any_ok {n : Nat} (hn : 50 ≤ n) {a : V} {k : Nat} (hk : k ≤ 3)
    {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 409 [a, .data 95 k []] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 75 [.reg rd, a, .data 95 (movFpuSz k) []]) := by
  have hp' := hp
  isel_split hp hc h 409
  isel_inv [*, rule_inst_2930, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  have hsz := ‹ApplyInternal _ _ _ _ 95 410 _ _ _ _›
  obtain ⟨rfl, hs⟩ := size_for_mov_to_fpu_any hp' hc (by omega) hk hsz
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  rw [hs] at *
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 2000000 in
include hp hc in
theorem output_value_ok {n : Nat} (hn : 40 ≤ n) {x : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 25 173 [.value x] s v s') :
    ∃ r, ctx.valueReg? x = some r ∧ v = .regsVec [[r]] ∧ s'.1 = s.1 := by
  isel_split hp hc h 173
  isel_inv [*, rule_prelude_lower_109, ctor_put_in_regs_iff] at hm he
  exact ⟨_, ‹_›, rfl, rfl⟩

end Terms

end Backend.Proof
