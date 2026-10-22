import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.IselFloatArith

/-!
# S11f: `emit_fcmp`, the condition of a float comparison

`emit_fcmp cc x y` (`inst.isle:5209`) is `CondResult.Cond (fpu_cmp (scalar_size ty) x y)
(fp_cond_code cc)`: `FCMP sn, sm` / `FCMP dn, dm` sets NZCV to `0011` (unordered), `0110`
(equal), `1000` (less than) or `0010` (greater than) (`fcmpFlags`, the Arm model's
`exec_fp_compare`), and `fp_cond_code cc` (`fpCond?`) is an Arm condition that holds on those
flags exactly when CLIF's `fcmp cc` does (`condOn_fcmp`, all four comparison results, NaN
operands included). `one`/`ueq` are `CondResult.Or` (two conditions, `inst.isle:5216-5220`);
`instData` rejects them (`fccOk`), so their rules never fire here.

`emit_fcmp_okT`: over a float-capable context (`CtxInvT`) the code `emit_fcmp cc x y` appends
leaves a condition (`CondCode`) whose truth is `fcmp cc a b` whenever `x`, `y` hold `a`, `b` of
one float type (`FcmpT`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## `FloatCC` values and `fp_cond_code` -/

/-- Variant index of a `FloatCC` (`mkVariant TyId.FloatCC (floatccName cc)`). -/
def fccIdx : Clif.FloatCC → Nat
  | .eq => 0 | .gt => 1 | .ge => 2 | .lt => 3 | .le => 4 | .ne => 5 | .ord => 6 | .one => 7
  | .uno => 8 | .ueq => 9 | .ugt => 10 | .uge => 11 | .ult => 12 | .ule => 13

theorem mkVariant_floatcc (cc : Clif.FloatCC) :
    mkVariant TyId.FloatCC (floatccName cc) = .data 144 (fccIdx cc) [] := by
  cases cc <;> rfl

theorem fccIdx_inj {a b : Clif.FloatCC} (h : fccIdx a = fccIdx b) : a = b := by
  cases a <;> cases b <;> simp [fccIdx] at h ⊢

/-- `fp_cond_code` (`inst.isle:5230-5256`): the Arm condition testing `cc` on `FCMP`'s flags;
none for `one`/`ueq`. -/
def fpCond? : Clif.FloatCC → Option Cond
  | .ord => some .vc | .uno => some .vs | .eq => some .eq | .ne => some .ne | .lt => some .mi
  | .le => some .ls | .gt => some .gt | .ge => some .ge | .ult => some .lt | .ule => some .le
  | .ugt => some .hi | .uge => some .pl | .one => none | .ueq => none

theorem fpCond?_ok {cc : Clif.FloatCC} (h : fccOk cc = true) : ∃ c, fpCond? cc = some c := by
  cases cc <;> simp_all [fccOk, fpCond?]

theorem fpCond?_ne_al {cc : Clif.FloatCC} {c : Cond} (h : fpCond? cc = some c) :
    c ≠ .al ∧ c ≠ .nv := by
  cases cc <;> simp [fpCond?] at h <;> subst h <;> decide

/-- **`fp_cond_code` is `fcmp`'s condition**: on the flags `FCMP` writes for a comparison result
`r` (unordered, equal, less, greater), the Arm condition of `cc` holds iff CLIF's `fcmp cc`
holds of `r`. -/
theorem condOn_fcmp {cc : Clif.FloatCC} {c : Cond} (h : fpCond? cc = some c) (r : IEEE.Cmp) :
    condOn c.bits (fcmpFlags r) = Clif.FSem.condHolds cc r := by
  cases cc <;> simp [fpCond?] at h <;> subst h <;> cases r <;> decide

/-! ## `FCMP` -/

theorem vuseNums_fpuCmp (sz : ScalarSize) (a b : Nat) (ca cb : RegClass) :
    vuseNums (.fpuCmp sz (.vreg a ca) (.vreg b cb)) = [a, b] := rfl

theorem setsFlags_fpuCmp32 (a b : Nat) (ca cb : RegClass) (ρ : Nat → CV) :
    SetsFlags (.fpuCmp .size32 (.vreg a ca) (.vreg b cb)) ρ
      (fcmpFlags (IEEE.compare .b32 ((ρ a).setWidth 32) ((ρ b).setWidth 32))) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

theorem setsFlags_fpuCmp64 (a b : Nat) (ca cb : RegClass) (ρ : Nat → CV) :
    SetsFlags (.fpuCmp .size64 (.vreg a ca) (.vreg b cb)) ρ
      (fcmpFlags (IEEE.compare .b64 ((ρ a).setWidth 64) ((ρ b).setWidth 64))) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

/-! ## CLIF `fcmp` -/

/-- The truth `b` of `fcmp cc x y` in a frame: `x`, `y` hold `a`, `b` of one type, at which
`fcmp cc a b` is `b` (a float type). -/
def FcmpT (cc : Clif.FloatCC) (x y : Nat) (fr : Clif.Frame) (r : Bool) : Prop :=
  ∃ ty a b, fr.regs x = some ⟨ty, a⟩ ∧ fr.regs y = some ⟨ty, b⟩ ∧ Clif.FSem.fcmp cc ty a b = some r

/-- CLIF `fcmp`: the operands are of the controlling type, the result is `fcmp`'s truth. -/
theorem evalFloat_fcmp_ok {cc : Clif.FloatCC} {ty : Clif.Ty} {a b r : Clif.Val}
    (h : Clif.evalFloat (.fcmp cc) ty [a, b] = .ok r) :
    ∃ xa xb t, a = ⟨ty, xa⟩ ∧ b = ⟨ty, xb⟩ ∧ Clif.FSem.fcmp cc ty xa xb = some t ∧
      r = Clif.Val.ofBool t := by
  simp only [Clif.evalFloat, bind, Clif.Res.bind] at h
  cases ha : a.at ty with
  | ok xa =>
    rw [ha] at h
    cases hb : b.at ty with
    | ok xb =>
      rw [hb] at h
      cases ht : Clif.FSem.fcmp cc ty xa xb with
      | none => simp [ht, Clif.Res.ofOption] at h
      | some t =>
        simp only [ht, Clif.Res.ofOption, pure, Clif.Res.ok.injEq] at h
        exact ⟨xa, xb, t, val_at_ok ha, val_at_ok hb, rfl, h.symm⟩
    | trap _ => rw [hb] at h; cases h
    | stuck _ => rw [hb] at h; cases h
  | trap _ => rw [ha] at h; cases h
  | stuck _ => rw [ha] at h; cases h

/-- CLIF `fcmp cc ty [x, y]` evaluated in a frame: `FcmpT` of its `i8` result. -/
theorem evalInst_fcmp_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {cc : Clif.FloatCC} {ty : Clif.Ty}
    {x y : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.float (.fcmp cc) ty [x, y]) = .ok (vals, cm')) :
    ∃ t, vals = [Clif.Val.ofBool t] ∧ cm' = cm ∧ FcmpT cc x y fr t := by
  obtain ⟨vs, r, hv, hr, rfl, rfl⟩ := evalInst_float_ok h
  obtain ⟨a, b, hx, hy, rfl⟩ := getMany_two hv
  obtain ⟨xa, xb, t, rfl, rfl, ht, rfl⟩ := evalFloat_fcmp_ok hr
  exact ⟨t, rfl, rfl, ty, xa, xb, hx, hy, ht⟩

theorem truthy_ofBool (t : Bool) : Clif.Sem.truthy (Clif.Val.ofBool t).bits = t := by
  cases t <;> rfl

/-- A value defined by `fcmp cc ty a b` is the truth of `cc` on `a`, `b`. -/
theorem fcmp_truthy {ctx : Ctx} {fr : Clif.Frame} (hdf : DFGCons ctx fr) {z j : Nat} {info : IInfo}
    {cc : Clif.FloatCC} {ty : Clif.Ty} {a b : Nat} {v : Clif.Val} (hj : ctx.defInst? z = some j)
    (hi : ctx.insts[j]? = some info) (hcl : info.clif = some (.float (.fcmp cc) ty [a, b]))
    (hv : fr.regs z = some v) : v.ty = .i8 ∧ FcmpT cc a b fr (Clif.Sem.truthy v.bits) := by
  obtain ⟨vals, hev, hl⟩ := hdf.1 z j info _ v hj hi hcl rfl hv
  obtain ⟨t, rfl, -, hT⟩ := evalInst_fcmp_ok (hev default)
  have := lookup_zip_single hl
  subst this
  exact ⟨rfl, by rw [truthy_ofBool]; exact hT⟩

/-! ## The condition -/

section Core
variable {F : BitVec 64 → Prop} {isem : Sem} {f : Clif.Function} {ctx : Ctx}

/-- The flag instruction of `emit_fcmp` (`FCMP` at the size of `y`'s type `t`) leaves the
condition `fp_cond_code cc`, true iff `fcmp cc` is. -/
theorem emit_fcmp_core (hctx : CtxInvT f ctx) {st : LState} (hvb : ValsBelow ctx st)
    {cc : Clif.FloatCC} {cond : Cond} (hcond : fpCond? cc = some cond) {x y : Nat} {rx ry : Reg}
    {t : CTy} {sz : ScalarSize} {sv : V}
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry) (hT : ctx.valueType? y = some t)
    (hofv : MInst.ofV (.data 58 56 [sv, .reg rx, .reg ry]) = some (.fpuCmp sz rx ry))
    (hsz : ∀ ty : Clif.Ty, CTy.ofClif ty = t → (ty = .f32 → sz = .size32) ∧ (ty = .f64 → sz = .size64)) :
    CondCode F isem ctx st st (.data 123 2 [.data 47 1 [.data 58 56 [sv, .reg rx, .reg ry]],
      .data 96 cond.idx []]) (FcmpT cc x y) := by
  have := hctx.valueReg x rx hx; subst this
  have := hctx.valueReg y ry hy; subst this
  refine CondCode.flag (ms := []) (Frag.nil _) hofv (fpCond?_ne_al hcond) rfl ?_ ?_
  · intro u hu
    rw [vuseNums_fpuCmp] at hu
    rcases mem2 hu with rfl | rfl
    · exact vreg_lt hvb hx
    · exact vreg_lt hvb hy
  · rintro fr ρ b hh hdf ⟨ty, xa, xb, hxv, hyv, hb⟩
    refine ⟨UsesLo.nil _ _, fun u hu => ?_, fun w => Runs.nil ?_⟩
    · rw [vuseNums_fpuCmp] at hu
      rcases mem2 hu with rfl | rfl
      · exact .inr (by simp [hxv])
      · exact .inr (by simp [hyv])
    · have hty := hsz ty (vholds_ty hdf hT hyv)
      have ha := hh x _ hxv
      have hb' := hh y _ hyv
      cases ty <;> simp only [Clif.FSem.fcmp, reduceCtorEq, Option.some.injEq] at hb
      · obtain rfl := hty.1 rfl
        have ha2 : (ρ x).setWidth 32 = xa := ha
        have hb2 : (ρ y).setWidth 32 = xb := hb'
        refine ⟨_, setsFlags_fpuCmp32 x y _ _ ρ, ?_⟩
        rw [condOn_fcmp hcond, ha2, hb2, ← hb]
      · obtain rfl := hty.2 rfl
        have ha2 : (ρ x).setWidth 64 = xa := ha
        have hb2 : (ρ y).setWidth 64 = xb := hb'
        refine ⟨_, setsFlags_fpuCmp64 x y _ _ ρ, ?_⟩
        rw [condOn_fcmp hcond, ha2, hb2, ← hb]

end Core

/-! ## The terms -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `fpu_cmp` (`inst.isle:2606`): `MInst.FpuCmp` as a flag producer. -/
theorem fpu_cmp_ok {n : Nat} (hn : 30 ≤ n) {a b c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 47 370 [a, b, c] s v s') :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 56 [a, b, c]] := by
  isel_split hp hc h 370
  isel_inv [*, rule_inst_2606] at hm he

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `fp_cond_code` (`inst.isle:5230-5256`): `fpCond?` of the condition, which is not `one`/`ueq`. -/
theorem fp_cond_code_ok {n : Nat} (hn : 30 ≤ n) {k : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 96 656 [.data 144 k []] s v s') :
    s'.1 = s.1 ∧ ∃ cc c, k = fccIdx cc ∧ fpCond? cc = some c ∧ v = .data 96 c.idx [] := by
  isel_split hp hc h 656
  all_goals isel_inv [*, rule_inst_5232, rule_inst_5235, rule_inst_5237, rule_inst_5239,
    rule_inst_5241, rule_inst_5243, rule_inst_5245, rule_inst_5247, rule_inst_5249, rule_inst_5251,
    rule_inst_5253, rule_inst_5255] at hm he
  all_goals refine ⟨rfl, ?_⟩
  all_goals first
    | exact ⟨.eq, _, rfl, rfl, rfl⟩ | exact ⟨.ne, _, rfl, rfl, rfl⟩
    | exact ⟨.lt, _, rfl, rfl, rfl⟩ | exact ⟨.le, _, rfl, rfl, rfl⟩
    | exact ⟨.gt, _, rfl, rfl, rfl⟩ | exact ⟨.ge, _, rfl, rfl, rfl⟩
    | exact ⟨.ord, _, rfl, rfl, rfl⟩ | exact ⟨.uno, _, rfl, rfl, rfl⟩
    | exact ⟨.ult, _, rfl, rfl, rfl⟩ | exact ⟨.ule, _, rfl, rfl, rfl⟩
    | exact ⟨.ugt, _, rfl, rfl, rfl⟩ | exact ⟨.uge, _, rfl, rfl, rfl⟩

end Terms

end Backend.Proof
