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

/-- `fccOk` excludes exactly `one` (`fccIdx 7`) and `ueq` (`fccIdx 9`). -/
theorem fccOk_ne {cc : Clif.FloatCC} {k : Nat} (h : fccIdx cc = k) (hok : fccOk cc = true) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 8 ∨ k = 10 ∨ k = 11 ∨
      k = 12 ∨ k = 13 := by
  cases cc <;> simp_all [fccIdx, fccOk]

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
        exact ⟨xa, xb, t, val_at_ok ha, val_at_ok hb, ht, h.symm⟩
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

/-- The frame side of `emit_fcmp_core`, with the (empty) instruction list fixed: on a frame
where the operands hold values of the controlling type, the `FCMP` run's condition truth is
`Clif.FSem.fcmp` on them. -/
theorem emit_fcmp_core_run {st : LState} (hvb : ValsBelow ctx st)
    {cc : Clif.FloatCC} {cond : Cond} (hcond : fpCond? cc = some cond) {x y : Nat} {rx ry : Reg}
    {t : CTy} {sz : ScalarSize} {sv : V}
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry) (hT : ctx.valueType? y = some t)
    (hofv : MInst.ofV (.data 58 56 [sv, .reg rx, .reg ry]) = some (.fpuCmp sz rx ry))
    (hsz : ∀ ty : Clif.Ty, CTy.ofClif ty = t → (ty = .f32 → sz = .size32) ∧ (ty = .f64 → sz = .size64))
    (fr : Clif.Frame) (ρ : Nat → CV) (b : Bool) (hh : ValsHeld fr ρ) (hdf : DFGCons ctx fr)
    (hT' : FcmpT cc x y fr b) :
    UsesLo st.nextVreg fr [] ∧
      (∀ u ∈ vuseNums (MInst.fpuCmp sz rx ry), st.nextVreg ≤ u ∨ (fr.regs u).isSome) ∧
      ∀ w, Runs F isem [] ρ w (fun ρ' _ => ∃ ps, SetsFlags (MInst.fpuCmp sz rx ry) ρ' ps ∧
        condOn cond.bits ps = b) := by
  rintro ⟨ty, xa, xb, hxv, hyv, hb⟩ at hT'
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
  · exact fun fr ρ b hh hdf hT => emit_fcmp_core_run hvb hcond hx hy hT hofv hsz fr ρ b hh hdf hT

end Core

/-! ## The terms -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `fpu_cmp` (`inst.isle:2606`): `MInst.FpuCmp` as a flag producer. -/
theorem fpu_cmp_ok {n : Nat} {a b c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 47 370 [a, b, c] s v s') (hn : 30 ≤ n) :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 56 [a, b, c]] := by
  isel_split hp hc h 370
  isel_inv [*, rule_inst_2606] at hm he

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `fp_cond_code` (`inst.isle:5230-5256`): `fpCond?` of the condition, which is not `one`/`ueq`. -/
theorem fp_cond_code_ok {n : Nat} {k : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 96 656 [.data 144 k []] s v s') (hn : 40 ≤ n) :
    s'.1 = s.1 ∧ ∃ cc c, k = fccIdx cc ∧ fpCond? cc = some c ∧ v = .data 96 c.idx [] := by
  isel_split hp hc h 656
  all_goals isel_inv [*, rule_inst_5232, rule_inst_5235, rule_inst_5237, rule_inst_5239,
    rule_inst_5241, rule_inst_5243, rule_inst_5245, rule_inst_5247, rule_inst_5249, rule_inst_5251,
    rule_inst_5253, rule_inst_5255] at hm he
  all_goals first
    | exact ⟨.eq, rfl, _, rfl, rfl⟩ | exact ⟨.ne, rfl, _, rfl, rfl⟩
    | exact ⟨.lt, rfl, _, rfl, rfl⟩ | exact ⟨.le, rfl, _, rfl, rfl⟩
    | exact ⟨.gt, rfl, _, rfl, rfl⟩ | exact ⟨.ge, rfl, _, rfl, rfl⟩
    | exact ⟨.ord, rfl, _, rfl, rfl⟩ | exact ⟨.uno, rfl, _, rfl, rfl⟩
    | exact ⟨.ult, rfl, _, rfl, rfl⟩ | exact ⟨.ule, rfl, _, rfl, rfl⟩
    | exact ⟨.ugt, rfl, _, rfl, rfl⟩ | exact ⟨.uge, rfl, _, rfl, rfl⟩

/-! ## `instData` -/

section VNs
attribute [local irreducible] Isle.Aarch64.program

set_option maxHeartbeats 4000000 in
theorem cmp_vn_FloatCompare : (variantNames 152)[11]? = some "FloatCompare" := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem cmp_vn_Fcmp : (variantNames 151)[112]? = some "Fcmp" := by decide +kernel

end VNs

/-- An instruction whose opcode name is `Fcmp` is a float operation. -/
theorem instNames_fcmp {c : Clif.Inst} {s : String} (hs : s ∈ "Fcmp" :: fArithNames)
    (h : (instNames c).2 = s) : ∃ op ty args, c = .float op ty args := by
  cases c
  case float op ty args => exact ⟨op, ty, args, rfl⟩
  all_goals exfalso
  all_goals subst h
  all_goals simp only [instNames, fArithNames] at hs
  all_goals first
    | (simp at hs; done)
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at hs; done)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at hs; done)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at hs; done)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at hs; done)

/-- A matched `FloatCompare` is an `fcmp` at a type and condition `instData` admits. -/
theorem instData_fcmp_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 11 (.data 151 112 [] :: fs))) :
    ∃ cc ty x y, cl = .float (.fcmp cc) ty [x, y] ∧ ty.isFloat ∧ fccOk cc = true ∧
      fs = [.values [x, y], .data 144 (fccIdx cc) []] := by
  obtain ⟨ho1, ho2⟩ := instData_inv_names h (by decide)
  rw [cmp_vn_FloatCompare] at ho1
  rw [cmp_vn_Fcmp] at ho2
  have h2 : (instNames cl).2 = "Fcmp" := (Option.some.inj ho2).symm
  obtain ⟨op, ty, args, rfl⟩ := instNames_fcmp (s := "Fcmp") (hs := by simp) h2
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp only [instData, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  · cases op <;>
      simp only [instData, fUnaryOpcode, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
    all_goals
      first
        | (split at h
           · simp only [pure, Except.pure, Except.ok.injEq] at h
             obtain ⟨hc, -, -⟩ := mkVariant_eq_data h
             rw [cmp_vn_FloatCompare] at hc
             simp at hc
           · simp only [reduceCtorEq] at h)
        | simp only [reduceCtorEq] at h
  · cases op <;>
      simp only [instData, fBinaryOpcode, fUnaryOpcode, throw, throwThe, MonadExceptOf.throw,
        reduceCtorEq] at h
    case fcmp cc =>
      split at h
      · rename_i hf
        simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true] at h hf
        obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
        simp only [List.cons.injEq] at h3
        obtain ⟨-, hfs⟩ := h3
        simp only [mkVariant_floatcc] at hfs
        exact ⟨cc, ty, x, y, rfl, hf.1, hf.2, hfs⟩
      · simp only [reduceCtorEq] at h
    all_goals
      first
        | (split at h
           · simp only [pure, Except.pure, Except.ok.injEq] at h
             obtain ⟨hc, -, -⟩ := mkVariant_eq_data h
             rw [cmp_vn_FloatCompare] at hc
             simp at hc
           · simp only [reduceCtorEq] at h)
        | simp only [reduceCtorEq] at h
  · simp only [instData, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h

/-! ## The contract -/

section Contract

/-- The `scalar_size` term's output index: the `OperandSize` variant of the type
(`inst.isle:1623-1631`: `S8`/`S16`/`S32`/`S64`/`S128` for `i8`..`i128`, `S16`/`S32`/`S64` for
`f16`/`f32`/`f64`; other types have no rule, so the call cannot succeed there). -/
def ssIdx : CTy → Nat
  | .int 8 => 0 | .int 16 => 1 | .int 32 => 2 | .int 64 => 3 | .int 128 => 4
  | .float 16 => 1 | .float 32 => 2 | .float 64 => 3 | _ => 0

theorem ssIdx_le (t : CTy) : ssIdx t ≤ 4 := by
  unfold ssIdx
  split <;> omega

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `scalar_size` at any type: the size index of the type (rules exist only for the scalar
types; at `invalid`/vectors no rule matches and the call cannot succeed). -/
theorem scalar_size_ok {n : Nat} {t : CTy}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 307 [.ty t] s v s') (hn : 40 ≤ n) :
    v = .data 95 (ssIdx t) [] ∧ s'.1 = s.1 := by
  cases t with
  | invalid =>
    exfalso
    isel_split hp hc h 307
    all_goals isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
      rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
    all_goals (simp only [Backend.Proof.sem_eq] at *; simp only [V.beq] at *; simp)
  | vec lb nb fl =>
    exfalso
    isel_split hp hc h 307
    all_goals isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
      rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
    all_goals (simp only [Backend.Proof.sem_eq] at *; simp only [V.beq] at *; simp)
  | int w =>
    isel_split hp hc h 307
    all_goals isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
      rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
    all_goals
      first
        | (have hw : CTy.int w = CTy.int 8 := by assumption
           simp only [CTy.int.injEq] at hw; subst hw; rfl)
        | (have hw : CTy.int w = CTy.int 16 := by assumption
           simp only [CTy.int.injEq] at hw; subst hw; rfl)
        | (have hw : CTy.int w = CTy.int 32 := by assumption
           simp only [CTy.int.injEq] at hw; subst hw; rfl)
        | (have hw : CTy.int w = CTy.int 64 := by assumption
           simp only [CTy.int.injEq] at hw; subst hw; rfl)
        | (have hw : CTy.int w = CTy.int 128 := by assumption
           simp only [CTy.int.injEq] at hw; subst hw; rfl)
  | float w =>
    isel_split hp hc h 307
    all_goals isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
      rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
    all_goals
      first
        | (have hw : CTy.float w = CTy.float 16 := by assumption
           simp only [CTy.float.injEq] at hw; subst hw; rfl)
        | (have hw : CTy.float w = CTy.float 32 := by assumption
           simp only [CTy.float.injEq] at hw; subst hw; rfl)
        | (have hw : CTy.float w = CTy.float 64 := by assumption
           simp only [CTy.float.injEq] at hw; subst hw; rfl)

/-- The scalar size of an index (the decoding `ofV` uses; `fpu_cmp`'s output only reaches
`ofV` for indices `0..4`, where it is the matching `OperandSize`). -/
def sizeOfIdx : Nat → ScalarSize
  | 0 => .size8 | 1 => .size16 | 2 => .size32 | 3 => .size64 | 4 => .size128 | _ => .size8

/-- The condition instruction `fpu_cmp` builds decodes at any scalar size index `k ≤ 4`
(`ssIdx` of a type is at most 4). -/
theorem ofV_fpuCmp {k : Nat} (hk : k ≤ 4) (rx ry : Reg) :
    MInst.ofV (.data 58 56 [.data 95 k [], .reg rx, .reg ry]) =
      some (.fpuCmp (sizeOfIdx k) rx ry) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The `hsz` fact of `emit_fcmp_core` at `f32`: the size index `2`. -/
theorem hsz32 {sz : ScalarSize} (h : sz = .size32) :
    ∀ ty : Clif.Ty, CTy.ofClif ty = .float 32 →
      (ty = .f32 → sz = .size32) ∧ (ty = .f64 → sz = .size64) := by
  subst h
  rintro ty h'
  cases ty <;> simp [CTy.ofClif] at h' ⊢

/-- The `hsz` fact of `emit_fcmp_core` at `f64`: the size index `3`. -/
theorem hsz64 {sz : ScalarSize} (h : sz = .size64) :
    ∀ ty : Clif.Ty, CTy.ofClif ty = .float 64 →
      (ty = .f32 → sz = .size32) ∧ (ty = .f64 → sz = .size64) := by
  subst h
  rintro ty h'
  cases ty <;> simp [CTy.ofClif] at h' ⊢

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`emit_fcmp`** over a float-capable context: the condition is `fcmp cc` of the operands'
values. On a frame where the operands hold values of the controlling type, the condition's
truth is `fcmp cc` on them (`emit_fcmp_core`); otherwise the condition is unreachable
(`FcmpT` is false, `fcmp` of a non-float type traps). -/
theorem emit_fcmp_okT {F : BitVec 64 → Prop} {isem : Sem} {f : Clif.Function}
    (hctx : CtxInvT f ctx) {n : Nat} (hn : 200 ≤ n) {cc : Clif.FloatCC} (hok : fccOk cc = true)
    {x y : Nat} {s s' : LState × Array RuleId} {c : V} (hvb : ValsBelow ctx s.1)
    (h : ApplyInternal p (sem ctx) cfg n 123 655 [.data 144 (fccIdx cc) [], .value x, .value y]
      s c s') :
    CondCode F isem ctx s.1 s'.1 c (FcmpT cc x y) := by
  isel_split' hp hc h 655
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  -- rules 527/528 (`one`/`ueq`): excluded by `fccOk`
  all_goals try
    (exfalso
     have h9 : fccIdx cc = 9 := by assumption
     have := fccOk_ne h9 hok
     omega)
  all_goals try
    (exfalso
     have h9 : fccIdx cc = 7 := by assumption
     have := fccOk_ne h9 hok
     omega)
  · -- rule 526
    obtain ⟨hk, hst1⟩ := scalar_size_ok hp hc ‹_› (by omega)
    obtain ⟨hst2, hv8⟩ := fpu_cmp_ok hp hc ‹_› (by omega)
    obtain ⟨hst3, cc', cond, hfk, hfc, hv7⟩ := fp_cond_code_ok hp hc ‹_› (by omega)
    obtain rfl := fccIdx_inj hfk
    have hvx : _ = Reg.vreg x (valClassOf ctx x) := hctx.valueReg x _ (by assumption)
    have hvy : _ = Reg.vreg y (valClassOf ctx y) := hctx.valueReg y _ (by assumption)
    subst hvx
    subst hvy
    dsimp only at hst3 hst2
    rw [hv8, hk, hv7, hst3, hst2, hst1]
    refine CondCode.flag (ms := []) (Frag.nil _) (ofV_fpuCmp (ssIdx_le _) _ _)
      (fpCond?_ne_al hfc) rfl ?_ ?_
    · intro u hu
      rw [vuseNums_fpuCmp] at hu
      rcases mem2 hu with rfl | rfl
      · exact vreg_lt hvb (by assumption)
      · exact vreg_lt hvb (by assumption)
    · rintro fr ρ b hh hdf ⟨ty, xa, xb, hxv, hyv, hb⟩
      have hrt : _ = _ := vholds_ty hdf (by assumption) hyv
      subst hrt
      cases ty with
      | f32 =>
        have hxq : ctx.valueReg? x = some (Reg.vreg x (valClassOf ctx x)) := by assumption
        have hyq : ctx.valueReg? y = some (Reg.vreg y (valClassOf ctx y)) := by assumption
        have hTy : ctx.valueType? y = some (CTy.ofClif Clif.Ty.f32) := by assumption
        exact emit_fcmp_core_run hvb hfc hxq hyq hTy
          (ofV_fpuCmp (ssIdx_le (CTy.ofClif Clif.Ty.f32)) _ _) (hsz32 rfl) fr ρ b hh hdf
          ⟨.f32, xa, xb, hxv, hyv, hb⟩
      | f64 =>
        have hxq : ctx.valueReg? x = some (Reg.vreg x (valClassOf ctx x)) := by assumption
        have hyq : ctx.valueReg? y = some (Reg.vreg y (valClassOf ctx y)) := by assumption
        have hTy : ctx.valueType? y = some (CTy.ofClif Clif.Ty.f64) := by assumption
        exact emit_fcmp_core_run hvb hfc hxq hyq hTy
          (ofV_fpuCmp (ssIdx_le (CTy.ofClif Clif.Ty.f64)) _ _) (hsz64 rfl) fr ρ b hh hdf
          ⟨.f64, xa, xb, hxv, hyv, hb⟩
      | _ => simp [Clif.FSem.fcmp] at hb

end Contract

end Terms

end Backend.Proof
