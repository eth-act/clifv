import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.IselFloatBitcast

/-!
# S11f: `fcmp` conditions (`emit_fcmp`, `inst.isle:5210`)

`emit_fcmp cc x y` for every condition but `one`/`ueq` (which `instData` keeps outside the
lowering: their rule, `inst.isle:5216/5219`, builds the two-condition `CondResult.Or`): the flag
producer `fcmp sn, sm` / `fcmp dn, dm` (`fpu_cmp` at the operands' scalar size, `MInst.FpuCmp`)
and the Arm condition `fp_cond_code cc` (`fpCond`). Its truth on `FCMP`'s flags (`fcmpFlags`, the
Arm model's `FPCompare` NZCV) is CLIF's `fcmp cc` on the same shared `IEEE.compare`
(`condOn_fpCond`, checked over the 12 conditions and the 4 comparison results).

`emit_fcmp_okT` is the `CondCode` of `emit_fcmp` over float-capable contexts; it serves the
`fcmp` root (`IselFloatArith`) and the `fcmp` look-through of `is_nonzero_cmp` (`IselCmpRoot`),
hence the `select`/`brif`/`trapz`/`trapnz` consumers.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Float conditions -/

/-- The variant index of a CLIF float condition in ISLE's `FloatCC`. -/
def fccIdx : Clif.FloatCC → Nat
  | .eq => 0 | .gt => 1 | .ge => 2 | .lt => 3 | .le => 4 | .ne => 5 | .ord => 6 | .one => 7
  | .uno => 8 | .ueq => 9 | .ugt => 10 | .uge => 11 | .ult => 12 | .ule => 13

theorem mkVariant_floatcc (cc : Clif.FloatCC) :
    mkVariant tyFloatCC (floatccName cc) = .data 144 (fccIdx cc) [] := by
  cases cc <;> rfl

/-- `fp_cond_code` (`inst.isle:5230-5257`): the Arm condition testing a float condition on
`FCMP`'s flags (`one`/`ueq` have no rule). -/
def fpCond : Clif.FloatCC → Cond
  | .ord => .vc | .uno => .vs | .eq => .eq | .ne => .ne | .lt => .mi | .le => .ls
  | .gt => .gt | .ge => .ge | .ult => .lt | .ule => .le | .ugt => .hi | .uge => .pl
  | .one => .al | .ueq => .al

/-- The conditions `instData` admits (`one`/`ueq` are outside the lowering). -/
def FccOk (cc : Clif.FloatCC) : Prop := cc ≠ .one ∧ cc ≠ .ueq

theorem fpCond_ne_al {cc : Clif.FloatCC} (h : FccOk cc) : fpCond cc ≠ .al ∧ fpCond cc ≠ .nv := by
  obtain ⟨h1, h2⟩ := h
  cases cc <;> simp_all [fpCond]

/-- **`fp_cond_code` decides CLIF's `fcmp`**: on the flags `FCMP` writes for a comparison
result, the condition `fpCond cc` holds iff `fcmp cc` does. -/
theorem condOn_fpCond {cc : Clif.FloatCC} (h : FccOk cc) (c : IEEE.Cmp) :
    condOn (fpCond cc).bits (fcmpFlags c) = Clif.FSem.condHolds cc c := by
  obtain ⟨h1, h2⟩ := h
  cases cc <;> cases c <;> first | (exact absurd rfl ‹_›) | decide

/-! ## Instruction data and CLIF semantics of `fcmp` -/

set_option maxRecDepth 20000 in
theorem variantNames_FloatCompare : (variantNames 152)[11]? = some "FloatCompare" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Fcmp : (variantNames 151)[112]? = some "Fcmp" := rfl

/-- A matched `FloatCompare (Fcmp)` is an `fcmp` at a float type, of a condition `instData`
admits. -/
theorem instData_fcmp_inv {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V}
    (h : instData f cl = .ok (.data 152 11 [.data 151 112 [], w1, w2])) :
    ∃ cc ty x y, cl = .float (.fcmp cc) ty [x, y] ∧ ty.isFloat = true ∧ FccOk cc ∧
      w1 = .values [x, y] ∧ w2 = .data 144 (fccIdx cc) [] := by
  obtain ⟨hf, -⟩ := instData_inv_names h
  rw [variantNames_FloatCompare] at hf
  cases cl <;> simp [instNames] at hf
  rename_i op ty args
  cases op <;> simp [fFmt] at hf
  rename_i cc
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, throw, throwThe, MonadExceptOf.throw,
      reduceCtorEq] at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hfl, h1⟩, h2⟩ := hok
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq, mkVariant_floatcc] at h3
    exact ⟨cc, ty, x, y, rfl, hfl, ⟨h1, h2⟩, h3.2.1, h3.2.2.1⟩
  · simp only [reduceCtorEq] at h

/-- The bits of a value at its type (`Val.at`). -/
theorem val_at_ok {v : Clif.Val} {ty : Clif.Ty} {a : BitVec ty.width} (h : v.at ty = .ok a) :
    v = ⟨ty, a⟩ := by
  obtain ⟨vty, vb⟩ := v
  unfold Clif.Val.at Clif.Val.as? at h
  by_cases hty : vty = ty
  · subst hty
    simp [Clif.Res.ofOption] at h
    rw [h]
  · simp [hty, Clif.Res.ofOption] at h

theorem getMany_two {fr : Clif.Frame} {x y : Nat} {vs : List Clif.Val}
    (h : fr.getMany [x, y] = .ok vs) :
    ∃ a b, fr.regs x = some a ∧ fr.regs y = some b ∧ vs = [a, b] := by
  simp only [Clif.Frame.getMany, Clif.Frame.get, bind, Clif.Res.bind] at h
  cases hx : fr.regs x <;> cases hy : fr.regs y <;>
    simp [hx, hy, Clif.Res.ofOption, pure] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem getMany_one {fr : Clif.Frame} {x : Nat} {vs : List Clif.Val}
    (h : fr.getMany [x] = .ok vs) : ∃ a, fr.regs x = some a ∧ vs = [a] := by
  simp only [Clif.Frame.getMany, Clif.Frame.get, bind, Clif.Res.bind] at h
  cases hx : fr.regs x <;> simp [hx, Clif.Res.ofOption, pure] at h
  exact ⟨_, rfl, h.symm⟩

/-- CLIF `float op ty args`: the operands' values and the result. -/
theorem evalInst_float_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.FOp} {ty : Clif.Ty}
    {args : List Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.float op ty args) = .ok (vals, cm')) :
    ∃ vs r, fr.getMany args = .ok vs ∧ Clif.evalFloat op ty vs = .ok r ∧ vals = [r] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hg : fr.getMany args with
  | ok vs =>
    rw [hg] at h
    simp only [bind, Clif.Res.bind] at h
    cases he : Clif.evalFloat op ty vs with
    | ok r =>
      rw [he] at h
      simp only [pure, Clif.Res.ok.injEq, Prod.mk.injEq] at h
      exact ⟨vs, r, rfl, he, h.1.symm, h.2.symm⟩
    | trap _ => rw [he] at h; cases h
    | stuck _ => rw [he] at h; cases h
  | trap _ => rw [hg] at h; cases h
  | stuck _ => rw [hg] at h; cases h

/-- CLIF `fcmp cc ty x y`: both operands of type `ty`, the `i8` truth of `fcmp`. -/
theorem evalInst_fcmp_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {cc : Clif.FloatCC} {ty : Clif.Ty}
    {x y : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.float (.fcmp cc) ty [x, y]) = .ok (vals, cm')) :
    ∃ (a b : BitVec ty.width) (r : Bool), fr.regs x = some ⟨ty, a⟩ ∧ fr.regs y = some ⟨ty, b⟩ ∧
      Clif.FSem.fcmp cc ty a b = some r ∧ vals = [Clif.Val.ofBool r] ∧ cm' = cm := by
  obtain ⟨vs, r, hg, he, rfl, rfl⟩ := evalInst_float_ok h
  obtain ⟨va, vb, hx, hy, rfl⟩ := getMany_two hg
  simp only [Clif.evalFloat, bind, Clif.Res.bind] at he
  cases ha : va.at ty with
  | ok a =>
    rw [ha] at he
    cases hb : vb.at ty with
    | ok b =>
      rw [hb] at he
      simp only [Clif.Res.ofOption] at he
      cases hc : Clif.FSem.fcmp cc ty a b with
      | none => rw [hc] at he; cases he
      | some c =>
        rw [hc] at he
        simp only [pure, Clif.Res.ok.injEq] at he
        rw [val_at_ok ha] at hx
        rw [val_at_ok hb] at hy
        exact ⟨a, b, c, hx, hy, hc, by rw [he], rfl⟩
    | trap _ => rw [hb] at he; cases he
    | stuck _ => rw [hb] at he; cases he
  | trap _ => rw [ha] at he; cases he
  | stuck _ => rw [ha] at he; cases he

/-- The truth of an `fcmp cc` of the values of `x`, `y` (the `CondCode` target of
`emit_fcmp`). -/
def FcmpT (cc : Clif.FloatCC) (x y : Nat) (fr : Clif.Frame) (b : Bool) : Prop :=
  ∃ (ty : Clif.Ty) (a b' : BitVec ty.width), fr.regs x = some ⟨ty, a⟩ ∧ fr.regs y = some ⟨ty, b'⟩ ∧
    Clif.FSem.fcmp cc ty a b' = some b

/-! ## The `FCMP` flags -/

theorem vdefs_fpuCmp (sz : ScalarSize) (a b : Nat) (c1 c2 : RegClass) :
    vdefs (.fpuCmp sz (.vreg a c1) (.vreg b c2)) = [] := rfl
theorem vuseNums_fpuCmp (sz : ScalarSize) (a b : Nat) (c1 c2 : RegClass) :
    vuseNums (.fpuCmp sz (.vreg a c1) (.vreg b c2)) = [a, b] := rfl

theorem setsFlags_fpuCmp32 (a b : Nat) (c1 c2 : RegClass) (ρ : Nat → CV) :
    SetsFlags (.fpuCmp .size32 (.vreg a c1) (.vreg b c2)) ρ
      (fcmpFlags (IEEE.compare .b32 ((ρ a).setWidth 32) ((ρ b).setWidth 32))) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

theorem setsFlags_fpuCmp64 (a b : Nat) (c1 c2 : RegClass) (ρ : Nat → CV) :
    SetsFlags (.fpuCmp .size64 (.vreg a c1) (.vreg b c2)) ρ
      (fcmpFlags (IEEE.compare .b64 ((ρ a).setWidth 64) ((ρ b).setWidth 64))) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

/-- `FCMP`'s condition on held `f32`/`f64` values is CLIF's `fcmp`. -/
theorem fcmp_cond {cc : Clif.FloatCC} (hcc : FccOk cc) {ty : Clif.Ty} {a b : BitVec ty.width}
    {X Y : CV} {r : Bool} (hx : VHolds ⟨ty, a⟩ X) (hy : VHolds ⟨ty, b⟩ Y)
    (hr : Clif.FSem.fcmp cc ty a b = some r) :
    (ty = .f32 ∧ condOn (fpCond cc).bits
        (fcmpFlags (IEEE.compare .b32 (X.setWidth 32) (Y.setWidth 32))) = r) ∨
      (ty = .f64 ∧ condOn (fpCond cc).bits
        (fcmpFlags (IEEE.compare .b64 (X.setWidth 64) (Y.setWidth 64))) = r) := by
  cases ty <;> simp only [Clif.FSem.fcmp, reduceCtorEq, Option.some.injEq] at hr
  · refine .inl ⟨rfl, ?_⟩
    have ha : X.setWidth 32 = a := hx
    have hb : Y.setWidth 32 = b := hy
    rw [ha, hb, condOn_fpCond hcc, hr]
  · refine .inr ⟨rfl, ?_⟩
    have ha : X.setWidth 64 = a := hx
    have hb : Y.setWidth 64 = b := hy
    rw [ha, hb, condOn_fpCond hcc, hr]

/-! ## The internal terms -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `fpu_cmp` (`inst.isle:2606`): the side-effect flag producer `MInst.FpuCmp`. -/
theorem fpu_cmp_ok {n : Nat} (hn : 30 ≤ n) {a b k : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 47 370 [k, a, b] s v s') :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 56 [k, a, b]] := by
  isel_split hp hc h 370
  isel_inv [*, rule_inst_2606] at hm he

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `fp_cond_code` (`inst.isle:5230-5257`) on a condition `instData` admits. -/
theorem fp_cond_code_ok {n : Nat} (hn : 40 ≤ n) {cc : Clif.FloatCC} (hcc : FccOk cc)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 96 656 [.data 144 (fccIdx cc) []] s v s') :
    s'.1 = s.1 ∧ v = .data 96 (fpCond cc).idx [] := by
  obtain ⟨h1, h2⟩ := hcc
  isel_split hp hc h 656
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv [*, rule_inst_5232, rule_inst_5235, rule_inst_5237, rule_inst_5239,
    rule_inst_5241, rule_inst_5243, rule_inst_5245, rule_inst_5247, rule_inst_5249,
    rule_inst_5251, rule_inst_5253, rule_inst_5255] at hm he
  all_goals (cases cc <;> first | exact absurd rfl h1 | exact absurd rfl h2 | (simp_all [fccIdx, fpCond]; done) | skip)
  case _ => trace_state; sorry
  all_goals sorry

include hp hc in
/-- `scalar_size` of a lowering value type (`i8..i64`, `f32`, `f64`). -/
theorem scalar_size_m_ok {n : Nat} (hn : 40 ≤ n) {t : CTy} (ht : t ∈ mCTys)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 307 [.ty t] s v s') :
    s'.1 = s.1 ∧ ∃ k sz, v = .data 95 k [] ∧ ScalarSize.ofIdx? k = some sz ∧
      (t = .float 32 → sz = .size32) ∧ (t = .float 64 → sz = .size64) := by
  rcases mCTys_cases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨rfl, hs⟩ := scalar_size_int_ok hp hc hn (by decide) h
    exact ⟨hs, _, .size8, rfl, rfl, by simp, by simp⟩
  · obtain ⟨rfl, hs⟩ := scalar_size_int_ok hp hc hn (by decide) h
    exact ⟨hs, _, .size16, rfl, rfl, by simp, by simp⟩
  · obtain ⟨rfl, hs⟩ := scalar_size_int_ok hp hc hn (by decide) h
    exact ⟨hs, _, .size32, rfl, rfl, by simp, by simp⟩
  · obtain ⟨rfl, hs⟩ := scalar_size_int_ok hp hc hn (by decide) h
    exact ⟨hs, _, .size64, rfl, rfl, by simp, by simp⟩
  · obtain ⟨rfl, hs⟩ := scalar_size_float_ok hp hc hn (by decide) h
    exact ⟨hs, _, .size32, rfl, rfl, fun _ => rfl, by simp⟩
  · obtain ⟨rfl, hs⟩ := scalar_size_float_ok hp hc hn (by decide) h
    exact ⟨hs, _, .size64, rfl, rfl, by simp, fun _ => rfl⟩

end Terms

/-! ## `emit_fcmp` -/

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

theorem ofV_fpuCmp {k : Nat} {sz : ScalarSize} (hk : ScalarSize.ofIdx? k = some sz) (rx ry : Reg) :
    MInst.ofV (.data 58 56 [.data 95 k [], .reg rx, .reg ry]) = some (.fpuCmp sz rx ry) := by
  simp [MInst.ofV, V.scalarSize?, V.enum?, V.enumOf?, hk, V.reg?]

set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`emit_fcmp`** over a float-capable context, on a condition `instData` admits: the flag
producer `fcmp` of the operands' registers at their scalar size, tested by `fp_cond_code cc`; the
condition is CLIF's `fcmp cc` of the operands' values. -/
theorem emit_fcmp_okT {F : BitVec 64 → Prop} {isem : Sem} {f : Clif.Function}
    (hctx : CtxInvT f ctx) {n : Nat} (hn : 200 ≤ n) {cc : Clif.FloatCC} (hcc : FccOk cc) {x y : Nat}
    {s s' : LState × Array RuleId} {c : V} (hvb : ValsBelow ctx s.1)
    (h : ApplyInternal p (sem ctx) cfg n 123 655 [.data 144 (fccIdx cc) [], .value x, .value y] s c s') :
    CondCode F isem ctx s.1 s'.1 c (FcmpT cc x y) := by
  have hp' := hp
  have hcc' := hcc
  obtain ⟨h1, h2⟩ := hcc'
  isel_split' hp hc h 655
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  all_goals try (cases cc <;> simp [fccIdx] at * <;> done)
  obtain ⟨t, ht, htw⟩ := (ext_value_type_iff ctx _ y _).mp ‹externExtract ctx T.value_type _ _ = _›
  simp only [List.cons.injEq, and_true] at htw
  subst htw
  obtain ⟨rx, hrx, rfl, rfl⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp
    ‹externCtor ctx T.put_in_reg [.value x] _ = _›
  obtain ⟨ry, hry, rfl, rfl⟩ := (ctor_put_in_reg_iff ctx _ y _ _).mp
    ‹externCtor ctx T.put_in_reg [.value y] _ = _›
  obtain ⟨hs1, k, sz, rfl, hk, hk32, hk64⟩ :=
    scalar_size_m_ok hp' hc (by omega) (hctx.valTyM y t ht) ‹ApplyInternal _ _ _ _ 95 307 _ _ _ _›
  obtain ⟨hs2, rfl⟩ := fpu_cmp_ok hp' hc (by omega) ‹ApplyInternal _ _ _ _ 47 370 _ _ _ _›
  obtain ⟨hs3, rfl⟩ := fp_cond_code_ok hp' hc (by omega) hcc ‹ApplyInternal _ _ _ _ 96 656 _ _ _ _›
  rw [hctx.valueReg x rx hrx]
  rw [hctx.valueReg y ry hry]
  refine (CondCode.flag (ms := []) (Frag.nil _) (ofV_fpuCmp hk _ _) (fpCond_ne_al hcc) rfl ?_ ?_).st_eq
    (by simp_all)
  · intro u hu
    rw [vuseNums_fpuCmp] at hu
    rcases mem2 hu with rfl | rfl
    · exact vreg_lt hvb hrx
    · exact vreg_lt hvb hry
  · rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, hr⟩
    refine ⟨UsesLo.nil _ _, fun u hu => ?_, fun w => Runs.nil ?_⟩
    · rw [vuseNums_fpuCmp] at hu
      rcases mem2 hu with rfl | rfl
      · exact .inr (by simp [hxv])
      · exact .inr (by simp [hyv])
    · have hty := vholds_ty hdf ht hyv
      rcases fcmp_cond hcc (hh x _ hxv) (hh y _ hyv) hr with ⟨rfl, hc32⟩ | ⟨rfl, hc64⟩
      · obtain rfl := hk32 hty.symm
        exact ⟨_, setsFlags_fpuCmp32 x y _ _ ρ, hc32⟩
      · obtain rfl := hk64 hty.symm
        exact ⟨_, setsFlags_fpuCmp64 x y _ _ ρ, hc64⟩

end

end Backend.Proof
