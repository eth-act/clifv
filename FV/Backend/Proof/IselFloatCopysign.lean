import FV.Backend.Proof.IselFloatArith
import FV.Backend.Proof.IselCopysignFamily

/-!
# #35: the scalar `fcopysign` root over float-capable contexts

`lower (fcopysign ty x y)` (`rule_lower_685`, `lower.isle:685`, id 712) is
`fcopy_sign (put_in_reg x) (put_in_reg y) ty`, whose scalar rule (`inst.isle:4612`, priority 1)
emits, into `dst = temp_writable_reg $F64` (allocated first) and the fresh `tmp` of `fpu_rri`:

* `ushr tmp, y, #max_shift` (`FpuRRI`, `fpu_op_ri_ushr (ty_bits ty) (max_shift ty)`): the sign bit
  of `y` moved to bit 0 (`ushr v.2s, #31` at `f32`, `ushr d, #63` at `f64`);
* `sli dst, tmp, #max_shift` with `dst` reusing `x` (`FpuRRIMod`, `reg_reuse_def`): the bits of `x`
  below the sign kept and `tmp` shifted back into the sign bit.

At `f32` the `2s` forms act on both 32-bit lanes of the low 64 bits; `VHolds` reads the low 32
only (lane 1 is junk). The vector rule (`inst.isle:4619`, `multi_lane`) never matches a scalar
float type. The result is `Clif.FSem.copysign` (`copysign32_ushr_sli`, `copysign64_ushr_sli`),
so the root is proven over `CtxInvT` (`copysign_okT`) and with it the family
`LowerRulesCorrectCS` (`lowerRulesCorrectCS_program`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The shifts of a float type -/

/-- `max_shift ty` (`inst.isle:4606-4607`) of a float width: `63` at 64 bits, `31` at 32. -/
def maxShift (w : Nat) : Int := w - 1

/-- The `ushr` of `fcopy_sign`'s scalar rule at a float type
(`fpu_op_ri_ushr (ty_bits ty) (max_shift ty)`). -/
def csUShr : Clif.Ty → FPUOpRI
  | .f32 => .uShr32 31
  | _ => .uShr64 63

/-- The `sli` of `fcopy_sign`'s scalar rule at a float type
(`fpu_op_ri_sli (ty_bits ty) (max_shift ty)`). -/
def csSli : Clif.Ty → FPUOpRIMod
  | .f32 => .sli32 31
  | _ => .sli64 63

/-! ## Semantics: `ushr` + `sli` is `fcopysign` -/

/-- **`fcopysign.f32` is `ushr v.2s, #31` + `sli v.2s, #31`**: on register values `zx`, `zy` (the
operands in their low 32 bits), the `ushr` of `zy` and the `sli` into `zx` give a register value
whose low 32 bits are `Clif.FSem.copysign` of the operands' (the upper lane is junk). -/
theorem copysign32_ushr_sli (zx zy : CV) :
    ∃ t z, fpuRRIOut (.uShr32 31) zy = some t ∧ fpuRRIModOut (.sli32 31) zx t = some z ∧
      VHolds ⟨.f32, Clif.FSem.copysign .b32 (zx.setWidth 32) (zy.setWidth 32)⟩ z := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  show BitVec.setWidth 32 _ = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Clif.FSem.copysign, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  have h2 : (2147483648 : Nat).testBit i = decide (i = 31) := by
    rw [show (2147483648 : Nat) = 2 ^ 31 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]
  by_cases h31 : i < 31
  · simp [h31, h2, show i < 64 by omega, show i < 128 by omega, show i ≠ 31 by omega]
  · obtain rfl : i = 31 := by omega
    simp [h2]

/-- **`fcopysign.f64` is `ushr d, #63` + `sli d, #63`**: as `copysign32_ushr_sli` on the low 64
bits. -/
theorem copysign64_ushr_sli (zx zy : CV) :
    ∃ t z, fpuRRIOut (.uShr64 63) zy = some t ∧ fpuRRIModOut (.sli64 63) zx t = some z ∧
      VHolds ⟨.f64, Clif.FSem.copysign .b64 (zx.setWidth 64) (zy.setWidth 64)⟩ z := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  show BitVec.setWidth 64 _ = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Clif.FSem.copysign, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  have h2 : (9223372036854775808 : Nat).testBit i = decide (i = 63) := by
    rw [show (9223372036854775808 : Nat) = 2 ^ 63 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]
  by_cases h63 : i < 63
  · simp [h63, h2, show i < 128 by omega, show i ≠ 63 by omega]
  · obtain rfl : i = 63 := by omega
    simp [h2]

/-- **CLIF `fcopysign` is the `ushr` + `sli` the rule emits**: on register values holding the
operands, the two instructions' outputs exist and the second holds CLIF's result. -/
theorem copysign_holds {ty : Clif.Ty} (hty : ty = .f32 ∨ ty = .f64) {a b r : Clif.Val}
    {za zb : CV} (ha : VHolds a za) (hb : VHolds b zb)
    (h : Clif.evalFloat .fcopysign ty [a, b] = .ok r) :
    ∃ t z, fpuRRIOut (csUShr ty) zb = some t ∧ fpuRRIModOut (csSli ty) za t = some z ∧
      VHolds r z := by
  rcases hty with rfl | rfl <;>
    simp only [Clif.evalFloat, Clif.FSem.binary, bind, Clif.Res.bind] at h
  all_goals
    cases ha' : a.at _ with
    | ok xa =>
      rw [ha'] at h
      cases hb' : b.at _ with
      | ok xb =>
        rw [hb'] at h
        obtain rfl := val_at_ok ha'
        obtain rfl := val_at_ok hb'
        simp only [Clif.FSem.lift2, Clif.Res.ofOption, pure, Clif.Res.ok.injEq] at h
        subst h
        first
          | (have ha2 : za.setWidth 32 = xa := ha
             have hb2 : zb.setWidth 32 = xb := hb
             subst ha2 hb2
             exact copysign32_ushr_sli za zb)
          | (have ha2 : za.setWidth 64 = xa := ha
             have hb2 : zb.setWidth 64 = xb := hb
             subst ha2 hb2
             exact copysign64_ushr_sli za zb)
      | trap _ => rw [hb'] at h; cases h
      | stuck _ => rw [hb'] at h; cases h
    | trap _ => rw [ha'] at h; cases h
    | stuck _ => rw [ha'] at h; cases h

/-! ## `LowerInstOk` of the two emitted instructions -/

/-- **`LowerInstOk` of `fcopysign` lowered to `ushr` + `sli`**: `dst` is the first fresh vreg
(`st.nextVreg`, `temp_writable_reg`), `tmp` the second (`fpu_rri`'s). The `sli` reads `x`, which
is below the fresh vregs (`ValsBelow`), so the `ushr` into `tmp` does not clobber it. -/
theorem lowerInstOk_fcopysign {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {ctx : Ctx} {ty : Clif.Ty}
    (hty : ty = .f32 ∨ ty = .f64) {x y : Nat} {cx cy : RegClass} {results : List Nat}
    {st : LState} (hR : Refines F isem) (hMR : MRStable F MR) (hx : x < st.nextVreg) :
    LowerInstOk isem MR env cp ctx (.float .fcopysign ty [x, y]) results st
      [[.vreg st.nextVreg .float]]
      ((((st.fresh .float).2.fresh .float).2.emit
        (.fpuRRI (csUShr ty) (.vreg (st.nextVreg + 1) .float) (.vreg y cy))).emit
        (.fpuRRIMod (csSli ty) (.vreg st.nextVreg .float) (.vreg x cx)
          (.vreg (st.nextVreg + 1) .float)))
      [.fpuRRI (csUShr ty) (.vreg (st.nextVreg + 1) .float) (.vreg y cy),
        .fpuRRIMod (csSli ty) (.vreg st.nextVreg .float) (.vreg x cx)
          (.vreg (st.nextVreg + 1) .float)] := by
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh] <;> omega) ?_ rfl ?_
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    rcases hmi with rfl | rfl
    · have hv : vdefs (.fpuRRI (csUShr ty) (.vreg (st.nextVreg + 1) .float) (.vreg y cy)) =
          [st.nextVreg + 1] := rfl
      rw [hv, List.mem_singleton] at he
      subst he
      simp [LState.emit, LState.fresh] <;> omega
    · have hv : vdefs (.fpuRRIMod (csSli ty) (.vreg st.nextVreg .float) (.vreg x cx)
          (.vreg (st.nextVreg + 1) .float)) = [st.nextVreg] := rfl
      rw [hv, List.mem_singleton] at he
      subst he
      simp [LState.emit, LState.fresh] <;> omega
  · intro fr cm ρ vals cm' _ hvals _ ho
    have ho' : Clif.evalInst fr cm (.float .fcopysign ty [x, y]) = .ok (vals, cm') := ho
    obtain ⟨vs, r, hv, hr, rfl, rfl⟩ := evalInst_float_ok ho'
    obtain ⟨a, b, hxa, hyb, rfl⟩ := getMany_two hv
    obtain ⟨t, z, ht, hz, hrz⟩ := copysign_holds hty (hvals x a hxa) (hvals y b hyb) hr
    have hne : x ≠ st.nextVreg + 1 := by omega
    refine ⟨rfl, ?_, .inl (Nat.le_refl _), r,
      upd (upd ρ (st.nextVreg + 1) t) st.nextVreg z, rfl,
      prun_rr_c (r := t) hR rfl (fun w => ?_)
        (prun_cons hR rfl (outs := [z]) (fun w => ?_) rfl (prun_nil _)), ?_⟩
    · refine usesOk_of [x, y] ?_ (by simp [hxa, hyb])
      intro mi hmi u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
      rcases hmi with rfl | rfl
      · have hu' : vuseNums (.fpuRRI (csUShr ty) (.vreg (st.nextVreg + 1) .float)
            (.vreg y cy)) = [y] := rfl
        rw [hu', List.mem_singleton] at hu
        subst hu
        exact .inr (by simp)
      · have hu' : vuseNums (.fpuRRIMod (csSli ty) (.vreg st.nextVreg .float) (.vreg x cx)
            (.vreg (st.nextVreg + 1) .float)) = [x, st.nextVreg + 1] := rfl
        rw [hu'] at hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl
        · exact .inr (by simp)
        · exact .inl (by omega)
    · first
        | (show ispecFP (.fpuRRI (csUShr ty) (.vreg (st.nextVreg + 1) .float) (.vreg y cy))
            [ρ y] w = _
           simp only [ispecFP, ht, Option.map_some]
           rfl)
        | (simp only [ispec, ispecFP, ht, Option.map_some]; rfl)
    · first
        | (show ispecFP (.fpuRRIMod (csSli ty) (.vreg st.nextVreg .float) (.vreg x cx)
            (.vreg (st.nextVreg + 1) .float))
            [upd ρ (st.nextVreg + 1) t x, upd ρ (st.nextVreg + 1) t (st.nextVreg + 1)] w = _
           simp only [ispecFP, upd, hne, ↓reduceIte, hz, Option.map_some]
           rfl)
        | (simp only [ispec, ispecFP, vuses, upd, hne, ↓reduceIte, hz, Option.map_some]; rfl)
    · simp only [upd, ↓reduceIte]
      exact hrz

/-! ## Internal terms: `fpu_rri`, `max_shift`, `fcopy_sign` -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

theorem ext_multi_lane_float (st : LState) (w : Nat) (fs : List V) :
    externExtract ctx T.multi_lane (.ty (.float w)) st = .ok fs ↔ False := by
  have e : externExtract ctx T.multi_lane (.ty (.float w)) st = .fail := rfl
  rw [e]; simp

theorem ctor_fpu_op_ri_ushr_iff (st : LState) (b s : Int) (v : V) (st' : LState) :
    externCtor ctx T.fpu_op_ri_ushr [.int b, .int s] st = .ok (v, st') ↔
      ushrImmOk s b = true ∧ v = .data tyFPUOpRI (laneVariant b) [.int s, .int b] ∧ st' = st := by
  have : externCtor ctx T.fpu_op_ri_ushr [.int b, .int s] st =
      if ushrImmOk s b then .ok (.data tyFPUOpRI (laneVariant b) [.int s, .int b], st)
      else .unmodeled "fpu_op_ri_ushr: size not 32/64 or shift out of range" := rfl
  rw [this]
  cases hk : ushrImmOk s b
  · simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and]
  · simp only [↓reduceIte, Isle.ExtResult.ok.injEq, Prod.mk.injEq, true_and]
    exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

theorem ctor_fpu_op_ri_sli_iff (st : LState) (b s : Int) (v : V) (st' : LState) :
    externCtor ctx T.fpu_op_ri_sli [.int b, .int s] st = .ok (v, st') ↔
      sliImmOk s b = true ∧ v = .data tyFPUOpRIMod (laneVariant b) [.int s, .int b] ∧
        st' = st := by
  have : externCtor ctx T.fpu_op_ri_sli [.int b, .int s] st =
      if sliImmOk s b then .ok (.data tyFPUOpRIMod (laneVariant b) [.int s, .int b], st)
      else .unmodeled "fpu_op_ri_sli: size not 32/64 or shift out of range" := rfl
  rw [this]
  cases hk : sliImmOk s b
  · simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and]
  · simp only [↓reduceIte, Isle.ExtResult.ok.injEq, Prod.mk.injEq, true_and]
    exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `fpu_rri` (`inst.isle:2583`): `MInst.FpuRRI` into a fresh float vreg. -/
theorem fpu_rri_ok {n : Nat} (hn : 40 ≤ n) {op a : V} {st st' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 367 [op, a] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 53 [op, .reg rd, a]) := by
  isel_split hp hc h 367
  isel_inv [*, rule_inst_2583, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_f64_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `max_shift` (`inst.isle:4606-4607`) of `f32`/`f64`: `31`/`63`, the state unchanged. -/
theorem max_shift_ok {n : Nat} (hn : 40 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 1 623 [.ty (.float w)] s v s') :
    v = .int (maxShift w) ∧ s'.1 = s.1 := by
  rcases hw with rfl | rfl
  all_goals
    isel_split hp hc h 623
    all_goals
      isel_inv [*, rule_inst_4606, rule_inst_4607, CTy.int.injEq, CTy.float.injEq] at hm he
    all_goals first
      | exact ⟨rfl, rfl⟩
      | rfl
      | decide
      | (exfalso; revert ‹CTy.float _ = CTy.float _›; decide)

/-- The `FpuRRI` `fcopy_sign`'s `fpu_rri` emitted at `f32`. -/
theorem ofV_ushr32 {rd rn : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 53 [.data tyFPUOpRI (laneVariant ↑(CTy.float 32).bits)
      [.int (maxShift 32), .int ↑(CTy.float 32).bits], .reg rd, .reg rn]) = some m) :
    m = .fpuRRI (csUShr .f32) rd rn :=
  Option.some.inj (h.symm.trans rfl)

/-- The `FpuRRI` `fcopy_sign`'s `fpu_rri` emitted at `f64`. -/
theorem ofV_ushr64 {rd rn : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 53 [.data tyFPUOpRI (laneVariant ↑(CTy.float 64).bits)
      [.int (maxShift 64), .int ↑(CTy.float 64).bits], .reg rd, .reg rn]) = some m) :
    m = .fpuRRI (csUShr .f64) rd rn :=
  Option.some.inj (h.symm.trans rfl)

/-- The `FpuRRIMod` `fcopy_sign` emitted at `f32`. -/
theorem ofV_sli32 {rd ri rn : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 54 [.data tyFPUOpRIMod (laneVariant ↑(CTy.float 32).bits)
      [.int (maxShift 32), .int ↑(CTy.float 32).bits], .reg rd, .reg ri, .reg rn]) = some m) :
    m = .fpuRRIMod (csSli .f32) rd ri rn :=
  Option.some.inj (h.symm.trans rfl)

/-- The `FpuRRIMod` `fcopy_sign` emitted at `f64`. -/
theorem ofV_sli64 {rd ri rn : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 54 [.data tyFPUOpRIMod (laneVariant ↑(CTy.float 64).bits)
      [.int (maxShift 64), .int ↑(CTy.float 64).bits], .reg rd, .reg ri, .reg rn]) = some m) :
    m = .fpuRRIMod (csSli .f64) rd ri rn :=
  Option.some.inj (h.symm.trans rfl)

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `fcopy_sign` (`inst.isle:4612`, the scalar rule; the vector rule `4619` needs `multi_lane`)
at `f32`/`f64` on registers `ra` (`x`), `rb` (`y`): `dst` (fresh first), then `fpu_rri`'s `ushr`
into the next fresh vreg `tmp`, then the `sli` into `dst` reusing `ra`; the result is `dst`. -/
theorem fcopy_sign_ok {n : Nat} (hn : 100 ≤ n) {ty : Clif.Ty} (hty : ty = .f32 ∨ ty = .f64)
    {ra rb : Reg} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 624 [.reg ra, .reg rb, .ty (CTy.ofClif ty)] st v st') :
    v = .reg (.vreg st.1.nextVreg .float) ∧
      st'.1 = (((st.1.fresh .float).2.fresh .float).2.emit
        (.fpuRRI (csUShr ty) (.vreg (st.1.nextVreg + 1) .float) rb)).emit
        (.fpuRRIMod (csSli ty) (.vreg st.1.nextVreg .float) ra (.vreg (st.1.nextVreg + 1) .float)) := by
  have hp' := hp
  rcases hty with rfl | rfl
  all_goals
    simp only [CTy.ofClif] at h
    isel_split hp hc h 624
    all_goals
      isel_inv [*, rule_inst_4612, rule_inst_4619, ctor_emit_iff, ctor_writable_reg_to_reg',
        ext_multi_lane_float] at hm he
    all_goals try (exfalso; exact (ext_multi_lane_float _ _ _).mp ‹externExtract ctx T.multi_lane _ _ = _›)
    obtain ⟨rfl, rfl⟩ :=
      (ctor_temp_writable_reg_f64_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
    revert ‹ApplyInternal _ _ _ _ 1 623 _ _ _ _›
    intro hs1
    obtain ⟨rfl, e1⟩ := max_shift_ok hp' hc (by omega) (by simp) hs1
    clear hs1
    revert ‹ApplyInternal _ _ _ _ 1 623 _ _ _ _›
    intro hs2
    obtain ⟨rfl, e2⟩ := max_shift_ok hp' hc (by omega) (by simp) hs2
    clear hs2
    obtain ⟨-, rfl, rfl⟩ := (ctor_fpu_op_ri_ushr_iff _ _ _ _ _).mp
      ‹externCtor ctx T.fpu_op_ri_ushr _ _ = _›
    obtain ⟨-, rfl, rfl⟩ := (ctor_fpu_op_ri_sli_iff _ _ _ _ _).mp
      ‹externCtor ctx T.fpu_op_ri_sli _ _ = _›
    have h367 := ‹ApplyInternal _ _ _ _ 27 367 _ _ _ _›
    obtain ⟨rfl, m1, hm1, hs3⟩ := fpu_rri_ok hp' hc (by omega) h367
    have hm2 := ‹MInst.ofV (V.data 58 54 _) = some _›
    refine ⟨rfl, ?_⟩
  · obtain rfl := ofV_ushr32 hm1
    obtain rfl := ofV_sli32 hm2
    (simp only [e2, hs3, e1]) <;> rfl
  · obtain rfl := ofV_ushr64 hm1
    obtain rfl := ofV_sli64 hm2
    (simp only [e2, hs3, e1]) <;> rfl

end Terms

/-! ## The matched instruction -/

theorem variantNames_Fcopysign : (variantNames 151)[121]? = some "Fcopysign" := rfl

/-- An instruction whose opcode name is `"Fcopysign"` is a float operation of that name. -/
theorem instNames_fcopysign {c : Clif.Inst} {s : String} (hs : s ∈ ["Fcopysign"])
    (h : (instNames c).2 = s) : ∃ op ty args, c = .float op ty args ∧ fOpc op = s := by
  cases c
  case float op ty args => exact ⟨op, ty, args, rfl, h⟩
  all_goals exfalso
  all_goals subst h
  all_goals simp only [instNames] at hs
  all_goals first
    | (simp at hs; done)
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at hs; done)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at hs; done)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at hs; done)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at hs; done)

/-- A matched `Binary` of opcode `Fcopysign` is an `fcopysign` at `f32`/`f64` (`instData`). -/
theorem instData_fcopysign_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 2 (.data 151 121 [] :: fs))) :
    ∃ ty x y, cl = .float .fcopysign ty [x, y] ∧ ty.isArithFloat = true ∧
      fs = [.values [x, y]] := by
  obtain ⟨-, ho⟩ := instData_inv_names h
  rw [variantNames_Fcopysign] at ho
  obtain ⟨op, ty, args, rfl, hop⟩ :=
    instNames_fcopysign (s := "Fcopysign") (by simp) (Option.some.inj ho).symm
  obtain rfl : op = .fcopysign := by cases op <;> simp [fOpc] at hop <;> rfl
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, fCvtOpcode, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at h
  split at h
  · rename_i hok
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq] at h3
    exact ⟨ty, x, y, rfl, hok, h3.2⟩
  · simp only [reduceCtorEq] at h

/-- The instruction the `fcopysign` root matched (`InstructionData::Binary`, `Fcopysign`). -/
theorem fcopysign_front {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst) {r : Rule}
    {tyPat xPat yPat : Pattern} {oT : TermId} {to : Term}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 [.term 151 oT [],
      .term 147 1614 [xPat, yPat]]]])
    (hto : termOf p oT = .ok to) (hko : to.kind = .enumVariant 121)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x y, inst = .float .fcopysign ty [x, y] ∧ ty.isArithFloat = true ∧
      info.data = .data 152 2 [.data 151 121 [], .values [x, y]] := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2449 term_2449_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨ty, x, y, rfl, hok, rfl⟩ := instData_fcopysign_inv hdat
  exact ⟨ty, x, y, rfl, hok, hd⟩

/-! ## The root -/

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of the `fcopysign` root** (`output_reg (fcopy_sign (put_in_reg x)
(put_in_reg y) ty)`), from the facts the inversion of its match and evaluation leaves. -/
theorem copysign_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {st st' : LState} (hvb : ValsBelow ctx st) {ii : Nat}
    {info w : IInfo} (hi : ctx.insts[ii]? = some info) {ty : Clif.Ty} {x y : Nat}
    (hic : info.clif = some (.float .fcopysign ty [x, y])) (hok : ty.isArithFloat = true)
    (hd : info.data = .data 152 2 [.data 151 121 [], .values [x, y]])
    {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 100 ≤ n2) {tr tr' : Array RuleId}
    {out w11 w9 w8 w3 w2 w1 : V} {w10 : LState × Array RuleId} {w7 w5 : LState}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w11] w10 out (st', tr'))
    (h624 : ApplyInternal p (sem ctx) cfg n2 27 624
      [w9, w8, .ty (w.resTys.head?.getD .invalid)] (w5, tr) w11 w10)
    (hva : externExtract ctx T.value_array_2 w3 st = .ok [w2, w1])
    (hi' : ctx.insts[ii]? = some w) (hw : V.data 152 2 [.data 151 121 [], w3] = w.data)
    (hpx : externCtor ctx T.put_in_reg [w2] st = .ok (w9, w7))
    (hpy : externCtor ctx T.put_in_reg [w1] w7 = .ok (w8, w5)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float .fcopysign ty [x, y]) info.results st rss st' ms := by
  obtain ⟨hwi, hw3⟩ := fdata_eq hi hd hi' hw
  subst w
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw3
  subst hw3
  rw [ext_value_array_2_iff] at hva
  simp only [List.cons.injEq, and_true] at hva
  obtain ⟨rfl, rfl⟩ := hva
  obtain ⟨rx, hrx, rfl, h7⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp hpx
  subst w7
  obtain ⟨ry, hry, rfl, h5⟩ := (ctor_put_in_reg_iff ctx _ y _ _).mp hpy
  subst w5
  have hxb := hvb x rx hrx
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
  rw [float_resTy hctx (fun cc h => by cases h) hi hic] at h624
  have hty : ty = .f32 ∨ ty = .f64 := by cases ty <;> simp_all
  obtain ⟨rfl, hs⟩ := fcopy_sign_ok hp hco hn2 hty h624
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
  simp only at hs hs3
  rw [hs] at hs3
  subst hs3
  refine ⟨_, _, ?_, rfl, lowerInstOk_fcopysign hty hR hMR hxb⟩
  simp only [LState.emit, LState.fresh]
  apply Array.ext'
  simp

section Roots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} (MR : MemRelT)
  (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR)
include hp hR hMR

set_option maxHeartbeats 8000000 in
/-- **`fcopysign` of `f32`/`f64`** (`rule_lower_685`, `lower.isle:685`, id 712): `ushr` +
`sli` (`fcopy_sign`'s scalar rule, `inst.isle:4612`). -/
theorem copysign_okT : LowerRuleOkT isem MR env cp p rule_lower_685 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, rfl, hok, hd⟩ := fcopysign_front hp hctx hi hic rfl hp.t2405
    term_2405_kind (m := m' + 9) hmatch
  have hp' := hp
  isel_inv' hp [] at hmatch heval
  have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  have h2 := ‹ApplyInternal _ _ _ _ 27 624 _ _ _ _›
  have h4 := ‹externExtract ctx T.value_array_2 _ _ = _›
  obtain ⟨ms, rss, e1, e2, e3⟩ := copysign_rhs hp' hR hMR hctx hco hvb hi hic hok hd
    (by omega) (by omega) h1 h2 h4 (by assumption) (by assumption) (by assumption)
    (by assumption)
  exact ⟨ms, e1, rss, e2, e3⟩

end Roots

/-- The `fcopysign` root is the only rule of `lower` in the family. -/
theorem lower_copysignRoot_filter :
    (program.rulesOf TId.lower).filter copysignRootRule = [rule_lower_685] := by
  rw [program_rulesOf_686]
  rfl

/-- **#35's target (`fcopysign`)**: over float-capable contexts (`CtxInvT`), the `fcopysign`
root is correct. -/
theorem lowerRulesCorrectCS_program : LowerRulesCorrectCS program := by
  intro F isem MR env cp hR hMR r hr hcs
  have hsub : r ∈ (program.rulesOf TId.lower).filter copysignRootRule :=
    List.mem_filter.2 ⟨hr, hcs⟩
  rw [lower_copysignRoot_filter, List.mem_singleton] at hsub
  subst hsub
  exact copysign_okT data_program MR env cp hR hMR

end Backend.Proof
