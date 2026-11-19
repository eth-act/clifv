import FV.Backend.Proof.IselFloatCopysign
import FV.Backend.Proof.IselFmaFamily

/-!
# #35: the scalar `fma` roots over float-capable contexts

`lower (fma ty x y z)` (`rule_lower_608`, `lower.isle:608`, id 693) is `fmadd ty x y z`, and
`lower (fma (ty_scalar_float ty) x y (fneg _ z))` (`rule_lower_609`, `lower.isle:609`, id 694,
higher priority) is `fnmsub ty x y z`. The helpers (`lower.isle:632-645`), in priority order:

* `fmadd`: rule 3 (`fneg` on `y` → `fmsub x y`), rule 2 (`fneg` on `x` → `fmsub x y`), rule 1
  (`multi_lane`: vectors), rule 0 (`ty_scalar_float` → `fpu_rrrr MAdd`);
* `fmsub`: rule 1 (`multi_lane`), rule 0 (`fpu_rrrr MSub`);
* `fnmsub`: rule 3 (`fneg` on `y` → `fnmadd`), rule 2 (`fneg` on `x` → `fnmadd`), rule 0
  (`fpu_rrrr NMSub`);
* `fnmadd`: rule 0 (`fpu_rrrr NMAdd`).

`fpu_rrrr op sz x y z` emits `FpuRRRR op sz rd x y z` (`fmadd`/`fmsub`/`fnmadd`/`fnmsub
rd, rn = x, rm = y, ra = z`), whose meaning is `fpu3Out` (`ispecFP`): `FPMulAdd` with the Arm
model's `FPNeg` on the addend (`NMAdd`, `NMSub`) and on the first multiplicand (`MSub`,
`NMAdd`). CLIF's `fma x y z` is `FPMulAdd(z, x, y)` (`Clif.FSem.fma`), `fneg` the sign flip
`IEEE.neg`, so:

* rule 0 of each helper is exact;
* an `fneg` on `x` (rule 2) or on the addend (`rule_lower_609`) is folded into the operand the
  Arm instruction negates: exact, NaN operands included;
* an `fneg` on `y` (rule 3) would be folded into a negation of `x`: the same real number, but a
  NaN operand's sign differs (`FVTest/Backend/FloatFmaWitness.lean`). Those contexts are
  excluded by `FmaNegYFree` (`Compile.fmaNegYFree`), so rule 3 never fires here;
* the vector rules (`multi_lane`) never match a scalar float type.

`fma_okT` and `fma_fneg_okT` prove the roots over `CtxInvT` contexts with `FmaNegYFree`
(`LowerRuleOkTC`), and with them the family `LowerRulesCorrectFM` (`lowerRulesCorrectFM_program`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## CLIF semantics: `fma` and `fneg` at `f32`/`f64` -/

/-- CLIF `fma` at a type: the three operands are floats of that type and the result is
`FPMulAdd(z, x, y)` rounded to nearest even. -/
theorem evalFloat_fma_inv {ty : Clif.Ty} {a b c r : Clif.Val}
    (h : Clif.evalFloat .fma ty [a, b, c] = .ok r) :
    (∃ xa xb xc : BitVec 32, ty = .f32 ∧ a = ⟨.f32, xa⟩ ∧ b = ⟨.f32, xb⟩ ∧ c = ⟨.f32, xc⟩ ∧
      r = ⟨.f32, IEEE.mulAdd .b32 .rne xc xa xb⟩) ∨
    (∃ xa xb xc : BitVec 64, ty = .f64 ∧ a = ⟨.f64, xa⟩ ∧ b = ⟨.f64, xb⟩ ∧ c = ⟨.f64, xc⟩ ∧
      r = ⟨.f64, IEEE.mulAdd .b64 .rne xc xa xb⟩) := by
  simp only [Clif.evalFloat, bind, Clif.Res.bind] at h
  cases ha : a.at ty with
  | trap _ => rw [ha] at h; cases h
  | stuck _ => rw [ha] at h; cases h
  | ok xa =>
    rw [ha] at h
    cases hb : b.at ty with
    | trap _ => rw [hb] at h; cases h
    | stuck _ => rw [hb] at h; cases h
    | ok xb =>
      rw [hb] at h
      cases hc : c.at ty with
      | trap _ => rw [hc] at h; cases h
      | stuck _ => rw [hc] at h; cases h
      | ok xc =>
        rw [hc] at h
        obtain rfl := val_at_ok ha
        obtain rfl := val_at_ok hb
        obtain rfl := val_at_ok hc
        cases ty <;>
          simp only [Clif.FSem.lift3, Clif.Res.ofOption, pure, Clif.Res.ok.injEq,
            reduceCtorEq] at h
        · exact .inl ⟨xa, xb, xc, rfl, rfl, rfl, rfl, h.symm⟩
        · exact .inr ⟨xa, xb, xc, rfl, rfl, rfl, rfl, h.symm⟩

/-- CLIF `fneg` at a type: the operand is a float of that type and the result its sign flip. -/
theorem evalFloat_fneg_inv {ty : Clif.Ty} {a r : Clif.Val}
    (h : Clif.evalFloat .fneg ty [a] = .ok r) :
    (∃ x : BitVec 32, ty = .f32 ∧ a = ⟨.f32, x⟩ ∧ r = ⟨.f32, IEEE.neg .b32 x⟩) ∨
    (∃ x : BitVec 64, ty = .f64 ∧ a = ⟨.f64, x⟩ ∧ r = ⟨.f64, IEEE.neg .b64 x⟩) := by
  simp only [Clif.evalFloat, Clif.FSem.unary, bind, Clif.Res.bind] at h
  cases ha : a.at ty with
  | trap _ => rw [ha] at h; cases h
  | stuck _ => rw [ha] at h; cases h
  | ok xa =>
    rw [ha] at h
    obtain rfl := val_at_ok ha
    cases ty <;>
      simp only [Clif.FSem.lift1, Clif.Res.ofOption, pure, Clif.Res.ok.injEq, reduceCtorEq] at h
    · exact .inl ⟨xa, rfl, rfl, h.symm⟩
    · exact .inr ⟨xa, rfl, rfl, h.symm⟩

/-- A one-result lookup (as `lookup_zip_single`, which `IselFamALUA` states). -/
theorem lookup_zip_one {l : List Nat} {a v : Clif.Val} {x : Nat}
    (h : (l.zip [a]).lookup x = some v) : v = a := by
  cases l with
  | nil => simp at h
  | cons z zs =>
    simp only [List.zip_cons_cons, List.zip_nil_right, List.lookup] at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h

theorem getMany_three {fr : Clif.Frame} {x y z : Nat} {vs : List Clif.Val}
    (h : fr.getMany [x, y, z] = .ok vs) : ∃ a b c, fr.regs x = some a ∧ fr.regs y = some b ∧
      fr.regs z = some c ∧ vs = [a, b, c] := by
  simp only [Clif.Frame.getMany, Clif.Frame.get] at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some a =>
    cases hy : fr.regs y with
    | none => rw [hx, hy] at h; cases h
    | some b =>
      cases hz : fr.regs z with
      | none => rw [hx, hy, hz] at h; cases h
      | some c =>
        rw [hx, hy, hz] at h
        exact ⟨a, b, c, rfl, rfl, rfl, (Clif.Res.ok.inj h).symm⟩

/-- An `fneg`-defined value (`def_inst` look-through, `DFGCons`): its frame value is the sign flip
of its operand's, which the frame holds. -/
theorem fneg_def_val {ctx : Ctx} {fr : Clif.Frame} (hdf : DFGCons ctx fr) {x x0 j : Nat}
    {info : IInfo} {ty : Clif.Ty} (hj : ctx.defInst? x = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.float .fneg ty [x0])) {v : Clif.Val} (hv : fr.regs x = some v) :
    ∃ a, fr.regs x0 = some a ∧ Clif.evalFloat .fneg ty [a] = .ok v := by
  obtain ⟨vals, hev, hl⟩ := hdf.1 x j info _ v hj hi hcl rfl hv
  obtain ⟨vs, r, hg, hr, rfl, -⟩ := evalInst_float_ok (hev default)
  obtain ⟨a, hx0, rfl⟩ := getMany_one hg
  obtain rfl := lookup_zip_one hl
  exact ⟨a, hx0, hr⟩

/-! ## `LowerInstOk` of the emitted `FpuRRRR` -/

/-- The scalar size of `fpu_rrrr` at a float width (`scalar_size`). -/
def fmaSize (w : Nat) : ScalarSize := if w = 32 then .size32 else .size64

/-- **`LowerInstOk` of an `fma` lowered to one `FpuRRRR`** into the fresh vreg `st.nextVreg`,
from the per-frame fact that the instruction reads defined values and computes CLIF's result. -/
theorem lowerInstOk_fpu3 {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {ty : Clif.Ty} {x y z : Nat} {o : FPUOp3} {sz : ScalarSize}
    {n m a : Nat} {cn cm ca : RegClass} {results : List Nat} {st : LState}
    (hR : Refines F isem) (hMR : MRStable F MR)
    (hsem : ∀ (fr : Clif.Frame) (cm0 : Clif.Mem) (ρ : Nat → CV) (vals : List Clif.Val)
      (cm' : Clif.Mem), ValsHeld fr ρ → DFGCons ctx fr →
      Clif.evalInst fr cm0 (.float .fma ty [x, y, z]) = .ok (vals, cm') →
      cm' = cm0 ∧ (fr.regs n).isSome ∧ (fr.regs m).isSome ∧ (fr.regs a).isSome ∧
        ∃ r w, vals = [r] ∧ fpu3Out o sz (ρ n) (ρ m) (ρ a) = some w ∧ VHolds r w) :
    LowerInstOk isem MR env cp ctx (.float .fma ty [x, y, z]) results st
      [[.vreg st.nextVreg .float]]
      ((st.fresh .float).2.emit
        (.fpuRRRR o sz (.vreg st.nextVreg .float) (.vreg n cn) (.vreg m cm) (.vreg a ca)))
      [.fpuRRRR o sz (.vreg st.nextVreg .float) (.vreg n cn) (.vreg m cm) (.vreg a ca)] := by
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    have hv : vdefs (.fpuRRRR o sz (.vreg st.nextVreg .float) (.vreg n cn) (.vreg m cm)
      (.vreg a ca)) = [st.nextVreg] := rfl
    rw [hv, List.mem_singleton] at he
    subst he
    simp [LState.emit, LState.fresh]
  · intro fr cm0 ρ vals cm' _ hvals hdf ho
    have ho' : Clif.evalInst fr cm0 (.float .fma ty [x, y, z]) = .ok (vals, cm') := ho
    obtain ⟨rfl, hn, hm, ha, r, w, rfl, hw, hrw⟩ := hsem fr cm0 ρ vals cm' hvals hdf ho'
    refine ⟨rfl, ?_, .inl (Nat.le_refl _), r, upd ρ st.nextVreg w, rfl,
      prun_cons hR rfl (outs := [w]) (fun w' => ?_) rfl (prun_nil _), ?_⟩
    · refine usesOk_of [n, m, a] ?_ (by simp [hn, hm, ha])
      intro mi hmi u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
      subst hmi
      have hu' : vuseNums (.fpuRRRR o sz (.vreg st.nextVreg .float) (.vreg n cn) (.vreg m cm)
        (.vreg a ca)) = [n, m, a] := rfl
      rw [hu'] at hu
      exact .inr hu
    · first
        | (show ispecFP (.fpuRRRR o sz (.vreg st.nextVreg .float) (.vreg n cn) (.vreg m cm)
            (.vreg a ca)) [ρ n, ρ m, ρ a] w' = _
           simp only [ispecFP, hw, Option.map_some]
           rfl)
        | (simp only [ispec, ispecFP, vuses, hw, Option.map_some]; rfl)
    · simp only [upd, ↓reduceIte]
      exact hrw

/-- `IEEE.neg` (a sign flip) is an involution. -/
theorem ieee_neg_neg (f : IEEE.Fmt) (a : IEEE.Bits f) : IEEE.neg f (IEEE.neg f a) = a := by
  simp [IEEE.neg, BitVec.xor_assoc]

/-- Whether `fpu_rrrr o` negates its first multiplicand (`rn`): `MSub`, `NMAdd`. -/
def negN : FPUOp3 → Bool
  | .mSub | .nMAdd => true
  | _ => false

/-- Whether `fpu_rrrr o` negates its addend (`ra`): `NMSub`, `NMAdd`. -/
def negA : FPUOp3 → Bool
  | .nMSub | .nMAdd => true
  | _ => false

/-- **The emitted `FpuRRRR` computes CLIF's `fma`** (`f32`): `xa`, `xb`, `xc` the operands of
CLIF's `fma`; the registers `zn`, `zm`, `za` of `rn`, `rm`, `ra` hold `xa`, `xb`, `xc`, where the
instruction negates `rn` (`negN o`) or `ra` (`negA o`) holding their negations instead. -/
theorem fma_holds32 {o : FPUOp3} {xa xb xc : BitVec 32} {zn zm za : CV}
    (hn : zn.setWidth 32 = (bif negN o then IEEE.neg .b32 xa else xa))
    (hm : zm.setWidth 32 = xb)
    (ha : za.setWidth 32 = (bif negA o then IEEE.neg .b32 xc else xc)) :
    ∃ w, fpu3Out o .size32 zn zm za = some w ∧
      VHolds ⟨.f32, IEEE.mulAdd .b32 .rne xc xa xb⟩ w := by
  refine ⟨_, rfl, ?_⟩
  show VHolds _ ((fpu3Val o .b32 (zn.setWidth 32) (zm.setWidth 32) (za.setWidth 32)).setWidth 128)
  rw [hn, hm, ha]
  have e : fpu3Val o .b32 (bif negN o then IEEE.neg .b32 xa else xa) xb
      (bif negA o then IEEE.neg .b32 xc else xc) = IEEE.mulAdd .b32 .rne xc xa xb := by
    cases o <;> simp [fpu3Val, negN, negA, ieee_neg_neg]
  rw [e]
  exact vholds_f32' _

/-- `fma_holds32` at `f64`. -/
theorem fma_holds64 {o : FPUOp3} {xa xb xc : BitVec 64} {zn zm za : CV}
    (hn : zn.setWidth 64 = (bif negN o then IEEE.neg .b64 xa else xa))
    (hm : zm.setWidth 64 = xb)
    (ha : za.setWidth 64 = (bif negA o then IEEE.neg .b64 xc else xc)) :
    ∃ w, fpu3Out o .size64 zn zm za = some w ∧
      VHolds ⟨.f64, IEEE.mulAdd .b64 .rne xc xa xb⟩ w := by
  refine ⟨_, rfl, ?_⟩
  show VHolds _ ((fpu3Val o .b64 (zn.setWidth 64) (zm.setWidth 64) (za.setWidth 64)).setWidth 128)
  rw [hn, hm, ha]
  have e : fpu3Val o .b64 (bif negN o then IEEE.neg .b64 xa else xa) xb
      (bif negA o then IEEE.neg .b64 xc else xc) = IEEE.mulAdd .b64 .rne xc xa xb := by
    cases o <;> simp [fpu3Val, negN, negA, ieee_neg_neg]
  rw [e]
  exact vholds_f64' _

/-- The register operand standing for the CLIF operand `v`: `v` itself, or (`true`) the operand
`v0` of the `fneg` defining `v`. -/
def NegSrc (ctx : Ctx) : Bool → Nat → Nat → Prop
  | true, v, v0 => ∃ j info ty, ctx.defInst? v = some j ∧ ctx.insts[j]? = some info ∧
    info.clif = some (.float .fneg ty [v0])
  | false, v, v0 => v0 = v

/-- A `NegSrc` operand at `f32`: the frame defines it and its register holds `v`'s bits, negated
if `neg`. -/
theorem negSrc_bits32 {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV} (hvals : ValsHeld fr ρ)
    (hdf : DFGCons ctx fr) {neg : Bool} {v v0 : Nat} (hs : NegSrc ctx neg v v0) {x : BitVec 32}
    (hv : fr.regs v = some ⟨.f32, x⟩) :
    (fr.regs v0).isSome ∧ (ρ v0).setWidth 32 = (bif neg then IEEE.neg .b32 x else x) := by
  cases neg
  · have hs' : v0 = v := hs
    subst hs'
    exact ⟨by simp [hv], hvals _ _ hv⟩
  · obtain ⟨j, info, ty, hj, hi, hcl⟩ := hs
    obtain ⟨a, ha, hev⟩ := fneg_def_val hdf hj hi hcl hv
    rcases evalFloat_fneg_inv hev with ⟨x0, rfl, rfl, he⟩ | ⟨x0, rfl, rfl, he⟩
    · cases he
      exact ⟨by simp [ha], by rw [Bool.cond_true, ieee_neg_neg]; exact hvals _ _ ha⟩
    · cases he

/-- `negSrc_bits32` at `f64`. -/
theorem negSrc_bits64 {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV} (hvals : ValsHeld fr ρ)
    (hdf : DFGCons ctx fr) {neg : Bool} {v v0 : Nat} (hs : NegSrc ctx neg v v0) {x : BitVec 64}
    (hv : fr.regs v = some ⟨.f64, x⟩) :
    (fr.regs v0).isSome ∧ (ρ v0).setWidth 64 = (bif neg then IEEE.neg .b64 x else x) := by
  cases neg
  · have hs' : v0 = v := hs
    subst hs'
    exact ⟨by simp [hv], hvals _ _ hv⟩
  · obtain ⟨j, info, ty, hj, hi, hcl⟩ := hs
    obtain ⟨a, ha, hev⟩ := fneg_def_val hdf hj hi hcl hv
    rcases evalFloat_fneg_inv hev with ⟨x0, rfl, rfl, he⟩ | ⟨x0, rfl, rfl, he⟩
    · cases he
    · cases he
      exact ⟨by simp [ha], by rw [Bool.cond_true, ieee_neg_neg]; exact hvals _ _ ha⟩

/-- **The frame-level fact of `lowerInstOk_fpu3`** for an `fma x y z` lowered to
`fpu_rrrr o sz n y a`, with `n` standing for `x` and `a` for `z` (`NegSrc`, negated where `o`
negates). -/
theorem fma_sem {ctx : Ctx} {ty : Clif.Ty} {o : FPUOp3} {sz : ScalarSize}
    (hsz : (ty = .f32 ∧ sz = .size32) ∨ (ty = .f64 ∧ sz = .size64)) {x y z n a : Nat}
    (hN : NegSrc ctx (negN o) x n) (hA : NegSrc ctx (negA o) z a) :
    ∀ (fr : Clif.Frame) (cm0 : Clif.Mem) (ρ : Nat → CV) (vals : List Clif.Val)
      (cm' : Clif.Mem), ValsHeld fr ρ → DFGCons ctx fr →
      Clif.evalInst fr cm0 (.float .fma ty [x, y, z]) = .ok (vals, cm') →
      cm' = cm0 ∧ (fr.regs n).isSome ∧ (fr.regs y).isSome ∧ (fr.regs a).isSome ∧
        ∃ r w, vals = [r] ∧ fpu3Out o sz (ρ n) (ρ y) (ρ a) = some w ∧ VHolds r w := by
  intro fr cm0 ρ vals cm' hvals hdf ho
  obtain ⟨vs, r, hv, hr, rfl, rfl⟩ := evalInst_float_ok ho
  obtain ⟨va, vb, vc, hxa, hyb, hzc, rfl⟩ := getMany_three hv
  rcases evalFloat_fma_inv hr with ⟨xa, xb, xc, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨xa, xb, xc, rfl, rfl, rfl, rfl, rfl⟩
  · obtain rfl : sz = .size32 := by
      rcases hsz with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    obtain ⟨hn1, hn2⟩ := negSrc_bits32 hvals hdf hN hxa
    obtain ⟨ha1, ha2⟩ := negSrc_bits32 hvals hdf hA hzc
    obtain ⟨w, hw, hrw⟩ := fma_holds32 hn2 (hvals _ _ hyb) ha2
    exact ⟨rfl, hn1, by simp [hyb], ha1, _, w, rfl, hw, hrw⟩
  · obtain rfl : sz = .size64 := by
      rcases hsz with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · exact h
    obtain ⟨hn1, hn2⟩ := negSrc_bits64 hvals hdf hN hxa
    obtain ⟨ha1, ha2⟩ := negSrc_bits64 hvals hdf hA hzc
    obtain ⟨w, hw, hrw⟩ := fma_holds64 hn2 (hvals _ _ hyb) ha2
    exact ⟨rfl, hn1, by simp [hyb], ha1, _, w, rfl, hw, hrw⟩

/-! ## Internal terms: `fpu_rrrr` and the four helpers -/

/-- The variant index of an `FPUOp3` (`inst.isle`'s order). -/
def fpuOp3Idx : FPUOp3 → Nat
  | .mAdd => 0 | .mSub => 1 | .nMAdd => 2 | .nMSub => 3

/-- What a helper of the `fma` lowering returns at a float width `w`: `fpu_rrrr o` of the
operands' registers into the fresh vreg `s.nextVreg`. -/
def Fpu3Res (ctx : Ctx) (o : FPUOp3) (w : Nat) (x y z : Nat) (s s' : LState) (v : V) : Prop :=
  ∃ rx ry rz, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧ ctx.valueReg? z = some rz ∧
    v = .reg (.vreg s.nextVreg .float) ∧
    s' = (s.fresh .float).2.emit (.fpuRRRR o (fmaSize w) (.vreg s.nextVreg .float) rx ry rz)

/-- An `fneg` look-through (`def_inst` + `inst_data_value` matching `Unary`/`Fneg`): the value
`x` is defined by an instruction whose data is `fneg x0`'s. -/
def FnegDef (ctx : Ctx) (x x0 : Nat) : Prop :=
  ∃ j info, ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧
    info.data = .data 152 29 [.data 151 119 [], .value x0]

/-- The operand of an `fneg` a `def_inst` look-through matched (`Unary`/`Fneg` data of a
float-capable context) is a value. -/
theorem fneg_data_value {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {x j : Nat}
    {info : IInfo} {w : V} (hj : ctx.defInst? x = some j) (hi : ctx.insts[j]? = some info)
    (hd : V.data 152 29 [V.data 151 119 [], w] = info.data) : ∃ x0, w = .value x0 := by
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp (hctx.defClif x j info hj hi)
  have hdat := hctx.data j info cl hi hcl
  rw [← hd] at hdat
  obtain ⟨ty, x', -, -, hfs⟩ :=
    instData_fun_inv (op := .fneg) (n := "Fneg") rfl variantNames_Fneg hdat
  simp only [List.cons.injEq, and_true] at hfs
  exact ⟨x', hfs⟩

theorem fnegDef_of {ctx : Ctx} {x x0 j : Nat} {info : IInfo} (hj : ctx.defInst? x = some j)
    (hi : ctx.insts[j]? = some info) (hd : V.data 152 29 [V.data 151 119 [], .value x0] = info.data) :
    FnegDef ctx x x0 :=
  ⟨j, info, hj, hi, hd.symm⟩

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `fpu_rrrr` (`inst.isle:2598`): `MInst.FpuRRRR` into a fresh float vreg. -/
theorem fpu_rrrr_ok {n : Nat} (hn : 40 ≤ n) {op k a b c : V} {st st' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 369 [op, k, a, b, c] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 55 [op, k, .reg rd, a, b, c]) := by
  isel_split hp hc h 369
  isel_inv [*, rule_inst_2598, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_f64_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

/-- The `FpuRRRR` an `fpu_rrrr` of size index `szIdxOf w` emitted. -/
theorem ofV_fpuRRRR {o : FPUOp3} {w : Nat} (hw : w = 32 ∨ w = 64) {rd rn rm ra : Reg}
    {m : MInst}
    (h : MInst.ofV (.data 58 55 [.data 100 (fpuOp3Idx o) [], .data 95 (szIdxOf w) [], .reg rd,
      .reg rn, .reg rm, .reg ra]) = some m) : m = .fpuRRRR o (fmaSize w) rd rn rm ra := by
  rcases hw with rfl | rfl <;> cases o <;> exact Option.some.inj (h.symm.trans rfl)

set_option maxHeartbeats 4000000 in
include hp hc in
/-- The end of a helper's scalar rule (`fpu_rrrr o (scalar_size ty) x y z`), from the facts the
inversion of its match and right-hand side leaves. -/
theorem fpu3_close {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2) {w : Nat}
    (hw : w = 32 ∨ w = 64) (o : FPUOp3) {x y z : Nat} {s s3 : LState × Array RuleId} {k : V}
    {rx ry rz : Reg} {v : V} {s' : LState} {tr' : Array RuleId}
    (h307 : ApplyInternal p (sem ctx) cfg n1 95 307 [.ty (.float w)] s k s3)
    (hrx : ctx.valueReg? x = some rx) (hry : ctx.valueReg? y = some ry)
    (hrz : ctx.valueReg? z = some rz)
    (h369 : ApplyInternal p (sem ctx) cfg n2 27 369
      [.data 100 (fpuOp3Idx o) [], k, .reg rx, .reg ry, .reg rz] (s3.1, s3.2) v (s', tr')) :
    Fpu3Res ctx o w x y z s.1 s' v := by
  obtain ⟨rfl, e1⟩ := scalar_size_float_ok hp hc hn1 hw h307
  obtain ⟨rfl, m1, hm1, hs5⟩ := fpu_rrrr_ok hp hc hn2 h369
  obtain rfl := ofV_fpuRRRR hw hm1
  simp only at hs5
  rw [e1] at hs5
  exact ⟨rx, ry, rz, hrx, hry, hrz, by rw [e1]; rfl, hs5⟩

set_option hygiene false in
/-- Close a helper's scalar rule: `fpu3_close` on the facts the inversion left. -/
macro "fpu3_rule0 " o:term:max : tactic => `(tactic| (
  obtain ⟨h307⟩ : Nonempty (ApplyInternal _ _ _ _ 95 307 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h369⟩ : Nonempty (ApplyInternal _ _ _ _ 27 369 _ _ _ _) := ⟨‹_›⟩
  exact fpu3_close hp' hc (by omega) (by omega) (by decide) $o h307 (by assumption)
    (by assumption) (by assumption) h369))

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `fmsub` (`lower.isle:640`, `645`) at `f32`/`f64`: the vector rule needs `multi_lane`; the
scalar rule is `fpu_rrrr MSub`. -/
theorem fmsub_ok {n : Nat} (hn : 100 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64) {x y z : Nat}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 695 [.ty (.float w), .value x, .value y, .value z] s v
      s') :
    Fpu3Res ctx .mSub w x y z s.1 s'.1 v := by
  have hp' := hp
  isel_split' hp hc h 695
  all_goals
    isel_inv' hp [rule_lower_645, rule_lower_640, ext_multi_lane_float, ext_ty_scalar_float_iff]
      at hm he
  all_goals try (exfalso; exact (ext_multi_lane_float _ _ _).mp ‹externExtract ctx T.multi_lane _ _ = _›)
  all_goals fpu3_rule0 .mSub

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `fnmadd` (`lower.isle:639`) at `f32`/`f64`: `fpu_rrrr NMAdd`. -/
theorem fnmadd_ok {n : Nat} (hn : 100 ≤ n) {w : Nat} (hw : w = 32 ∨ w = 64) {x y z : Nat}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 694 [.ty (.float w), .value x, .value y, .value z] s v
      s') :
    Fpu3Res ctx .nMAdd w x y z s.1 s'.1 v := by
  have hp' := hp
  isel_split' hp hc h 694
  all_goals isel_inv' hp [rule_lower_639, ext_ty_scalar_float_iff] at hm he
  all_goals fpu3_rule0 .nMAdd

set_option hygiene false in
/-- An `fneg` rule of a helper (`fneg` on the operand `v`, a `def_inst` look-through): the facts
the inversion left, the operand of the `fneg` named `x0`. -/
macro "fneg_facts " v:term:max : tactic => `(tactic| (
  obtain ⟨hdi⟩ : Nonempty (ctx.defInst? $v = some _) := ⟨‹_›⟩
  obtain ⟨hii⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 29 _ = _) := ⟨‹_›⟩
  obtain ⟨x0, rfl⟩ := fneg_data_value hctx hdi hii hdd))

set_option maxHeartbeats 8000000 in
include hp hc in
/-- `fmadd` (`lower.isle:632-644`) at `f32`/`f64`, its second operand no `fneg`: rule 2 (`fneg`
on the first operand `x = fneg x0`: `fmsub x0 y z`) or rule 0 (`fpu_rrrr MAdd`); the vector
rule needs `multi_lane`, rule 3 an `fneg` on `y`. -/
theorem fmadd_ok {f : Clif.Function} (hctx : CtxInvT f ctx) {n : Nat} (hn : 200 ≤ n) {w : Nat}
    (hw : w = 32 ∨ w = 64) {x y z : Nat} (hny : ∀ y0, ¬ FnegDef ctx y y0)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 693 [.ty (.float w), .value x, .value y, .value z] s v
      s') :
    Fpu3Res ctx .mAdd w x y z s.1 s'.1 v ∨
      ∃ x0, FnegDef ctx x x0 ∧ Fpu3Res ctx .mSub w x0 y z s.1 s'.1 v := by
  have hp' := hp
  isel_split' hp hc h 693
  all_goals
    isel_inv' hp [rule_lower_633, rule_lower_632, rule_lower_644, rule_lower_638,
      ext_multi_lane_float, ext_ty_scalar_float_iff] at hm he
  all_goals try (exfalso; exact (ext_multi_lane_float _ _ _).mp ‹externExtract ctx T.multi_lane _ _ = _›)
  all_goals
    first
      | (refine .inl ?_; fpu3_rule0 .mAdd)
      | (fneg_facts x
         obtain ⟨h695⟩ : Nonempty (ApplyInternal _ _ _ _ 27 695 _ _ _ _) := ⟨‹_›⟩
         exact .inr ⟨x0, fnegDef_of hdi hii hdd, fmsub_ok hp' hc (by omega) (by decide) h695⟩)
      | (fneg_facts y
         exact absurd (fnegDef_of hdi hii hdd) (hny x0))

set_option maxHeartbeats 8000000 in
include hp hc in
/-- `fnmsub` (`lower.isle:634-641`) at `f32`/`f64`, its second operand no `fneg`: rule 2 (`fneg`
on the first operand `x = fneg x0`: `fnmadd x0 y z`) or rule 0 (`fpu_rrrr NMSub`); rule 3
needs an `fneg` on `y`. -/
theorem fnmsub_ok {f : Clif.Function} (hctx : CtxInvT f ctx) {n : Nat} (hn : 200 ≤ n) {w : Nat}
    (hw : w = 32 ∨ w = 64) {x y z : Nat} (hny : ∀ y0, ¬ FnegDef ctx y y0)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 696 [.ty (.float w), .value x, .value y, .value z] s v
      s') :
    Fpu3Res ctx .nMSub w x y z s.1 s'.1 v ∨
      ∃ x0, FnegDef ctx x x0 ∧ Fpu3Res ctx .nMAdd w x0 y z s.1 s'.1 v := by
  have hp' := hp
  isel_split' hp hc h 696
  all_goals
    isel_inv' hp [rule_lower_635, rule_lower_634, rule_lower_641, ext_ty_scalar_float_iff] at hm he
  all_goals
    first
      | (refine .inl ?_; fpu3_rule0 .nMSub)
      | (fneg_facts x
         obtain ⟨h694⟩ : Nonempty (ApplyInternal _ _ _ _ 27 694 _ _ _ _) := ⟨‹_›⟩
         exact .inr ⟨x0, fnegDef_of hdi hii hdd, fnmadd_ok hp' hc (by omega) (by decide) h694⟩)
      | (fneg_facts y
         exact absurd (fnegDef_of hdi hii hdd) (hny x0))


end Terms

/-! ## The matched instruction -/

theorem variantNames_Fma : (variantNames 151)[118]? = some "Fma" := rfl

/-- An instruction whose opcode name is `"Fma"` is a float operation of that name. -/
theorem instNames_fma {c : Clif.Inst} {s : String} (hs : s ∈ ["Fma"])
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

/-- A matched `Ternary` of opcode `Fma` is an `fma` of three operands at `f32`/`f64`
(`instData`). -/
theorem instData_fma_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 24 (.data 151 118 [] :: fs))) :
    ∃ ty x y z, cl = .float .fma ty [x, y, z] ∧ ty.isArithFloat = true ∧
      fs = [.values [x, y, z]] := by
  obtain ⟨-, ho⟩ := instData_inv_names h
  rw [variantNames_Fma] at ho
  obtain ⟨op, ty, args, rfl, hop⟩ :=
    instNames_fma (s := "Fma") (by simp) (Option.some.inj ho).symm
  obtain rfl : op = .fma := by cases op <;> simp [fOpc] at hop <;> rfl
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, fCvtOpcode, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at h
  split at h
  · rename_i hok
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq] at h3
    exact ⟨ty, x, y, z, rfl, hok, h3.2⟩
  · simp only [reduceCtorEq] at h

/-- The instruction an `fma` root matched (`InstructionData::Ternary`, `Fma`). -/
theorem fma_front {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst) {r : Rule}
    {tyPat xPat yPat zPat : Pattern} {oT : TermId} {to : Term}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2471 [.term 151 oT [],
      .term 148 1615 [xPat, yPat, zPat]]]])
    (hto : termOf p oT = .ok to) (hko : to.kind = .enumVariant 118)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x y z, inst = .float .fma ty [x, y, z] ∧ ty.isArithFloat = true ∧
      info.data = .data 152 24 [.data 151 118 [], .values [x, y, z]] := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2471 term_2471_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨ty, x, y, z, rfl, hok, rfl⟩ := instData_fma_inv hdat
  exact ⟨ty, x, y, z, rfl, hok, hd⟩

/-- An `fneg` look-through in a float-capable context is a CLIF `fneg` of one operand. -/
theorem fnegDef_clif {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {x x0 : Nat}
    (h : FnegDef ctx x x0) : ∃ j info ty, ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧
      info.clif = some (.float .fneg ty [x0]) := by
  obtain ⟨j, info, hj, hi, hd⟩ := h
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp (hctx.defClif x j info hj hi)
  have hdat := hctx.data j info cl hi hcl
  rw [hd] at hdat
  obtain ⟨ty, x', rfl, -, hfs⟩ :=
    instData_fun_inv (op := .fneg) (n := "Fneg") rfl variantNames_Fneg hdat
  simp only [List.cons.injEq, V.value.injEq, and_true] at hfs
  subst hfs
  exact ⟨j, info, ty, hj, hi, hcl⟩

/-! ## The roots -/

/-- `FmaNegYFree` at an `fma` of the context: its second operand is no `fneg` look-through. -/
theorem fmaNegY_noFneg {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hfn : FmaNegYFree ctx) {ii : Nat} {info : IInfo} (hi : ctx.insts[ii]? = some info)
    {ty : Clif.Ty} {x y z : Nat} (hic : info.clif = some (.float .fma ty [x, y, z])) :
    ∀ y0, ¬ FnegDef ctx y y0 := by
  intro y0 hdef
  obtain ⟨j, info', ty', hj, hi', hcl⟩ := fnegDef_clif hctx hdef
  exact hfn ii info ty x y z hi hic ty' y0 (by simp [Ctx.defClif?, hj, hi', hcl])

theorem float_ty_of_arith {ty : Clif.Ty} (h : ty.isArithFloat = true) :
    (ty = .f32 ∧ CTy.ofClif ty = .float 32) ∨ (ty = .f64 ∧ CTy.ofClif ty = .float 64) := by
  cases ty <;> simp_all [CTy.ofClif]

/-- `LowerInstOk` of an `fma x y z` whose helper returned `Fpu3Res`, its operand registers
those of `n` (for `x`), `y`, `a` (for `z`). -/
theorem fma_lowerOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInvT f ctx) {ty : Clif.Ty} {w : Nat}
    (hw : (ty = .f32 ∧ w = 32) ∨ (ty = .f64 ∧ w = 64)) {o : FPUOp3} {x y z n a : Nat}
    (hN : NegSrc ctx (negN o) x n) (hA : NegSrc ctx (negA o) z a) {results : List Nat}
    {st st' : LState} {tr' : Array RuleId} {out v : V} {s5 : LState × Array RuleId}
    (hres : Fpu3Res ctx o w n y a st s5.1 v) {n1 : Nat} (hn1 : 40 ≤ n1)
    {p : Program} (hp : Data p) {cfg : Config} (hco : cfg.checkOverlap = false)
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [v] s5 out (st', tr')) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ ∃ rss, out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float .fma ty [x, y, z]) results st rss st' ms := by
  obtain ⟨rn, rm, ra, hrn, hrm, hra, rfl, hs⟩ := hres
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
  simp only at hs3
  rw [hs] at hs3
  subst hs3
  obtain rfl := hctx.valueReg n rn hrn
  obtain rfl := hctx.valueReg y rm hrm
  obtain rfl := hctx.valueReg a ra hra
  refine ⟨_, by simp [LState.emit, LState.fresh], _, rfl, lowerInstOk_fpu3 hR hMR
    (fma_sem ?_ hN hA)⟩
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- `value_array_3` on three values (as `IselCmpSelect.ext_value_array_3`). -/
theorem ext_value_array_3' (ctx : Ctx) (st : LState) (a b c : Nat) :
    externExtract ctx T.value_array_3 (.values [a, b, c]) st = .ok [.value a, .value b, .value c] :=
  rfl

/-- The instruction `inst_data_value` returned (named by its data `hw`) is the context's. -/
theorem info_of_data {ctx : Ctx} {ii : Nat} {info w : IInfo} {d : V}
    (hi : ctx.insts[ii]? = some info) (hi' : ctx.insts[ii]? = some w) (_hw : d = w.data) :
    w = info := by
  rw [hi] at hi'
  exact (Option.some.inj hi').symm

section Roots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} (MR : MemRelT)
  (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR)
include hp hR hMR

set_option maxHeartbeats 8000000 in
/-- **`fma` of `f32`/`f64`** (`rule_lower_608`, `lower.isle:608`, id 693): `fmadd` (`fpu_rrrr
MAdd`), or `fmsub` of an `fneg`'s operand; over contexts without an `fneg` second operand
(`FmaNegYFree`). -/
theorem fma_okT : LowerRuleOkTC FmaNegYFree isem MR env cp p rule_lower_608 := by
  intro f ctx hctx hfn ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 300 := ⟨n - 300, by omega⟩
  obtain ⟨ty, x, y, z, rfl, hok, hd⟩ := fma_front hp hctx hi hic rfl hp.t2402
    term_2402_kind (m := m' + 9) hmatch
  have hp' := hp
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal _ _ _ _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h693⟩ : Nonempty (ApplyInternal _ _ _ _ 27 693 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_3 _ st = _) := ⟨‹_›⟩
  obtain ⟨hw⟩ : Nonempty (V.data 152 24 _ = _) := ⟨‹_›⟩
  obtain rfl := info_of_data hi (by assumption) hw
  rw [hd] at hw
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw
  subst hw
  rw [ext_value_array_3'] at hva
  cases hva
  rw [float_resTy hctx (fun cc h => by cases h) hi hic] at h693
  have hny := fmaNegY_noFneg hctx hfn hi hic
  rcases float_ty_of_arith hok with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> rw [hc] at h693
  all_goals
    rcases fmadd_ok hp' hco hctx (by omega) (by decide) hny h693 with h | ⟨x0, hx0, h⟩
    · refine fma_lowerOk hR hMR hctx (o := .mAdd) ?_ (show x = x from rfl)
        (show z = z from rfl) h (by omega) hp' hco h172
      first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩
    · refine fma_lowerOk hR hMR hctx (o := .mSub) ?_ (fnegDef_clif hctx hx0)
        (show z = z from rfl) h (by omega) hp' hco h172
      first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`fma` of `f32`/`f64` with an `fneg` addend** (`rule_lower_609`, `lower.isle:609`,
id 694): `fnmsub` of the `fneg`'s operand (`fpu_rrrr NMSub`), or `fnmadd` of both `fneg`s'
operands; over contexts without an `fneg` second operand (`FmaNegYFree`). -/
theorem fma_fneg_okT : LowerRuleOkTC FmaNegYFree isem MR env cp p rule_lower_609 := by
  intro f ctx hctx hfn ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 300 := ⟨n - 300, by omega⟩
  obtain ⟨ty, x, y, z, rfl, hok, hd⟩ := fma_front hp hctx hi hic rfl hp.t2402
    term_2402_kind (m := m' + 9) hmatch
  have hp' := hp
  isel_inv' hp [ext_ty_scalar_float_iff] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal _ _ _ _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h696⟩ : Nonempty (ApplyInternal _ _ _ _ 27 696 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_3 _ st = _) := ⟨‹_›⟩
  obtain ⟨hdi⟩ : Nonempty (externExtract ctx T.def_inst _ st = _) := ⟨‹_›⟩
  obtain ⟨hidv⟩ : Nonempty (externExtract ctx T.inst_data_value _ st = _) := ⟨‹_›⟩
  obtain ⟨hw⟩ : Nonempty (V.data 152 24 _ = _) := ⟨‹_›⟩
  obtain rfl := info_of_data hi (by assumption) hw
  rw [hd] at hw
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw
  subst hw
  rw [ext_value_array_3'] at hva
  cases hva
  rw [ext_def_inst_iff] at hdi
  obtain ⟨j, hj, hdi⟩ := hdi
  simp only [List.cons.injEq, and_true] at hdi
  subst hdi
  rw [ext_inst_data_value_iff] at hidv
  obtain ⟨infoz, hiz, hidv⟩ := hidv
  simp only [List.cons.injEq, and_true] at hidv
  obtain ⟨-, hdz⟩ := hidv
  obtain ⟨z0, rfl⟩ := fneg_data_value hctx hj hiz hdz
  have hz0 := fnegDef_clif hctx (fnegDef_of hj hiz hdz)
  rw [float_resTy hctx (fun cc h => by cases h) hi hic] at h696
  have hny := fmaNegY_noFneg hctx hfn hi hic
  rcases float_ty_of_arith hok with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> rw [hc] at h696
  all_goals
    rcases fnmsub_ok hp' hco hctx (by omega) (by decide) hny h696 with h | ⟨x0, hx0, h⟩
    · refine fma_lowerOk hR hMR hctx (o := .nMSub) ?_ (show x = x from rfl) hz0 h
        (by omega) hp' hco h172
      first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩
    · refine fma_lowerOk hR hMR hctx (o := .nMAdd) ?_ (fnegDef_clif hctx hx0) hz0 h
        (by omega) hp' hco h172
      first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩

end Roots

/-- The `fma` roots are the only rules of `lower` in the family (`rule_lower_609` first: priority
2). -/
theorem lower_fmaRoot_filter :
    (program.rulesOf TId.lower).filter fmaRootRule = [rule_lower_609, rule_lower_608] := by
  rw [program_rulesOf_686]
  rfl

/-- **#35's target (`fma`)**: over float-capable contexts (`CtxInvT`) without an `fma` whose second
operand is an `fneg` (`FmaNegYFree`), the `fma` roots are correct. -/
theorem lowerRulesCorrectFM_program : LowerRulesCorrectFM program := by
  intro F isem MR env cp hR hMR r hr hfm
  have hsub : r ∈ (program.rulesOf TId.lower).filter fmaRootRule := List.mem_filter.2 ⟨hr, hfm⟩
  rw [lower_fmaRoot_filter] at hsub
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsub
  rcases hsub with rfl | rfl
  · exact fma_fneg_okT data_program MR env cp hR hMR
  · exact fma_okT data_program MR env cp hR hMR

end Backend.Proof
