import FV.Backend.Proof.IselFloatArith
import FV.Backend.Proof.IselCmpRoot

/-!
# S11f-cvt: float ↔ integer conversions over float-capable contexts

The `lower` roots of the float<->integer conversions cg_clif emits (`lower.isle:724-754`,
`int_to_fpu` + `put_in_reg_{s,z}ext32`: scvtf/ucvtf; `lower.isle:764-794`, `fpu_to_int_cvt_sat`:
fcvtzs/fcvtzu), proven over `CtxInvT` (`LowerRuleOkT`) against the shared IEEE core: CLIF's
`Inst.float` (`Clif.evalFloat`, `FV/Clif/FSem.lean`) and the Arm instruction the rule emits
(`ispecFP`'s `fpuToInt`/`intToFpu`, the Arm model's `exec_fp_int_cvt`) are the same `IEEE`
functions with `FPCR = 0` and rounding to nearest even, so each rule is a statement about one
function:

* `int_to_fpu` (`IntToFpu`): `fcvt_from_{s,u}int` from i8/i16/i32/i64 to f32/f64.
  The `i8`/`i16` sources go through `put_in_reg_{s,z}ext32` (sign/zero extend to 32 bits) and
  the `i32`/`i64` sources through `put_in_reg`; the rule emits `scvtf`/`ucvtf` at the
  destination's scalar size.
* `fpu_to_int_cvt_sat` (`FpuToInt`): `fcvt_to_{s,u}int_sat` from f32/f64 to i32/i64 (`fcvtzs`/
  `fcvtzu`). The `fits_in_32` result types (i8/i16) are rejected by `instData`'s `fCvtTyOk`
  (`cg_clif` lowers them to the `.i32` conversion + an integer clamp), so only the `.i32` and
  `.i64` roots can fire.

Trapping `fcvt_to_{s,u}int` is not emitted by cg_clif (its `cast.rs` never requests the
trapping variants) and its roots are not in the closure; we document that here.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Internal terms: `int_to_fpu`, `fpu_to_int_cvt_sat` -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `int_to_fpu` (`inst.isle:4758`): `MInst.IntToFpu` into a fresh float vreg
(`temp_writable_reg $I8X16`). -/
theorem intToFpu_ok {n : Nat} (hn : 40 ≤ n) {op a : V} {st st' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 633 [op, a] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 70 [op, .reg rd, a]) := by
  isel_split hp hc h 633
  isel_inv [*, rule_inst_4758, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `fpu_to_int` (`inst.isle:4750`): `MInst.FpuToInt` into a fresh int vreg
(`temp_writable_reg $I64`). -/
theorem fpuToInt_ok {n : Nat} (hn : 40 ≤ n) {op a : V} {st st' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 632 [op, a] st v st') :
    EmitOutC .int st.1 st'.1 v (fun rd => .data 58 69 [op, .reg rd, a]) := by
  isel_split hp hc h 632
  isel_inv [*, rule_inst_4750, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  exact ⟨rfl, _, ‹_›, rfl⟩

theorem ext_fits_in_16_64 (ctx : Ctx) (st : LState) :
    externExtract ctx T.fits_in_16 (.ty (.int 64)) st = .fail := by
  rw [ext_fits_in_16]; rfl

theorem ext_fits_in_16_32 (ctx : Ctx) (st : LState) :
    externExtract ctx T.fits_in_16 (.ty (.int 32)) st = .fail := by
  rw [ext_fits_in_16]; rfl

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `fpu_to_int_cvt_sat` (`inst.isle:4716-4718`) at an `i32`/`i64` result: `fpu_to_int`
(the `fits_in_16` clamping rules do not match). -/
theorem fpuToIntSat_ok {n : Nat} (hn : 60 ≤ n) {op a s : V} {t : CTy}
    (ht : t = .int 64 ∨ t = .int 32) {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 629 [op, a, s, .ty t] st v st') :
    EmitOutC .int st.1 st'.1 v (fun rd => .data 58 69 [op, .reg rd, a]) := by
  have hp' := hp
  rcases ht with rfl | rfl
  all_goals isel_split hp hc h 629
  all_goals isel_inv [*, rule_inst_4716, rule_inst_4718, rule_inst_4720, rule_inst_4726,
    ext_fits_in_16_64, ext_fits_in_16_32] at hm he
  all_goals first
    | exact absurd ‹CTy.int 64 = CTy.int 32› (by decide)
    | exact absurd ‹CTy.int 32 = CTy.int 64› (by decide)
    | exact absurd ‹(CTy.int 64).bits ≤ 16› (by decide)
    | exact absurd ‹(CTy.int 32).bits ≤ 16› (by decide)
    | (have h632 := ‹ApplyInternal _ _ _ _ 27 632 _ _ _ _›
       exact fpuToInt_ok hp' hc (by omega) h632)

end Terms


/-! ## The matched instruction -/

theorem variantNames_FcvtToUintSat : (variantNames 151)[149]? = some "FcvtToUintSat" := rfl
theorem variantNames_FcvtToSintSat : (variantNames 151)[150]? = some "FcvtToSintSat" := rfl
theorem variantNames_FcvtFromUint : (variantNames 151)[152]? = some "FcvtFromUint" := rfl
theorem variantNames_FcvtFromSint : (variantNames 151)[153]? = some "FcvtFromSint" := rfl

/-- The opcode names of the conversions `instData` builds (`fCvtOpcode`). -/
def fCvtNames : List String := ["FcvtFromUint", "FcvtFromSint", "FcvtToUintSat", "FcvtToSintSat"]

/-- An instruction whose opcode name is a conversion's is that float operation. -/
theorem instNames_fcvt {c : Clif.Inst} {s : String} (hs : s ∈ fCvtNames)
    (h : (instNames c).2 = s) : ∃ op ty args, c = .float op ty args ∧ fOpc op = s := by
  cases c
  case float op ty args => exact ⟨op, ty, args, rfl, h⟩
  all_goals exfalso
  all_goals subst h
  all_goals simp only [instNames, fCvtNames] at hs
  all_goals first
    | (simp at hs; done)
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at hs; done)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at hs; done)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at hs; done)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at hs; done)

/-- A matched `Unary` of a conversion opcode `n` is the conversion named `n`, at a type
`instData` admits (`fCvtTyOk`). -/
theorem instData_cvt_inv {f : Clif.Function} {cl : Clif.Inst} {ko : Nat} {fs : List V}
    {op : Clif.FOp} {n : String} (hop : fCvtOpcode op = some n)
    (hko : (variantNames 151)[ko]? = some n)
    (h : instData f cl = .ok (.data 152 29 (.data 151 ko [] :: fs))) :
    ∃ ty x, cl = .float op ty [x] ∧ fCvtTyOk op ty = true ∧ fs = [.value x] := by
  obtain ⟨-, ho⟩ := instData_inv_names h
  rw [hko] at ho
  have hn : n ∈ fCvtNames := by
    cases op <;> simp [fCvtOpcode] at hop <;> subst hop <;> decide
  obtain ⟨op', ty, args, rfl, hop'⟩ := instNames_fcvt hn (Option.some.inj ho).symm
  obtain rfl : op' = op := by
    cases op <;> simp [fCvtOpcode] at hop <;> subst hop <;> cases op' <;> simp [fOpc] at hop' <;>
      rfl
  cases op' <;> simp [fCvtOpcode] at hop <;> subst hop <;>
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, fCvtOpcode, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at h
  all_goals
    split at h
    · rename_i hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨ty, x, rfl, hok, h3.2⟩
    · simp only [reduceCtorEq] at h

/-- The instruction a conversion root matched (`InstructionData::Unary`). -/
theorem cvt_front {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst) {r : Rule}
    {tyPat xPat : Pattern} {oT : TermId} {to : Term} {ko : Nat} {op : Clif.FOp} {n : String}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 [.term 151 oT [], xPat]]])
    (hto : termOf p oT = .ok to) (hko : to.kind = .enumVariant ko)
    (hop : fCvtOpcode op = some n) (hn : (variantNames 151)[ko]? = some n)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x, inst = .float op ty [x] ∧ fCvtTyOk op ty = true ∧
      info.data = .data 152 29 [.data 151 ko [], .value x] := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2476 term_2476_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨ty, x, rfl, hok, rfl⟩ := instData_cvt_inv hop hn hdat
  exact ⟨ty, x, rfl, hok, hd⟩

/-! ## CLIF semantics of the conversions -/

theorem ofClif_inj {a b : Clif.Ty} (h : CTy.ofClif a = CTy.ofClif b) : a = b := by
  cases a <;> cases b <;> simp [CTy.ofClif] at h ⊢

/-- An integer type of `mCTys` is an `eCTys` type. -/
theorem ofClif_int_eCTys {a : Clif.Ty} (hm : CTy.ofClif a ∈ mCTys) (hi : a.isInt = true) :
    CTy.ofClif a ∈ eCTys := by
  cases a <;> simp_all [mCTys, eCTys, CTy.ofClif, Clif.Ty.isInt]

/-- The `fcvtzs`/`fcvtzu` of a saturating conversion to `ty` from a float of type `tx`. -/
def toIntOpAt : Clif.FOp → Clif.Ty → Clif.Ty → Option FpuToIntOp
  | .fcvtToUintSat, .i32, .f32 => some .f32ToU32
  | .fcvtToSintSat, .i32, .f32 => some .f32ToI32
  | .fcvtToUintSat, .i64, .f32 => some .f32ToU64
  | .fcvtToSintSat, .i64, .f32 => some .f32ToI64
  | .fcvtToUintSat, .i32, .f64 => some .f64ToU32
  | .fcvtToSintSat, .i32, .f64 => some .f64ToI32
  | .fcvtToUintSat, .i64, .f64 => some .f64ToU64
  | .fcvtToSintSat, .i64, .f64 => some .f64ToI64
  | _, _, _ => none

/-- The `scvtf`/`ucvtf` of a conversion to the float type `ty` from a 32-bit (`false`) or
64-bit (`true`) integer register. -/
def fromIntOpAt : Clif.FOp → Clif.Ty → Bool → Option IntToFpuOp
  | .fcvtFromUint, .f32, false => some .u32ToF32
  | .fcvtFromSint, .f32, false => some .i32ToF32
  | .fcvtFromUint, .f64, false => some .u32ToF64
  | .fcvtFromSint, .f64, false => some .i32ToF64
  | .fcvtFromUint, .f32, true => some .u64ToF32
  | .fcvtFromSint, .f32, true => some .i64ToF32
  | .fcvtFromUint, .f64, true => some .u64ToF64
  | .fcvtFromSint, .f64, true => some .i64ToF64
  | _, _, _ => none

/-- The extension of a narrow `fcvt_from_*` operand: `put_in_reg_sext32` for the signed one. -/
def cvtSigned : Clif.FOp → Bool
  | .fcvtFromSint => true
  | _ => false

theorem vholds_x32 (y : BitVec 32) : VHolds ⟨.i32, y⟩ (ofX (y.setWidth 64)) := by
  show ((y.setWidth 64).setWidth 128).setWidth 32 = y
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ (by omega),
    BitVec.setWidth_eq]

theorem vholds_x64 (y : BitVec 64) : VHolds ⟨.i64, y⟩ (ofX y) := by
  show (y.setWidth 128).setWidth 64 = y
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

/-- `FixedToFP` of a zero-extended operand: the unsigned value is unchanged. -/
theorem fromFixed_setWidth {f : IEEE.Fmt} {w : Nat} (x : BitVec w) (hw : w ≤ 32) (rm : IEEE.RMode) :
    IEEE.fromFixed f 32 (x.setWidth 32) true rm = IEEE.fromFixed f w x true rm := by
  have h : (x.setWidth 32).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hw))
  simp only [IEEE.fromFixed, h, ↓reduceIte]

/-- `FixedToFP` of a sign-extended operand: the signed value is unchanged. -/
theorem fromFixed_signExtend {f : IEEE.Fmt} {w : Nat} (x : BitVec w) (hw : w ≤ 32)
    (rm : IEEE.RMode) :
    IEEE.fromFixed f 32 (x.signExtend 32) false rm = IEEE.fromFixed f w x false rm := by
  simp only [IEEE.fromFixed, BitVec.toInt_signExtend_of_le hw, Bool.false_eq_true, ↓reduceIte]

theorem fop_beq :
    (Clif.FOp.fcvtFromUint == .fcvtFromUint) = true ∧ (Clif.FOp.fcvtFromSint == .fcvtFromUint) = false ∧
      (Clif.FOp.fcvtToUintSat == .fcvtToUintSat) = true ∧
      (Clif.FOp.fcvtToSintSat == .fcvtToUintSat) = false := by decide

/-- Only the saturating conversions have an `FpuToIntOp`. -/
theorem toIntOpAt_ne {op : Clif.FOp} {ty tx : Clif.Ty} {o : FpuToIntOp}
    (h : toIntOpAt op ty tx = some o) : op = .fcvtToUintSat ∨ op = .fcvtToSintSat := by
  cases op <;> first | (left; rfl) | (right; rfl) | (cases ty <;> cases tx <;> simp [toIntOpAt] at h)

/-- Only the conversions from integers have an `IntToFpuOp`. -/
theorem fromIntOpAt_ne {op : Clif.FOp} {ty : Clif.Ty} {b : Bool} {o : IntToFpuOp}
    (h : fromIntOpAt op ty b = some o) : op = .fcvtFromUint ∨ op = .fcvtFromSint := by
  cases op <;> first | (left; rfl) | (right; rfl) | (cases ty <;> cases b <;> simp [fromIntOpAt] at h)

set_option maxHeartbeats 4000000 in
/-- **A saturating conversion is the `FpuToInt` the rule emits**: on a register value holding
the float operand, `fpuToIntVal` holds CLIF's result. -/
theorem toSat_holds {op : Clif.FOp} {ty tx : Clif.Ty} {fop : FpuToIntOp}
    (hat : toIntOpAt op ty tx = some fop) {a r : Clif.Val} {za : CV} (hty : a.ty = tx)
    (ha : VHolds a za) (h : Clif.evalFloat op ty [a] = .ok r) : VHolds r (fpuToIntVal fop za) := by
  obtain ⟨aty, ab⟩ := a
  simp only at hty
  subst hty
  rcases toIntOpAt_ne hat with rfl | rfl
  all_goals
    cases ty <;> cases aty <;> simp only [toIntOpAt, Option.some.injEq, reduceCtorEq] at hat <;>
      subst hat
  all_goals
    have ha' : za.setWidth _ = ab := ha
    subst ha'
    simp only [Clif.evalFloat, Clif.Ty.isInt, ↓reduceIte, Clif.FSem.toIntSat, Clif.Res.ofOption,
      bind, Clif.Res.bind, pure, Clif.Res.ok.injEq, fop_beq, Clif.Ty.width] at h
    subst h
    first | exact vholds_x32 _ | exact vholds_x64 _

set_option maxHeartbeats 4000000 in
/-- **A conversion from a 64-bit integer is the `IntToFpu` the rule emits.** -/
theorem from64_holds {op : Clif.FOp} {ty : Clif.Ty} {iop : IntToFpuOp}
    (hat : fromIntOpAt op ty true = some iop) {a r : Clif.Val} {za : CV} (hty : a.ty = .i64)
    (ha : VHolds a za) (h : Clif.evalFloat op ty [a] = .ok r) : VHolds r (intToFpuVal iop za) := by
  obtain ⟨aty, ab⟩ := a
  simp only at hty
  subst hty
  have ha' : lo64 za = ab := ha
  subst ha'
  rcases fromIntOpAt_ne hat with rfl | rfl
  all_goals
    cases ty <;> simp only [fromIntOpAt, Option.some.injEq, reduceCtorEq] at hat <;> subst hat
  all_goals
    simp only [Clif.evalFloat, Clif.Ty.isInt, ↓reduceIte, Clif.FSem.fromInt, Clif.Res.ofOption,
      bind, Clif.Res.bind, pure, Clif.Res.ok.injEq, fop_beq, Clif.Ty.width] at h
    subst h
    first | exact vholds_f32' _ | exact vholds_f64' _

set_option maxHeartbeats 4000000 in
/-- **A conversion from an integer of at most 32 bits is the `IntToFpu` the rule emits**, on
the register `put_in_reg_{z,s}ext32` returned (`ExtHolds`). -/
theorem small_holds {op : Clif.FOp} {ty : Clif.Ty} {iop : IntToFpuOp}
    (hat : fromIntOpAt op ty false = some iop) {a r : Clif.Val} {z : CV} (hw : a.ty.width ≤ 32)
    (hext : ExtHolds (cvtSigned op) 32 a z) (h : Clif.evalFloat op ty [a] = .ok r) :
    VHolds r (intToFpuVal iop z) := by
  obtain ⟨aty, ab⟩ := a
  have he := hext.2 hw
  rcases fromIntOpAt_ne hat with rfl | rfl
  all_goals
    cases ty <;> simp only [fromIntOpAt, Option.some.injEq, reduceCtorEq] at hat <;> subst hat
  all_goals
    simp only [cvtSigned, Bool.false_eq_true, ↓reduceIte] at he
    simp only [Clif.evalFloat] at h
    split at h
    · simp only [Clif.FSem.fromInt, Clif.Res.ofOption, bind, Clif.Res.bind, pure,
        Clif.Res.ok.injEq, fop_beq] at h
      subst h
      simp only [intToFpuVal]
      rw [he]
      first
        | (rw [fromFixed_setWidth ab hw]; first | exact vholds_f32' _ | exact vholds_f64' _)
        | (rw [fromFixed_signExtend ab hw]; first | exact vholds_f32' _ | exact vholds_f64' _)
    · simp at h

/-- A conversion from an integer evaluates only on an integer operand. -/
theorem cvtFrom_isInt {op : Clif.FOp} {ty : Clif.Ty} {b : Bool} {iop : IntToFpuOp}
    (hat : fromIntOpAt op ty b = some iop) {a r : Clif.Val}
    (h : Clif.evalFloat op ty [a] = .ok r) : a.ty.isInt = true := by
  rcases fromIntOpAt_ne hat with rfl | rfl
  all_goals
    simp only [Clif.evalFloat] at h
    split at h
    · assumption
    · simp at h

/-! ## `LowerInstOk` of the emitted code -/

/-- **`LowerInstOk` of a conversion lowered to one instruction** `mi` defining the fresh vreg
`st.nextVreg` from the operand's vreg, of value `g` on it. -/
theorem lowerInstOk_cvt1 {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {op : Clif.FOp} {ty tx : Clif.Ty} {x : Nat}
    {results : List Nat} {st : LState} {mi : MInst} {c cx : RegClass} {g : CV → CV}
    (hR : Refines F isem) (hMR : MRStable F MR) (hT : ctx.valueType? x = some (CTy.ofClif tx))
    (hops : mi.operands = .ok #[⟨st.nextVreg, c, .def, .late, .reg⟩, ⟨x, cx, .use, .early, .reg⟩])
    (hvd : vdefs mi = [st.nextVreg]) (hvu : vuseNums mi = [x])
    (hs : ∀ a w, ispec mi [a] w = some ([g a], w, .next))
    (hsem : ∀ (a r : Clif.Val) (za : CV), a.ty = tx → VHolds a za →
      Clif.evalFloat op ty [a] = .ok r → VHolds r (g za)) :
    LowerInstOk isem MR env cp ctx (.float op ty [x]) results st [[.vreg st.nextVreg c]]
      ((st.fresh c).2.emit mi) [mi] := by
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro m hm e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    subst hm
    rw [hvd, List.mem_singleton] at he
    subst he
    simp [LState.emit, LState.fresh]
  · intro fr cm ρ vals cm' _ hvals hdfg ho
    have ho' : Clif.evalInst fr cm (.float op ty [x]) = .ok (vals, cm') := ho
    obtain ⟨vs, r, hv, hr, rfl, rfl⟩ := evalInst_float_ok ho'
    obtain ⟨a, hx, rfl⟩ := getMany_one hv
    have hty : a.ty = tx := ofClif_inj (hdfg.2 x _ a hT hx)
    refine ⟨rfl, ?_, .inl (Nat.le_refl _), r, upd ρ st.nextVreg (g (ρ x)), rfl,
      prun_rr_c hR hops (hs (ρ x)) (prun_nil _), ?_⟩
    · refine usesOk_of [x] ?_ (by simp [hx])
      intro m hm u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      subst hm
      rw [hvu] at hu
      exact .inr hu
    · simp only [upd, ↓reduceIte]
      exact hsem a r (ρ x) hty (hvals x a hx) hr

/-- A fragment that allocated one fresh float vreg and emitted `m` defining only it. -/
theorem Frag.fresh_emit_f (s : LState) {m : MInst} (hd : vdefs m ⊆ [s.nextVreg]) :
    Frag s ((s.fresh .float).2.emit m) [m] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LState.emit, LState.fresh]
  · simp [LState.emit, LState.fresh]
  · intro m' hm' d hd'
    simp only [List.mem_singleton] at hm'
    subst hm'
    have := hd hd'
    simp only [List.mem_singleton] at this
    simp [LState.emit, LState.fresh, this]

set_option maxHeartbeats 2000000 in
/-- **`LowerInstOk` of a conversion from an integer of at most 32 bits**: the code of
`put_in_reg_{z,s}ext32` (`ExtOut`), then `scvtf`/`ucvtf` into a fresh float vreg. -/
theorem lowerInstOk_cvtSmall {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx} (hR : Refines F isem)
    (hMR : MRStable F MR) (hctx : CtxInvT f ctx) {x : Nat} {t : CTy}
    (ht : ctx.valueType? x = some t) (hb : t.bits ≤ 32) {op : Clif.FOp} {ty : Clif.Ty}
    {iop : IntToFpuOp} {results : List Nat} {st s1 : LState} {r : Reg}
    (hE : ExtOut ctx x (cvtSigned op) 32 [.int 32, .int 64] st s1 (.reg r))
    (hvb : ValsBelow ctx st) (hat : fromIntOpAt op ty false = some iop) :
    ∃ ms, ((s1.fresh .float).2.emit (.intToFpu iop (.vreg s1.nextVreg .float) r)).emitted =
        st.emitted ++ ms.toArray ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) results st [[.vreg s1.nextVreg .float]]
        ((s1.fresh .float).2.emit (.intToFpu iop (.vreg s1.nextVreg .float) r)) ms := by
  by_cases htE : t ∈ eCTys
  · have hxi : IntPos ctx x := fun t' h' => by rw [ht] at h'; cases h'; exact htE
    obtain ⟨k, ms, hv, hfr, hk, hk', hrun⟩ :=
      ExtOut.semT hR hctx hxi hvb (.inl rfl) (by simp) (by simp) hE
    simp only [V.reg.injEq] at hv
    subst hv
    have hf2 : Frag s1 ((s1.fresh .float).2.emit
        (.intToFpu iop (.vreg s1.nextVreg .float) (.vreg k .int)))
        [.intToFpu iop (.vreg s1.nextVreg .float) (.vreg k .int)] :=
      Frag.fresh_emit_f s1 (fun d hd => by
        rwa [show vdefs (MInst.intToFpu iop (.vreg s1.nextVreg .float) (.vreg k .int)) =
          [s1.nextVreg] from rfl] at hd)
    have hF := hfr.append hf2
    refine ⟨_, hF.emitted, lowerInstOk_runs_c hMR hF.mono hF.defs rfl ?_⟩
    intro fr cm ρ w vals cm' _ hvals hdfg ho
    have ho' : Clif.evalInst fr cm (.float op ty [x]) = .ok (vals, cm') := ho
    obtain ⟨vs, rv, hvs, hr, rfl, rfl⟩ := evalInst_float_ok ho'
    obtain ⟨a, hx, rfl⟩ := getMany_one hvs
    have hty := hdfg.2 x t a ht hx
    subst hty
    have hw : a.ty.width ≤ 32 := by rw [← ofClif_bits]; exact hb
    obtain ⟨hU, hRun⟩ := hrun fr ρ a (hvals x a hx) hdfg hx
    refine ⟨rfl, ?_, .inl hfr.mono, rv, rfl, Runs.append (hRun w) fun ρ1 w1 h1 => ?_⟩
    · intro m hm u hu
      rcases List.mem_append.1 hm with hm | hm
      · exact hU m hm u hu
      · simp only [List.mem_singleton] at hm
        subst hm
        have hu' : vuseNums (.intToFpu iop (.vreg s1.nextVreg .float) (.vreg k .int)) = [k] := rfl
        rw [hu', List.mem_singleton] at hu
        subst hu
        rcases hk' with h | rfl
        · exact .inl h
        · exact .inr (by simp [hx])
    · refine Runs.one hR rfl rfl rfl (SameWorldNF.refl F w1) fun _ _ => ?_
      show VHolds rv (upd ρ1 s1.nextVreg (intToFpuVal iop (ρ1 k)) s1.nextVreg)
      simp only [upd, ↓reduceIte]
      exact small_holds hat hw h1 hr
  · obtain ⟨t2, hT2, rx, hx, hc⟩ := hE
    rw [ht] at hT2
    cases hT2
    rcases hc with ⟨hpass, -, -⟩ | ⟨-, -, hv, hs⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpass
      rcases hpass with rfl | rfl <;> simp [eCTys] at htE
    · simp only [V.reg.injEq] at hv
      subst hv
      subst hs
      obtain rfl := hctx.valueReg x rx hx
      have hf1 := Frag.fresh_emit st
        (m := .extend (.vreg st.nextVreg .int) (.vreg x (valClassOf ctx x)) (cvtSigned op) t.bits 32)
        (fun d hd => by
          rwa [show vdefs (MInst.extend (.vreg st.nextVreg .int) (.vreg x (valClassOf ctx x))
            (cvtSigned op) t.bits 32) = [st.nextVreg] from rfl] at hd)
      have hf2 : Frag ((st.fresh .int).2.emit
          (.extend (.vreg st.nextVreg .int) (.vreg x (valClassOf ctx x)) (cvtSigned op) t.bits 32))
          ((((st.fresh .int).2.emit (.extend (.vreg st.nextVreg .int) (.vreg x (valClassOf ctx x))
            (cvtSigned op) t.bits 32)).fresh .float).2.emit
            (.intToFpu iop (.vreg (((st.fresh .int).2.emit (.extend (.vreg st.nextVreg .int)
              (.vreg x (valClassOf ctx x)) (cvtSigned op) t.bits 32)).nextVreg) .float)
              (.vreg st.nextVreg .int)))
          [.intToFpu iop (.vreg (((st.fresh .int).2.emit (.extend (.vreg st.nextVreg .int)
              (.vreg x (valClassOf ctx x)) (cvtSigned op) t.bits 32)).nextVreg) .float)
              (.vreg st.nextVreg .int)] :=
        Frag.fresh_emit_f _ (fun d hd => by
          rwa [show vdefs (MInst.intToFpu iop (.vreg (((st.fresh .int).2.emit (.extend
            (.vreg st.nextVreg .int) (.vreg x (valClassOf ctx x)) (cvtSigned op) t.bits 32)).nextVreg)
            .float) (.vreg st.nextVreg .int)) = [_] from rfl] at hd)
      have hF := hf1.append hf2
      refine ⟨_, hF.emitted, lowerInstOk_runs_c hMR hF.mono hF.defs rfl ?_⟩
      intro fr cm ρ w vals cm' _ _ hdfg ho
      exfalso
      have ho' : Clif.evalInst fr cm (.float op ty [x]) = .ok (vals, cm') := ho
      obtain ⟨vs, rv, hvs, hr, rfl, rfl⟩ := evalInst_float_ok ho'
      obtain ⟨a, hxa, rfl⟩ := getMany_one hvs
      have hI := cvtFrom_isInt hat hr
      have hty := hdfg.2 x t a ht hxa
      subst hty
      exact htE (ofClif_int_eCTys (hctx.valTyM x _ ht) hI)

/-! ## The right-hand sides -/

/-- The variant index of an `IntToFpuOp` (`inst.isle`'s order). -/
def intToFpuIdx : IntToFpuOp → Nat
  | .u32ToF32 => 0 | .i32ToF32 => 1 | .u32ToF64 => 2 | .i32ToF64 => 3
  | .u64ToF32 => 4 | .i64ToF32 => 5 | .u64ToF64 => 6 | .i64ToF64 => 7

/-- The variant index of an `FpuToIntOp` (`inst.isle`'s order). -/
def fpuToIntIdx : FpuToIntOp → Nat
  | .f32ToU32 => 0 | .f32ToI32 => 1 | .f32ToU64 => 2 | .f32ToI64 => 3
  | .f64ToU32 => 4 | .f64ToI32 => 5 | .f64ToU64 => 6 | .f64ToI64 => 7

theorem ofV_intToFpu {iop : IntToFpuOp} {rd rn : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 70 [.data 102 (intToFpuIdx iop) [], .reg rd, .reg rn]) = some m) :
    m = .intToFpu iop rd rn := by
  cases iop <;> exact Option.some.inj (h.symm.trans rfl)

theorem ofV_fpuToInt {fop : FpuToIntOp} {rd rn : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 69 [.data 101 (fpuToIntIdx fop) [], .reg rd, .reg rn]) = some m) :
    m = .fpuToInt fop rd rn := by
  cases fop <;> exact Option.some.inj (h.symm.trans rfl)

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of a conversion from `i64`** (`output_reg (int_to_fpu op x)`). -/
theorem cvt_from64_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {op : Clif.FOp} {ty : Clif.Ty} {x : Nat}
    {results : List Nat} {iop : IntToFpuOp} (hat : fromIntOpAt op ty true = some iop)
    {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2) {st st' : LState} {tr tr' : Array RuleId}
    {out w5 w3 : V} {w4 : LState × Array RuleId} {w2 : LState}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w5] w4 out (st', tr'))
    (h633 : ApplyInternal p (sem ctx) cfg n2 27 633 [.data 102 (intToFpuIdx iop) [], w3] (w2, tr)
      w5 w4)
    (hvt : externExtract ctx T.value_type (.value x) st = .ok [.ty (.int 64)])
    (hpx : externCtor ctx T.put_in_reg [.value x] st = .ok (w3, w2)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) results st rss st' ms := by
  obtain ⟨t, ht, htw⟩ := (ext_value_type_iff ctx _ x _).mp hvt
  simp only [List.cons.injEq, V.ty.injEq, and_true] at htw
  subst htw
  obtain ⟨rx, hrx, rfl, rfl⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp hpx
  have hpos : IntPos ctx x := fun t' ht' => by rw [ht] at ht'; cases ht'; simp [eCTys]
  obtain rfl := hctx.valueReg_int hrx hpos
  obtain ⟨rfl, m1, hm1, hs2⟩ := intToFpu_ok hp hco hn2 h633
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
  simp only at hs2 hs3 hm1
  rw [hs2] at hs3
  subst hs3
  obtain rfl := ofV_intToFpu hm1
  exact ⟨_, _, by simp [LState.emit, LState.fresh], rfl,
    lowerInstOk_cvt1 (tx := .i64) hR hMR ht rfl rfl rfl (fun _ _ => rfl)
      (fun a r za hty ha h => from64_holds hat hty ha h)⟩

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of a conversion from an integer of at most 32 bits**
(`output_reg (int_to_fpu op (put_in_reg_{z,s}ext32 x))`). -/
theorem cvt_small_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {op : Clif.FOp} {ty : Clif.Ty} {x : Nat}
    {results : List Nat} {iop : IntToFpuOp} (hat : fromIntOpAt op ty false = some iop)
    {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2) {st st' : LState} {tr' : Array RuleId}
    (hvb : ValsBelow ctx st) {out w7 w5 w2 w1 : V} {w6 w4 : LState × Array RuleId}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w7] w6 out (st', tr'))
    (h633 : ApplyInternal p (sem ctx) cfg n2 27 633 [.data 102 (intToFpuIdx iop) [], w5] w4 w7 w6)
    (hvt : externExtract ctx T.value_type (.value x) st = .ok [w2])
    (hfit : externExtract ctx T.fits_in_32 w2 st = .ok [w1])
    (hE : ExtOut ctx x (cvtSigned op) 32 [.int 32, .int 64] st w4.1 w5) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) results st rss st' ms := by
  obtain ⟨t, ht, htw⟩ := (ext_value_type_iff ctx _ x _).mp hvt
  simp only [List.cons.injEq, and_true] at htw
  subst htw
  obtain ⟨hb, -⟩ := (ext_fits_in_32_iff ctx _ t _).mp hfit
  obtain ⟨r, rfl⟩ : ∃ r, w5 = .reg r := by
    obtain ⟨_, _, _, _, h | h⟩ := hE
    · exact ⟨_, h.2.1⟩
    · exact ⟨_, h.2.2.1⟩
  obtain ⟨w4s, w4t⟩ := w4
  obtain ⟨rfl, m1, hm1, hs2⟩ := intToFpu_ok hp hco hn2 h633
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
  simp only at hs2 hs3 hm1 hE
  rw [hs2] at hs3
  subst hs3
  obtain rfl := ofV_intToFpu hm1
  obtain ⟨ms, e, hL⟩ := lowerInstOk_cvtSmall (results := results) hR hMR hctx ht hb hE hvb hat
  exact ⟨ms, _, e, rfl, hL⟩

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of a saturating conversion to `i32`/`i64`**
(`output_reg (fpu_to_int_cvt_sat op x signed ty)`). -/
theorem cvt_toSat_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {op : Clif.FOp} {ty tx : Clif.Ty} {x : Nat}
    {results : List Nat} {fop : FpuToIntOp} (hat : toIntOpAt op ty tx = some fop) {Tt : CTy}
    (hT : Tt = .int 64 ∨ Tt = .int 32) {sg : Bool}
    {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 60 ≤ n2) {st st' : LState} {tr tr' : Array RuleId}
    {out w5 w3 : V} {w4 : LState × Array RuleId} {w2 : LState}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w5] w4 out (st', tr'))
    (h629 : ApplyInternal p (sem ctx) cfg n2 27 629
      [.data 101 (fpuToIntIdx fop) [], w3, .bool sg, .ty Tt] (w2, tr) w5 w4)
    (hvt : externExtract ctx T.value_type (.value x) st = .ok [.ty (CTy.ofClif tx)])
    (hpx : externCtor ctx T.put_in_reg [.value x] st = .ok (w3, w2)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) results st rss st' ms := by
  obtain ⟨t, ht, htw⟩ := (ext_value_type_iff ctx _ x _).mp hvt
  simp only [List.cons.injEq, V.ty.injEq, and_true] at htw
  subst htw
  obtain ⟨rx, hrx, rfl, rfl⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp hpx
  obtain rfl := hctx.valueReg x rx hrx
  obtain ⟨rfl, m1, hm1, hs2⟩ := fpuToIntSat_ok hp hco hn2 hT h629
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
  simp only at hs2 hs3 hm1
  rw [hs2] at hs3
  subst hs3
  obtain rfl := ofV_fpuToInt hm1
  exact ⟨_, _, by simp [LState.emit, LState.fresh], rfl,
    lowerInstOk_cvt1 hR hMR ht rfl rfl rfl (fun _ _ => rfl)
      (fun a r za hty ha h => toSat_holds hat hty ha h)⟩

/-! ## The 16 roots -/

set_option hygiene false in
/-- The common start of a conversion root: the matched instruction (`cvt_front`), the inversion
of the match and evaluation, the matched data and the result type (`float_resTy`). -/
macro "cvt_start " ht:term:max hk:term:max op:term:max hn:term:max : tactic =>
  `(tactic| (
    intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
      heval
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
    obtain ⟨ty, x, rfl, hok, hd⟩ := cvt_front hp hctx hi hic rfl $ht $hk (op := $op) rfl $hn
      (m := m' + 9) hmatch
    have hp' := hp
    isel_inv' hp [] at hmatch heval
    obtain ⟨rfl, hw1⟩ := fdata_eq hi hd ‹ctx.insts[ii]? = some _› ‹V.data 152 29 _ = _›
    simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw1
    subst hw1
    have hres := float_resTy hctx (fun cc h => by cases h) hi hic))

set_option hygiene false in
/-- `fcvt_from_{u,s}int` from `i64`: the result type `T`/`t`, the `IntToFpuOp`. -/
macro "from64_root " ht:term:max hk:term:max op:term:max hn:term:max T:term:max t:term:max
    iop:term:max : tactic =>
  `(tactic| (
    cvt_start $ht $hk $op $hn
    have hX : $T = CTy.ofClif ty := by rw [← hres]; exact ‹$T = _›
    obtain rfl : ty = $t := by cases ty <;> simp [CTy.ofClif] at hX ⊢
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h2 := ‹ApplyInternal _ _ _ _ 27 633 _ _ _ _›
    have h3 := ‹externExtract ctx T.value_type _ _ = _›
    have h4 := ‹externCtor ctx T.put_in_reg _ _ = _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := cvt_from64_rhs hp' hR hMR hctx hco (op := $op) (ty := $t)
      (iop := $iop) rfl (by omega) (by omega) h1 h2 h3 h4
    exact ⟨ms, e1, rss, e2, e3⟩))

set_option hygiene false in
/-- `fcvt_from_{u,s}int` from `i8`/`i16`/`i32`: as `from64_root`, then the extension lemma and
its term. -/
macro "small_root " ht:term:max hk:term:max op:term:max hn:term:max T:term:max t:term:max
    iop:term:max e:ident k:num : tactic =>
  `(tactic| (
    cvt_start $ht $hk $op $hn
    have hX : $T = CTy.ofClif ty := by rw [← hres]; exact ‹$T = _›
    obtain rfl : ty = $t := by cases ty <;> simp [CTy.ofClif] at hX ⊢
    have h55 := ‹ApplyInternal _ _ _ _ 27 $k _ _ _ _›
    have hE := $e hp' hco (hn := by omega) h55
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h2 := ‹ApplyInternal _ _ _ _ 27 633 _ _ _ _›
    have h3 := ‹externExtract ctx T.value_type _ _ = _›
    have h4 := ‹externExtract ctx T.fits_in_32 _ _ = _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := cvt_small_rhs hp' hR hMR hctx hco (op := $op) (ty := $t)
      (iop := $iop) rfl (by omega) (by omega) hvb h1 h2 h3 h4 hE
    exact ⟨ms, e1, rss, e2, e3⟩))

set_option hygiene false in
/-- `fcvt_to_{u,s}int_sat` to `i32` (the `fits_in_32` result type) from `tx`. -/
macro "sat32_root " ht:term:max hk:term:max op:term:max hn:term:max tx:term:max fop:term:max :
    tactic =>
  `(tactic| (
    cvt_start $ht $hk $op $hn
    have hX : (CTy.ofClif ty).bits ≤ 32 := by
      rw [← hres]; assumption
    obtain rfl : ty = .i32 := by
      cases ty <;> simp [fCvtTyOk, CTy.ofClif, CTy.bits] at hok hX ⊢
    have h2 := ‹ApplyInternal _ _ _ _ 27 629 _ _ _ _›
    rw [hres] at h2
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h3 := ‹externExtract ctx T.value_type _ _ = _›
    have h4 := ‹externCtor ctx T.put_in_reg _ _ = _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := cvt_toSat_rhs hp' hR hMR hctx hco (op := $op) (ty := .i32)
      (tx := $tx) (fop := $fop) rfl (.inr rfl) (by omega) (by omega) h1 h2 h3 h4
    exact ⟨ms, e1, rss, e2, e3⟩))

set_option hygiene false in
/-- `fcvt_to_{u,s}int_sat.i64` from `tx`. -/
macro "sat64_root " ht:term:max hk:term:max op:term:max hn:term:max tx:term:max fop:term:max :
    tactic =>
  `(tactic| (
    cvt_start $ht $hk $op $hn
    have hX : CTy.int 64 = CTy.ofClif ty := by rw [← hres]; exact ‹CTy.int 64 = _›
    obtain rfl : ty = .i64 := by cases ty <;> simp [CTy.ofClif] at hX ⊢
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h2 := ‹ApplyInternal _ _ _ _ 27 629 _ _ _ _›
    have h3 := ‹externExtract ctx T.value_type _ _ = _›
    have h4 := ‹externCtor ctx T.put_in_reg _ _ = _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := cvt_toSat_rhs hp' hR hMR hctx hco (op := $op) (ty := .i64)
      (tx := $tx) (fop := $fop) rfl (.inl rfl) (by omega) (by omega) h1 h2 h3 h4
    exact ⟨ms, e1, rss, e2, e3⟩))

section Roots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} (MR : MemRelT)
  (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR)
include hp hR hMR

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f32` from `i8`/`i16`/`i32`** (`rule_lower_724`, `lower.isle:724`): `ucvtf s, w` over the zero-extended operand. -/
theorem fcvt_from_uint_f32_le32_okT : LowerRuleOkT isem MR env cp p rule_lower_724 := by
  small_root hp.t2436 term_2436_kind .fcvtFromUint variantNames_FcvtFromUint (CTy.float 32) .f32 .u32ToF32 zext32_ok 556

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f64` from `i8`/`i16`/`i32`** (`rule_lower_727`): `ucvtf d, w`. -/
theorem fcvt_from_uint_f64_le32_okT : LowerRuleOkT isem MR env cp p rule_lower_727 := by
  small_root hp.t2436 term_2436_kind .fcvtFromUint variantNames_FcvtFromUint (CTy.float 64) .f64 .u32ToF64 zext32_ok 556

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f32` from `i64`** (`rule_lower_730`): `ucvtf s, x`. -/
theorem fcvt_from_uint_f32_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_730 := by
  from64_root hp.t2436 term_2436_kind .fcvtFromUint variantNames_FcvtFromUint (CTy.float 32) .f32 .u64ToF32

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f64` from `i64`** (`rule_lower_733`): `ucvtf d, x`. -/
theorem fcvt_from_uint_f64_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_733 := by
  from64_root hp.t2436 term_2436_kind .fcvtFromUint variantNames_FcvtFromUint (CTy.float 64) .f64 .u64ToF64

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f32` from `i8`/`i16`/`i32`** (`rule_lower_744`, `lower.isle:744`): `scvtf s, w` over the sign-extended operand. -/
theorem fcvt_from_sint_f32_le32_okT : LowerRuleOkT isem MR env cp p rule_lower_744 := by
  small_root hp.t2437 term_2437_kind .fcvtFromSint variantNames_FcvtFromSint (CTy.float 32) .f32 .i32ToF32 sext32_ok 555

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f64` from `i8`/`i16`/`i32`** (`rule_lower_747`): `scvtf d, w`. -/
theorem fcvt_from_sint_f64_le32_okT : LowerRuleOkT isem MR env cp p rule_lower_747 := by
  small_root hp.t2437 term_2437_kind .fcvtFromSint variantNames_FcvtFromSint (CTy.float 64) .f64 .i32ToF64 sext32_ok 555

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f32` from `i64`** (`rule_lower_750`): `scvtf s, x`. -/
theorem fcvt_from_sint_f32_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_750 := by
  from64_root hp.t2437 term_2437_kind .fcvtFromSint variantNames_FcvtFromSint (CTy.float 32) .f32 .i64ToF32

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f64` from `i64`** (`rule_lower_753`): `scvtf d, x`. -/
theorem fcvt_from_sint_f64_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_753 := by
  from64_root hp.t2437 term_2437_kind .fcvtFromSint variantNames_FcvtFromSint (CTy.float 64) .f64 .i64ToF64

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat.i32` from `f32`** (`rule_lower_764`, `lower.isle:764`): `fcvtzu w, s`. -/
theorem fcvt_to_uint_sat_i32_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_764 := by
  sat32_root hp.t2433 term_2433_kind .fcvtToUintSat variantNames_FcvtToUintSat .f32 .f32ToU32

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat.i64` from `f32`** (`rule_lower_767`): `fcvtzu x, s`. -/
theorem fcvt_to_uint_sat_i64_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_767 := by
  sat64_root hp.t2433 term_2433_kind .fcvtToUintSat variantNames_FcvtToUintSat .f32 .f32ToU64

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat.i32` from `f64`** (`rule_lower_770`): `fcvtzu w, d`. -/
theorem fcvt_to_uint_sat_i32_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_770 := by
  sat32_root hp.t2433 term_2433_kind .fcvtToUintSat variantNames_FcvtToUintSat .f64 .f64ToU32

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat.i64` from `f64`** (`rule_lower_773`): `fcvtzu x, d`. -/
theorem fcvt_to_uint_sat_i64_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_773 := by
  sat64_root hp.t2433 term_2433_kind .fcvtToUintSat variantNames_FcvtToUintSat .f64 .f64ToU64

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat.i32` from `f32`** (`rule_lower_784`, `lower.isle:784`): `fcvtzs w, s`. -/
theorem fcvt_to_sint_sat_i32_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_784 := by
  sat32_root hp.t2434 term_2434_kind .fcvtToSintSat variantNames_FcvtToSintSat .f32 .f32ToI32

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat.i64` from `f32`** (`rule_lower_787`): `fcvtzs x, s`. -/
theorem fcvt_to_sint_sat_i64_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_787 := by
  sat64_root hp.t2434 term_2434_kind .fcvtToSintSat variantNames_FcvtToSintSat .f32 .f32ToI64

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat.i32` from `f64`** (`rule_lower_790`): `fcvtzs w, d`. -/
theorem fcvt_to_sint_sat_i32_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_790 := by
  sat32_root hp.t2434 term_2434_kind .fcvtToSintSat variantNames_FcvtToSintSat .f64 .f64ToI32

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat.i64` from `f64`** (`rule_lower_793`): `fcvtzs x, d`. -/
theorem fcvt_to_sint_sat_i64_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_793 := by
  sat64_root hp.t2434 term_2434_kind .fcvtToSintSat variantNames_FcvtToSintSat .f64 .f64ToI64

end Roots

end Backend.Proof
