import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselFloatCopysign

/-!
Non-vacuity of the #35 `fcopysign` root (`IselFloatCopysign`): the context `buildCtx` makes for
a function with `fcopysign` at `f32` and `f64` passes the Boolean check `ctxOkT` (by
`native_decide`, witness only), so `ctxOkT_sound` gives `CtxInvT` for it, and the ISLE `lower`
term fires the `fcopysign` root (`rule_lower_685`, id 712, `copysignRootRule`) on both
instructions, through `fcopy_sign`'s scalar rule (`inst.isle:4612`, id 439) and not its vector
rule (`inst.isle:4619`, id 440); the lowering appends exactly the `ushr` + `sli` pair
`lowerInstOk_fcopysign` is about. The semantics lemma `copysign_holds` is applied to edge
values (signed zeros, NaNs of both signs, infinities, a junk upper lane), checked against
`Clif.evalFloat` by the kernel.
`lake build FVTest.Backend.FloatCopysignCtxT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

namespace Backend.Proof.FloatCopysignCtxT

/-- The `n`-th function of a CLIF text. -/
def fnOfTextC (src : String) (n : Nat := 0) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | fs => match fs[n]? with
    | some p => match p.func with
      | .ok f => f
      | .error _ => default
    | none => default

/-- `buildCtx`'s context and initial lowering state of a function (an empty context if it
fails). -/
def ctxStOfC (f : Clif.Function) : Ctx × LState :=
  match buildCtx f with
  | .ok (ctx, _, st) => (ctx, st)
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] },
      default)

def fCopysign : Clif.Function := fnOfTextC
  "function %cs(i32, i32, i64, i64) -> i64 {\nblock0(v0: i32, v1: i32, v2: i64, v3: i64):\n    v4 = bitcast.f32 v0\n    v5 = bitcast.f32 v1\n    v6 = fcopysign v4, v5\n    v7 = bitcast.f64 v2\n    v8 = bitcast.f64 v3\n    v9 = fcopysign v7, v8\n    v10 = bitcast.i64 v9\n    v11 = bitcast.i32 v6\n    v12 = uextend.i64 v11\n    v13 = iadd v10, v12\n    return v13\n}\n"

/-- The lowering of instruction `ii`: the rules that fired and the instructions appended, or
`([], [])`. -/
def lowerRunC (f : Clif.Function) (ii : Nat) : List Isle.RuleId × List MInst :=
  let (ctx, st) := ctxStOfC f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some (.regsVec _), st', tr) => (tr, (st'.emitted.extract st.emitted.size).toList)
  | _ => ([], [])

-- `buildCtx` succeeds and instructions 2 and 5 are the two `fcopysign`s
#guard (buildCtx fCopysign).toBool
#guard (ctxStOfC fCopysign).1.insts[2]?.bind (·.clif) == some (.float .fcopysign .f32 [4, 5])
#guard (ctxStOfC fCopysign).1.insts[5]?.bind (·.clif) == some (.float .fcopysign .f64 [7, 8])
-- the float values have float vregs
#guard (ctxStOfC fCopysign).1.valueReg? 4 == some (.vreg 4 .float)
#guard (ctxStOfC fCopysign).1.valueReg? 8 == some (.vreg 8 .float)
-- `lower` fires the root (712) through the scalar rule of `fcopy_sign` (439), not the vector
-- rule (440)
#guard copysignRootRule rule_lower_685 && rule_inst_4612.id == 439 && rule_inst_4619.id == 440
#guard (lowerRunC fCopysign 2).1.contains 712 && (lowerRunC fCopysign 2).1.contains 439 &&
  !(lowerRunC fCopysign 2).1.contains 440
#guard (lowerRunC fCopysign 5).1.contains 712 && (lowerRunC fCopysign 5).1.contains 439 &&
  !(lowerRunC fCopysign 5).1.contains 440
-- the appended code is `lowerInstOk_fcopysign`'s: `ushr` into the second fresh vreg, then the
-- `sli` into the first, reusing `x`
#guard (lowerRunC fCopysign 2).2 ==
  let n := (ctxStOfC fCopysign).2.nextVreg
  [.fpuRRI (csUShr .f32) (.vreg (n + 1) .float) (.vreg 5 .float),
    .fpuRRIMod (csSli .f32) (.vreg n .float) (.vreg 4 .float) (.vreg (n + 1) .float)]
#guard (lowerRunC fCopysign 5).2 ==
  let n := (ctxStOfC fCopysign).2.nextVreg
  [.fpuRRI (csUShr .f64) (.vreg (n + 1) .float) (.vreg 8 .float),
    .fpuRRIMod (csSli .f64) (.vreg n .float) (.vreg 7 .float) (.vreg (n + 1) .float)]

/-- **`CtxInvT` holds for the `fcopysign` context.** -/
theorem ctxInvT_float_copysign : CtxInvT fCopysign (ctxStOfC fCopysign).1 :=
  ctxOkT_sound (by native_decide)

/-- **The root of `LowerRulesCorrectCS` applies to this context**: its `fcopysign.f32`
(instruction 2) lies in a `CtxInvT` context and `rule_lower_685` is the `copysignRootRule` of
`lower`, so `lowerRulesCorrectCS_program` gives `LowerRuleOkT` for the rule on it. -/
theorem float_copysign_root_applies {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR) :
    CtxInvT fCopysign (ctxStOfC fCopysign).1 ∧
      ((ctxStOfC fCopysign).1.insts[2]?.bind (·.clif)) =
        some (.float .fcopysign .f32 [4, 5]) ∧
      LowerRuleOkT isem MR env cp program rule_lower_685 :=
  ⟨ctxInvT_float_copysign, by native_decide,
    lowerRulesCorrectCS_program F isem MR env cp hR hMR rule_lower_685
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; decide +kernel) rfl⟩

/-! ## Edge values: CLIF's `fcopysign` and the emitted `ushr` + `sli` agree (kernel-checked)

`copysign_holds` on concrete register values: `fcopysign x y` is computed by `Clif.evalFloat`,
the `ushr`/`sli` outputs by `fpuRRIOut`/`fpuRRIModOut` (`ispecFP`), and the result's low bits
are compared. -/

/-- The `ushr` + `sli` output of `fcopy_sign` at a float type on register values `zx`, `zy`. -/
def csOut (ty : Clif.Ty) (zx zy : CV) : Option CV :=
  (fpuRRIOut (csUShr ty) zy).bind (fpuRRIModOut (csSli ty) zx)

/-- CLIF's `fcopysign.f32` agrees with the emitted pair on bit patterns `x`, `y` held in the low
32 bits of registers whose other bits are `hx`, `hy`. -/
def agree32 (x y : BitVec 32) (hx hy : BitVec 96) : Bool :=
  match Clif.evalFloat .fcopysign .f32 [⟨.f32, x⟩, ⟨.f32, y⟩], csOut .f32 (hx ++ x) (hy ++ y) with
  | .ok r, some z => r.ty == .f32 && z.toNat % 2 ^ 32 == r.bits.toNat
  | _, _ => false

/-- As `agree32`, for `fcopysign.f64` in the low 64 bits. -/
def agree64 (x y : BitVec 64) (hx hy : BitVec 64) : Bool :=
  match Clif.evalFloat .fcopysign .f64 [⟨.f64, x⟩, ⟨.f64, y⟩], csOut .f64 (hx ++ x) (hy ++ y) with
  | .ok r, some z => r.ty == .f64 && z.toNat % 2 ^ 64 == r.bits.toNat
  | _, _ => false

/-- The value `fcopysign.f32` gives. -/
def cs32 (x y : BitVec 32) : Clif.Res Clif.Val := Clif.evalFloat .fcopysign .f32 [⟨.f32, x⟩, ⟨.f32, y⟩]
/-- The value `fcopysign.f64` gives. -/
def cs64 (x y : BitVec 64) : Clif.Res Clif.Val := Clif.evalFloat .fcopysign .f64 [⟨.f64, x⟩, ⟨.f64, y⟩]

-- `decide +kernel` on `evalFloat` results (witness only)
deriving instance DecidableEq for Clif.Res

theorem cs32_one_nzero : cs32 0x3F800000#32 0x80000000#32 = .ok ⟨.f32, 0xBF800000#32⟩ := by
  decide +kernel
theorem cs32_zero_nzero : cs32 0x00000000#32 0x80000000#32 = .ok ⟨.f32, 0x80000000#32⟩ := by
  decide +kernel
theorem cs32_nzero_zero : cs32 0x80000000#32 0x00000000#32 = .ok ⟨.f32, 0x00000000#32⟩ := by
  decide +kernel
theorem cs32_nan_neg : cs32 0x7FC00000#32 0xBF800000#32 = .ok ⟨.f32, 0xFFC00000#32⟩ := by
  decide +kernel
theorem cs32_nnan_pos : cs32 0xFFC00000#32 0x3F800000#32 = .ok ⟨.f32, 0x7FC00000#32⟩ := by
  decide +kernel
theorem cs32_pi_nnan : cs32 0x40490FDB#32 0xFFC00000#32 = .ok ⟨.f32, 0xC0490FDB#32⟩ := by
  decide +kernel
theorem cs32_snan_neg : cs32 0x7F800001#32 0x80000000#32 = .ok ⟨.f32, 0xFF800001#32⟩ := by
  decide +kernel
theorem cs32_inf_neg : cs32 0x7F800000#32 0xC0000000#32 = .ok ⟨.f32, 0xFF800000#32⟩ := by
  decide +kernel
theorem cs64_one_nzero : cs64 0x3FF0000000000000#64 0x8000000000000000#64 =
    .ok ⟨.f64, 0xBFF0000000000000#64⟩ := by decide +kernel
theorem cs64_nan_neg : cs64 0x7FF8000000000000#64 0xBFF0000000000000#64 =
    .ok ⟨.f64, 0xFFF8000000000000#64⟩ := by decide +kernel
theorem cs64_npi_pnan : cs64 0xC00921FB54442D18#64 0x7FF8000000000001#64 =
    .ok ⟨.f64, 0x400921FB54442D18#64⟩ := by decide +kernel
theorem cs64_nzero_zero : cs64 0x8000000000000000#64 0x0000000000000000#64 =
    .ok ⟨.f64, 0x0000000000000000#64⟩ := by decide +kernel

-- the emitted pair agrees with CLIF on the edge values, with junk above the operands (the
-- `2s` forms also rewrite lane 1, which `VHolds` never reads)
theorem agree32_edges :
    (agree32 0x3F800000#32 0x80000000#32 0 0 && agree32 0x00000000#32 0x80000000#32 0 0 &&
      agree32 0x80000000#32 0x00000000#32 0 0 && agree32 0x7FC00000#32 0xBF800000#32 0 0 &&
      agree32 0xFFC00000#32 0x3F800000#32 0 0 && agree32 0x7F800001#32 0x80000000#32 0 0 &&
      agree32 0x40490FDB#32 0xFFC00000#32 0xDEADBEEFCAFEF00D12345678#96
        0xFFFFFFFFFFFFFFFFFFFFFFFF#96 &&
      agree32 0xC0490FDB#32 0x7FC00001#32 0xFFFFFFFFFFFFFFFFFFFFFFFF#96 0x0123456789ABCDEF00000000#96) =
      true := by decide +kernel

theorem agree64_edges :
    (agree64 0x3FF0000000000000#64 0x8000000000000000#64 0 0 &&
      agree64 0x8000000000000000#64 0x0000000000000000#64 0 0 &&
      agree64 0x7FF8000000000000#64 0xBFF0000000000000#64 0 0 &&
      agree64 0xFFF8000000000000#64 0x3FF0000000000000#64 0xDEADBEEFCAFEF00D#64 0 &&
      agree64 0x7FF0000000000001#64 0x8000000000000000#64 0 0xFFFFFFFFFFFFFFFF#64 &&
      agree64 0xC00921FB54442D18#64 0x7FF8000000000001#64 0x0123456789ABCDEF#64
        0xFFFFFFFFFFFFFFFF#64) = true := by decide +kernel

/-- `copysign_holds` itself on a concrete instance: the `f32` pair's output holds CLIF's value
for `fcopysign 1.0, -0.0` with junk in the operand registers' upper bits. -/
theorem copysign_holds_one_nzero :
    ∃ t z, fpuRRIOut (csUShr .f32) (0xFFFFFFFFFFFFFFFFFFFFFFFF#96 ++ 0x80000000#32) = some t ∧
      fpuRRIModOut (csSli .f32) (0xDEADBEEFCAFEF00D12345678#96 ++ 0x3F800000#32) t = some z ∧
      VHolds ⟨.f32, 0xBF800000#32⟩ z := by
  obtain ⟨t, z, h1, h2, h3⟩ := copysign_holds (ty := .f32) (.inl rfl)
    (a := ⟨.f32, 0x3F800000#32⟩) (b := ⟨.f32, 0x80000000#32⟩)
    (za := 0xDEADBEEFCAFEF00D12345678#96 ++ 0x3F800000#32)
    (zb := 0xFFFFFFFFFFFFFFFFFFFFFFFF#96 ++ 0x80000000#32)
    (by unfold VHolds; decide +kernel) (by unfold VHolds; decide +kernel) cs32_one_nzero
  exact ⟨t, z, h1, h2, h3⟩

end Backend.Proof.FloatCopysignCtxT
