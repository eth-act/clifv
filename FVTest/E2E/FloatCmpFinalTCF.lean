import FV.E2E.VerifiableT
import FVTest.E2E.FloatFinalT
import FVTest.Backend.FloatArithCtxT
import FV.E2E.LinkCheck
import FVTest.Backend.FloatCmpCtxT

/-!
Non-vacuity of the typed final theorem with the proven float operations for the scalar
comparisons (S11f, #35): `fCmpT` (`fcmp lt`/`fcmp ge` of `f64` values, one of them an `fadd`'s
result, combined by `band`; `fcmp uno` of an `f32` under a `uextend`) is outside subset E, the
typed scope `functionET` and the scope with typed `try_call`s `functionETC`, and inside
`InSubsetTCF`; its whole pipeline — the validator `lowerCheckTCF`, `prepare` + `prepCheck`, the
spill allocation accepted by `checkAlloc`, `lowerRFunc`, emission and layout — succeeds
(`CompiledTCF`), the prepared code's forms are covered, and the backend reports it verified
(`unverifiedReason? = none`, `lowerChecked fCmpT true` succeeds). These are the premises of
`backend_correct_finalTCF` besides the run/link contracts (`backend_correct_finalTCF_fCmp`).
`lowerCheckTC` rejects it. Checks by `native_decide` (witness only).
`lake build FVTest.E2E.FloatCmpFinalTCF`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatCmpFinalTCF

open FloatFinalT Isle.Aarch64

/-- Scalar `fcmp`s of `f64` and `f32` values, one under a `uextend` (`rule_lower_1283`). -/
def fCmpT : Clif.Function := fnOfTextA
  "function %cmp(f64, f64, f32) -> i8, i32 {\nblock0(v0: f64, v1: f64, v2: f32):\n    v3 = fcmp lt v0, v1\n    v4 = fadd v0, v1\n    v5 = fcmp ge v4, v0\n    v6 = band v3, v5\n    v7 = fcmp uno v2, v2\n    v8 = uextend.i32 v7\n    return v6, v8\n}\n"

#guard !Compile.functionE fCmpT && !Compile.functionET fCmpT && !Compile.functionETC fCmpT &&
  Compile.functionETCF fCmpT
#guard !lowerCheckTC fCmpT (FloatDriverT.vcOf fCmpT) && lowerCheckTCF fCmpT (FloatDriverT.vcOf fCmpT)
#guard (unverifiedReason? fCmpT).isNone && verifiableTCF fCmpT

-- `lower` fires the `fcmp` roots: 951 (`rule_lower_2176`) on the `fcmp`s (instructions 0, 2, 4),
-- 812 (`rule_lower_1283`) on the `uextend` (instruction 5)
#guard (lowerTraceC fCmpT 0).contains 951 && (lowerTraceC fCmpT 2).contains 951 &&
  (lowerTraceC fCmpT 4).contains 951 && (lowerTraceC fCmpT 5).contains 812

/-- **Witness of the comparison facts of the exclusion**: `buildCtx`'s context of `fCmpT` is a
float-capable context (`CtxInvT`, `ctxOkT_sound`) whose instruction 0 is `fcmp lt` of two `f64`
values; it is in `Compile.fCmpET` (`fCmpET_cases`), its data has an opcode of `opsTF`
(`instData_cmp`), its result type is `i8` (`fcmp_resTy`), and the vector `fcmp` root
`rule_lower_2179` does not match it (`rule_lower_2179_nomatchT`). -/
theorem fcmp_excl_w :
    CtxInvT fCmpT (ctxStOfC fCmpT).1 ∧
      ∃ info, (ctxStOfC fCmpT).1.insts[0]? = some info ∧
        info.clif = some (.float (.fcmp .lt) .f64 [0, 1]) ∧
        Compile.fCmpET (.float (.fcmp .lt) .f64 [0, 1]) = true ∧
        (∃ kf ko fs, info.data = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ opsTF) ∧
        info.resTys.head?.getD .invalid = .int 8 ∧
        ∀ cfg m s env' s1, (Isle.Interp.matchRule program (sem (ctxStOfC fCmpT).1) cfg m
          rule_lower_2179 [.inst 0]).run s ≠ .ok (some env', s1) := by
  have hctx : CtxInvT fCmpT (ctxStOfC fCmpT).1 := ctxOkT_sound (by native_decide)
  have h0 : ((ctxStOfC fCmpT).1.insts[0]?.bind (·.clif)) =
      some (.float (.fcmp .lt) .f64 [0, 1]) := by native_decide
  refine ⟨hctx, ?_⟩
  cases hi : (ctxStOfC fCmpT).1.insts[0]? with
  | none => rw [hi] at h0; cases h0
  | some info =>
    rw [hi] at h0
    have hc : info.clif = some (.float (.fcmp .lt) .f64 [0, 1]) := h0
    exact ⟨info, rfl, hc, rfl, instData_cmp (hctx.data 0 info _ hi hc), fcmp_resTy hctx hi hc,
      fun cfg m s env' s1 => rule_lower_2179_nomatchT hctx hi hc⟩

/-- **Witness**: `fCmpT` is in the scope with the float operations, in a program without
functions. -/
theorem inSubsetTCF_t : InSubsetTCF { funcs := [] } fCmpT :=
  InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl

/-- **Witness**: the compiled-code premise holds for `fCmpT`. -/
theorem compiledTCF_t :
    CompiledTCF fCmpT 0 (FloatDriverT.vcOf fCmpT) (vcpOf fCmpT) (rfOf fCmpT) (afOf fCmpT) (faOf fCmpT)
      (fbOf fCmpT) := by
  refine ⟨?_, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (lowerFunction fCmpT).toBool = true := by native_decide
    unfold FloatDriverT.vcOf
    cases h : lowerFunction fCmpT with
    | error e => rw [h] at hok; cases hok
    | ok vc => rfl
  · have hok : (Backend.prepare (FloatDriverT.vcOf fCmpT)).toBool = true := by native_decide
    unfold vcpOf
    cases h : Backend.prepare (FloatDriverT.vcOf fCmpT) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (vcpOf fCmpT) (rfOf fCmpT)).isOk = true := by native_decide
    cases h : checkAlloc (vcpOf fCmpT) (rfOf fCmpT) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (vcpOf fCmpT) (rfOf fCmpT)).toBool = true := by native_decide
    unfold afOf
    cases h : lowerRFunc (vcpOf fCmpT) (rfOf fCmpT) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (afOf fCmpT)).toBool = true := by native_decide
    unfold faOf
    cases h : emitFunc 0 (afOf fCmpT) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (faOf fCmpT).layout.toBool = true := by native_decide
    unfold fbOf
    cases h : (faOf fCmpT).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness**: the prepared code's forms are covered. -/
theorem formsCovered_t : FormsCovered ⟨(faOf fCmpT).k, (afOf fCmpT).slotBase⟩ (vcpOf fCmpT) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: the backend reports `fCmpT` verified: no reason, in the scope with the float
operations only, and its validated lowering passes `lowerCheckTCF`. -/
theorem verdict_f : unverifiedReason? fCmpT = none ∧
    (Compile.functionE fCmpT = false ∧ Compile.functionET fCmpT = false ∧
      Compile.functionETC fCmpT = false ∧ verifiableTCF fCmpT = true) ∧
    lowerFunction fCmpT = .ok (getOk (lowerChecked fCmpT true)) ∧
      lowerCheckTCF fCmpT (getOk (lowerChecked fCmpT true)) = true := by
  have hn : unverifiedReason? fCmpT = none := by native_decide
  have hE : Compile.functionE fCmpT = false := by native_decide
  have hT : Compile.functionET fCmpT = false := by native_decide
  have hTC : Compile.functionETC fCmpT = false := by native_decide
  have hv : (lowerChecked fCmpT true).toBool = true := by native_decide
  refine ⟨hn, ?_, lowerChecked_specTCF (getOk_eq hv) hE hT hTC⟩
  rcases verdict_of_unverifiedReasonF hn with h | ⟨-, h⟩ | ⟨-, -, h⟩ | h
  · simp [Backend.verifiable, hE] at h
  · simp [Backend.verifiableT, hT] at h
  · simp [Backend.verifiableTC, hTC] at h
  · exact h

/-- **The typed final theorem with the float operations applies to `fCmpT`**: with its subset,
compiled code and form coverage discharged above, the Arm run of the compiled function refines
the CLIF run, each returned value in its class's return register, under the remaining run/link
contracts. -/
theorem backend_correct_finalTCF_fCmp
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk (frameW K (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase
      (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).size (afOf fCmpT) s) K X H (vcpOf fCmpT).CallSite)
    (hCT : (∃ B ∈ fCmpT.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase
        (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).size (afOf fCmpT) s) X H (vcpOf fCmpT).TrySite)
    (hTls : hasTls fCmpT = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase
        (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).size (afOf fCmpT) s) K X H)
    (hX : ∀ s, XCallsOk env (fCmpT.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase
        (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).size (afOf fCmpT) s, syms,
        slotOff, (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase⟩ fCmpT sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs fCmpT) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase
        (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).size (afOf fCmpT) s, syms,
        slotOff, (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase⟩ fCmpT sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (afOf fCmpT).slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (fbOf fCmpT) base ra s) (hres : StackAvail K (afOf fCmpT) s)
    (hbe : BodyEntry (afOf fCmpT) s w₀)
    (hargs : ArgsIn fCmpT.sig args s) (hcs : ClifEntry fCmpT args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase
      (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).size (afOf fCmpT) s,
      syms, slotOff, (RAFrame.compute (vcpOf fCmpT) (rfOf fCmpT)).intBase⟩ fCmpT
        cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesT (fbOf fCmpT) base ra (ArmStepX X H (faOf fCmpT)) s
      (Clif.runLoop env { funcs := [] } fuel cs) :=
  backend_correct_finalTCF inSubsetTCF_t compiledTCF_t formsCovered_t hC hCT hTls hX hXI hsym
    hslot hent hres hbe hargs hcs hrel htr fuel

end FloatCmpFinalTCF
