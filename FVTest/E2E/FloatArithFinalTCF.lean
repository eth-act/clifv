module

public import FV.E2E.VerifiableT
public import FVTest.E2E.FloatFinalT
public import FVTest.Backend.FloatArithCtxT
public import FV.E2E.LinkCheck

@[expose] public section

/-!
Non-vacuity of the typed final theorem with the proven float operations (S11f, #35):
`fOps` (`fcvt_from_sint`, `fmul`, `fadd`, `sqrt`, `floor`, `nearest`, `fdemote`/`fpromote`,
`fcvt_to_sint_sat`, `fcvt_to_uint_sat`) is outside subset E, the typed scope `functionET` and the
scope with typed `try_call`s `functionETC` (its statements are float arithmetic, rounding and
conversions) and inside `InSubsetTCF`; its whole pipeline — the validator `lowerCheckTCF`,
`prepare` + `prepCheck`, the spill allocation accepted by `checkAlloc`, `lowerRFunc`, emission and
layout — succeeds (`CompiledTCF`), the prepared code's forms are covered, and the backend reports
it verified (`unverifiedReason? = none`, `lowerChecked fOps true` succeeds). These are the premises
of `backend_correct_finalTCF` besides the run/link contracts (`backend_correct_finalTCF_fOps`).
`lowerCheckTC` rejects it. Checks by `native_decide` (witness only).
`lake build FVTest.E2E.FloatArithFinalTCF`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatArithFinalTCF

open FloatFinalT

/-- Float arithmetic, rounding and conversions in one function. -/
def fOps : Clif.Function := fnOfTextA
  "function %ops(f64, i64, f32) -> i32, i64 {\nblock0(v0: f64, v1: i64, v2: f32):\n    v3 = fcvt_from_sint.f64 v1\n    v4 = fmul v0, v3\n    v5 = fadd v4, v0\n    v6 = sqrt v5\n    v7 = floor v6\n    v8 = fpromote.f64 v2\n    v9 = fadd v7, v8\n    v10 = nearest v9\n    v11 = fdemote.f32 v10\n    v12 = fcvt_to_sint_sat.i32 v11\n    v13 = fcvt_to_uint_sat.i64 v10\n    return v12, v13\n}\n"

#guard !Compile.functionE fOps && !Compile.functionET fOps && !Compile.functionETC fOps &&
  Compile.functionETCF fOps
#guard !lowerCheckTC fOps (FloatDriverT.vcOf fOps) && lowerCheckTCF fOps (FloatDriverT.vcOf fOps)
#guard (unverifiedReason? fOps).isNone && verifiableTCF fOps

/-- **Witness**: `fOps` is in the scope with the float operations, in a program without
functions. -/
theorem inSubsetTCF_t : InSubsetTCF { funcs := [] } fOps :=
  InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl

/-- **Witness**: the compiled-code premise holds for `fOps`. -/
theorem compiledTCF_t :
    CompiledTCF fOps 0 (FloatDriverT.vcOf fOps) (vcpOf fOps) (rfOf fOps) (afOf fOps) (faOf fOps)
      (fbOf fOps) := by
  refine ⟨?_, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (lowerFunction fOps).toBool = true := by native_decide
    unfold FloatDriverT.vcOf
    cases h : lowerFunction fOps with
    | error e => rw [h] at hok; cases hok
    | ok vc => rfl
  · have hok : (Backend.prepare (FloatDriverT.vcOf fOps)).toBool = true := by native_decide
    unfold vcpOf
    cases h : Backend.prepare (FloatDriverT.vcOf fOps) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (vcpOf fOps) (rfOf fOps)).isOk = true := by native_decide
    cases h : checkAlloc (vcpOf fOps) (rfOf fOps) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (vcpOf fOps) (rfOf fOps)).toBool = true := by native_decide
    unfold afOf
    cases h : lowerRFunc (vcpOf fOps) (rfOf fOps) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (afOf fOps)).toBool = true := by native_decide
    unfold faOf
    cases h : emitFunc 0 (afOf fOps) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (faOf fOps).layout.toBool = true := by native_decide
    unfold fbOf
    cases h : (faOf fOps).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness**: the prepared code's forms are covered. -/
theorem formsCovered_t : FormsCovered ⟨(faOf fOps).k, (afOf fOps).slotBase⟩ (vcpOf fOps) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: the backend reports `fOps` verified: no reason, in the scope with the float
operations only, and its validated lowering passes `lowerCheckTCF`. -/
theorem verdict_f : unverifiedReason? fOps = none ∧
    (Compile.functionE fOps = false ∧ Compile.functionET fOps = false ∧
      Compile.functionETC fOps = false ∧ verifiableTCF fOps = true) ∧
    lowerFunction fOps = .ok (getOk (lowerChecked fOps true)) ∧
      lowerCheckTCF fOps (getOk (lowerChecked fOps true)) = true := by
  have hn : unverifiedReason? fOps = none := by native_decide
  have hE : Compile.functionE fOps = false := by native_decide
  have hT : Compile.functionET fOps = false := by native_decide
  have hTC : Compile.functionETC fOps = false := by native_decide
  have hv : (lowerChecked fOps true).toBool = true := by native_decide
  refine ⟨hn, ?_, lowerChecked_specTCF (getOk_eq hv) hE hT hTC⟩
  rcases verdict_of_unverifiedReasonF hn with h | ⟨-, h⟩ | ⟨-, -, h⟩ | h
  · simp [Backend.verifiable, hE] at h
  · simp [Backend.verifiableT, hT] at h
  · simp [Backend.verifiableTC, hTC] at h
  · exact h

/-- **The typed final theorem with the float operations applies to `fOps`**: with its subset,
compiled code and form coverage discharged above, the Arm run of the compiled function refines
the CLIF run, each returned value in its class's return register, under the remaining run/link
contracts. -/
theorem backend_correct_finalTCF_fOps
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk (frameW K (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase
      (RAFrame.compute (vcpOf fOps) (rfOf fOps)).size (afOf fOps) s) K X H (vcpOf fOps).CallSite)
    (hCT : (∃ B ∈ fOps.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase
        (RAFrame.compute (vcpOf fOps) (rfOf fOps)).size (afOf fOps) s) X H (vcpOf fOps).TrySite)
    (hTls : hasTls fOps = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase
        (RAFrame.compute (vcpOf fOps) (rfOf fOps)).size (afOf fOps) s) K X H)
    (hX : ∀ s, XCallsOk env (fOps.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase
        (RAFrame.compute (vcpOf fOps) (rfOf fOps)).size (afOf fOps) s, syms,
        slotOff, (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase⟩ fOps sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs fOps) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase
        (RAFrame.compute (vcpOf fOps) (rfOf fOps)).size (afOf fOps) s, syms,
        slotOff, (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase⟩ fOps sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (afOf fOps).slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (fbOf fOps) base ra s) (hres : StackAvail K (afOf fOps) s)
    (hbe : BodyEntry (afOf fOps) s w₀)
    (hargs : ArgsIn fOps.sig args s) (hcs : ClifEntry fOps args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase
      (RAFrame.compute (vcpOf fOps) (rfOf fOps)).size (afOf fOps) s,
      syms, slotOff, (RAFrame.compute (vcpOf fOps) (rfOf fOps)).intBase⟩ fOps
        cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesT (fbOf fOps) base ra (ArmStepX X H (faOf fOps)) s
      (Clif.runLoop env { funcs := [] } fuel cs) :=
  backend_correct_finalTCF inSubsetTCF_t compiledTCF_t formsCovered_t hC hCT hTls hX hXI hsym
    hslot hent hres hbe hargs hcs hrel htr fuel

end FloatArithFinalTCF
