import FV.E2E.VerifiableT
import FVTest.E2E.FloatFinalT
import FVTest.Backend.FloatArithCtxT
import FV.E2E.LinkCheck

/-!
Non-vacuity of the typed final theorem with plain float `call`s (S11g, #1015, #35): `fCallP`
calls `%g (f64, i64, f32) -> f64` (its `f64` and `f32` arguments in v0/v1, the `i64` in x0, the
result in v0) and `%k (f32) -> f32`. Until S11g it was outside every typed scope
(`Compile.functionETCF`'s `callsE`: every `call`'s callee had an integer signature). Now it is in
`InSubsetTCF`, its whole pipeline — the validator `lowerCheckTCF`, `prepare` + `prepCheck`, the
spill allocation accepted by `checkAlloc`, `lowerRFunc`, emission and layout — succeeds
(`CompiledTCF`), the prepared code's forms are covered, and the backend reports it verified
(`unverifiedReason? = none`, `lowerChecked fCallP true` succeeds): the premises of
`backend_correct_finalTCF` besides the run/link contracts (`backend_correct_finalTCF_fCallP`).
Checks by `native_decide` (witness only). `lake build FVTest.E2E.FloatCallFinalTCF`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatCallFinalTCF

open FloatFinalT

/-- Plain `call`s passing and returning `f32`s and `f64`s. -/
def fCallP : Clif.Function := fnOfTextA
  "function %p(f64, i64, f32) -> f32 {\n    fn0 = %g(f64, i64, f32) -> f64\n    fn1 = %k(f32) -> f32\nblock0(v0: f64, v1: i64, v2: f32):\n    v3 = call fn0(v0, v1, v2)\n    v4 = fdemote.f32 v3\n    v5 = call fn1(v4)\n    return v5\n}\n"

#guard !Compile.functionE fCallP && !Compile.functionET fCallP && !Compile.functionETC fCallP &&
  Compile.functionETCF fCallP
-- the removed `callsE_of_functionETCF`/`ctxT_of_functionETCF` (S11g) are false on `fCallP`: it is
-- in `functionETCF`, and its callees do not have integer signatures
#guard Compile.functionETCF fCallP && !Compile.callsE fCallP
#guard lowerCheckTCF fCallP (FloatDriverT.vcOf fCallP)
#guard (unverifiedReason? fCallP).isNone && verifiableTCF fCallP

/-- **Witness**: `fCallP` is in the scope with the float operations and float calls, in a program
without functions. -/
theorem inSubsetTCF_p : InSubsetTCF { funcs := [] } fCallP :=
  InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl

/-- **Witness**: the compiled-code premise holds for `fCallP`. -/
theorem compiledTCF_p :
    CompiledTCF fCallP 0 (FloatDriverT.vcOf fCallP) (vcpOf fCallP) (rfOf fCallP) (afOf fCallP)
      (faOf fCallP) (fbOf fCallP) := by
  refine ⟨?_, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (lowerFunction fCallP).toBool = true := by native_decide
    unfold FloatDriverT.vcOf
    cases h : lowerFunction fCallP with
    | error e => rw [h] at hok; cases hok
    | ok vc => rfl
  · have hok : (Backend.prepare (FloatDriverT.vcOf fCallP)).toBool = true := by native_decide
    unfold vcpOf
    cases h : Backend.prepare (FloatDriverT.vcOf fCallP) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (vcpOf fCallP) (rfOf fCallP)).isOk = true := by native_decide
    cases h : checkAlloc (vcpOf fCallP) (rfOf fCallP) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (vcpOf fCallP) (rfOf fCallP)).toBool = true := by native_decide
    unfold afOf
    cases h : lowerRFunc (vcpOf fCallP) (rfOf fCallP) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (afOf fCallP)).toBool = true := by native_decide
    unfold faOf
    cases h : emitFunc 0 (afOf fCallP) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (faOf fCallP).layout.toBool = true := by native_decide
    unfold fbOf
    cases h : (faOf fCallP).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness**: the prepared code's forms are covered. -/
theorem formsCovered_p :
    FormsCovered ⟨(faOf fCallP).k, (afOf fCallP).slotBase⟩ (vcpOf fCallP) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: the backend reports `fCallP` verified: no reason, in the scope with the float
operations and float calls only, and its validated lowering passes `lowerCheckTCF`. -/
theorem verdict_p : unverifiedReason? fCallP = none ∧
    (Compile.functionE fCallP = false ∧ Compile.functionET fCallP = false ∧
      Compile.functionETC fCallP = false ∧ verifiableTCF fCallP = true) ∧
    lowerFunction fCallP = .ok (getOk (lowerChecked fCallP true)) ∧
      lowerCheckTCF fCallP (getOk (lowerChecked fCallP true)) = true := by
  have hn : unverifiedReason? fCallP = none := by native_decide
  have hE : Compile.functionE fCallP = false := by native_decide
  have hT : Compile.functionET fCallP = false := by native_decide
  have hTC : Compile.functionETC fCallP = false := by native_decide
  have hv : (lowerChecked fCallP true).toBool = true := by native_decide
  refine ⟨hn, ?_, lowerChecked_specTCF (getOk_eq hv) hE hT hTC⟩
  rcases verdict_of_unverifiedReasonF hn with h | ⟨-, h⟩ | ⟨-, -, h⟩ | h
  · simp [Backend.verifiable, hE] at h
  · simp [Backend.verifiableT, hT] at h
  · simp [Backend.verifiableTC, hTC] at h
  · exact h

/-- **The typed final theorem applies to `fCallP`**: with its subset, compiled code and form
coverage discharged above, the Arm run of the compiled function refines the CLIF run, each
returned value in its class's return register, under the remaining run/link contracts (the
callees' contract `hX` over `fCallP`'s float-signature externs). -/
theorem backend_correct_finalTCF_fCallP
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk (frameW K (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase
      (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).size (afOf fCallP) s) K X H
      (vcpOf fCallP).CallSite)
    (hCT : (∃ B ∈ fCallP.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase
        (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).size (afOf fCallP) s) X H
        (vcpOf fCallP).TrySite)
    (hTls : hasTls fCallP = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase
        (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).size (afOf fCallP) s) K X H)
    (hX : ∀ s, XCallsOk env (fCallP.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase
        (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).size (afOf fCallP) s, syms,
        slotOff, (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase⟩ fCallP sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs fCallP) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase
        (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).size (afOf fCallP) s, syms,
        slotOff, (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase⟩ fCallP sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (afOf fCallP).slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (fbOf fCallP) base ra s) (hres : StackAvail K (afOf fCallP) s)
    (hbe : BodyEntry (afOf fCallP) s w₀)
    (hargs : ArgsIn fCallP.sig args s) (hcs : ClifEntry fCallP args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase
      (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).size (afOf fCallP) s,
      syms, slotOff, (RAFrame.compute (vcpOf fCallP) (rfOf fCallP)).intBase⟩ fCallP
        cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesT (fbOf fCallP) base ra (ArmStepX X H (faOf fCallP)) s
      (Clif.runLoop env { funcs := [] } fuel cs) :=
  backend_correct_finalTCF inSubsetTCF_p compiledTCF_p formsCovered_p hC hCT hTls hX hXI hsym
    hslot hent hres hbe hargs hcs hrel htr fuel

end FloatCallFinalTCF
