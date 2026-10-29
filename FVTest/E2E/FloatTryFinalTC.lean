module

public import FV.E2E.VerifiableT
public import FVTest.E2E.FloatFinalT
public import FVTest.Backend.FloatTryLower
public import FV.E2E.LinkCheck

@[expose] public section

/-!
Non-vacuity of the typed final theorem with typed `try_call`s (S11e6, #419):
`FloatTryLower.fTryF` (a direct `try_call` of `%g(f64, i64) -> f64`) is outside subset E and the
typed scope `functionET` (its callee has a float signature) and inside `InSubsetTC`; its whole
pipeline — the validator `lowerCheckTC`, `prepare` + `prepCheck`, the spill allocation accepted by
`checkAlloc`, `lowerRFunc`, emission and layout — succeeds (`CompiledTC`), the prepared code's
forms are covered, and the backend reports it verified (`unverifiedReason? = none`,
`lowerChecked fTryF true` succeeds). These are the premises of `backend_correct_finalTC` besides
the run/link contracts (`backend_correct_finalTC_fTryF`). The integer validators reject it.
Checks by `native_decide` (witness only).
`lake build FVTest.E2E.FloatTryFinalTC`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatTryFinalTC

open FloatFinalT FloatTryLower

#guard !Compile.functionE fTryF && !Compile.functionET fTryF && Compile.functionETC fTryF
#guard !lowerCheckT fTryF (FloatDriverT.vcOf fTryF) && lowerCheckTC fTryF (FloatDriverT.vcOf fTryF)
#guard (unverifiedReason? fTryF).isNone && verifiableTC fTryF

/-- **Witness**: `fTryF` is in the scope with typed `try_call`s, in a program without functions. -/
theorem inSubsetTC_t : InSubsetTC { funcs := [] } fTryF :=
  InSubsetTC.of_verifiableTC (by native_decide) fun _ => rfl

/-- **Witness**: the compiled-code premise holds for `fTryF`. -/
theorem compiledTC_t :
    CompiledTC fTryF 0 (FloatDriverT.vcOf fTryF) (vcpOf fTryF) (rfOf fTryF) (afOf fTryF) (faOf fTryF)
      (fbOf fTryF) := by
  refine ⟨?_, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (lowerFunction fTryF).toBool = true := by native_decide
    unfold FloatDriverT.vcOf
    cases h : lowerFunction fTryF with
    | error e => rw [h] at hok; cases hok
    | ok vc => rfl
  · have hok : (Backend.prepare (FloatDriverT.vcOf fTryF)).toBool = true := by native_decide
    unfold vcpOf
    cases h : Backend.prepare (FloatDriverT.vcOf fTryF) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (vcpOf fTryF) (rfOf fTryF)).isOk = true := by native_decide
    cases h : checkAlloc (vcpOf fTryF) (rfOf fTryF) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (vcpOf fTryF) (rfOf fTryF)).toBool = true := by native_decide
    unfold afOf
    cases h : lowerRFunc (vcpOf fTryF) (rfOf fTryF) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (afOf fTryF)).toBool = true := by native_decide
    unfold faOf
    cases h : emitFunc 0 (afOf fTryF) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (faOf fTryF).layout.toBool = true := by native_decide
    unfold fbOf
    cases h : (faOf fTryF).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness**: the prepared code's forms are covered. -/
theorem formsCovered_t : FormsCovered ⟨(faOf fTryF).k, (afOf fTryF).slotBase⟩ (vcpOf fTryF) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: the backend reports `fTryF` verified: no reason, in the scope with typed
`try_call`s only, and its validated lowering passes `lowerCheckTC`. -/
theorem verdict_t : unverifiedReason? fTryF = none ∧
    (Compile.functionE fTryF = false ∧ Compile.functionET fTryF = false ∧
      verifiableTC fTryF = true) ∧
    lowerFunction fTryF = .ok (getOk (lowerChecked fTryF true)) ∧
      lowerCheckTC fTryF (getOk (lowerChecked fTryF true)) = true := by
  have hn : unverifiedReason? fTryF = none := by native_decide
  have hE : Compile.functionE fTryF = false := by native_decide
  have hT : Compile.functionET fTryF = false := by native_decide
  have hTC : Compile.functionETC fTryF = true := by native_decide
  have hv : (lowerChecked fTryF true).toBool = true := by native_decide
  refine ⟨hn, ?_, lowerChecked_specTC (getOk_eq hv) hE hT hTC⟩
  rcases verdict_of_unverifiedReason hn (by simp [hTC]) with h | ⟨-, h⟩ | h
  · simp [Backend.verifiable, hE] at h
  · simp [Backend.verifiableT, hT] at h
  · exact h

/-- **The typed final theorem with typed `try_call`s applies to `fTryF`** (a function whose
`try_call` calls an `f64`-returning callee): with its subset, compiled code and form coverage
discharged above, the Arm run of the compiled function refines the CLIF run, each returned value
in its class's return register, under the remaining run/link contracts. -/
theorem backend_correct_finalTC_fTryF
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk (frameW K (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase
      (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).size (afOf fTryF) s) K X H (vcpOf fTryF).CallSite)
    (hCT : (∃ B ∈ fTryF.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase
        (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).size (afOf fTryF) s) X H (vcpOf fTryF).TrySite)
    (hTls : hasTls fTryF = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase
        (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).size (afOf fTryF) s) K X H)
    (hX : ∀ s, XCallsOk env (fTryF.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase
        (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).size (afOf fTryF) s, syms,
        slotOff, (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase⟩ fTryF sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs fTryF) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase
        (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).size (afOf fTryF) s, syms,
        slotOff, (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase⟩ fTryF sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (afOf fTryF).slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (fbOf fTryF) base ra s) (hres : StackAvail K (afOf fTryF) s)
    (hbe : BodyEntry (afOf fTryF) s w₀)
    (hargs : ArgsIn fTryF.sig args s) (hcs : ClifEntry fTryF args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase
      (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).size (afOf fTryF) s,
      syms, slotOff, (RAFrame.compute (vcpOf fTryF) (rfOf fTryF)).intBase⟩ fTryF
        cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesT (fbOf fTryF) base ra (ArmStepX X H (faOf fTryF)) s
      (Clif.runLoop env { funcs := [] } fuel cs) :=
  backend_correct_finalTC inSubsetTC_t compiledTC_t formsCovered_t hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel

end FloatTryFinalTC
