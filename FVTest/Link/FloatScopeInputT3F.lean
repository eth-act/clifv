module

public import FV.E2E.LinkScopeInputT3F
public import FV.E2E.LinkCheck

@[expose] public section

/-! Non-vacuity of the float input scope's `lowerFunction` totality (S11f, #35).

`%fs` has float arithmetic (`fadd`, `fmul`), rounding (`ceil`), conversions (`fcvt_from_sint`,
`fpromote`, the saturating `fcvt_to_sint_sat`) and a scalar `fcmp`: outside the typed movement
scope `Compile.functionET` (so `lowerFunction_ok_T3` does not apply), inside the float scope
`Compile.functionETF`. It meets every decided premise of `lowerFunction_ok_inT3F`
(`premisesB`, by `native_decide`, witness only), so `lowerFunction` succeeds on it by the
theorem (`lowers`). `lake build FVTest.Link.FloatScopeInputT3F`. -/

namespace E2E.FloatScopeInputT3FWitness

open E2E E2E.LinkCheck Backend Backend.Proof Backend.Proof.Driver

def src : String := "function %fs(f64, i32, f32) -> f64, i32 {
block0(v0: f64, v1: i32, v2: f32):
    v3 = fcvt_from_sint.f64 v1
    v4 = fadd v0, v3
    v5 = ceil v4
    v6 = fpromote.f64 v2
    v7 = fmul v5, v6
    v8 = fcmp lt v7, v0
    v9 = uextend.i32 v8
    v10 = fcvt_to_sint_sat.i32 v7
    v11 = iadd v9, v10
    return v7, v11
}
"

def fS : Clif.Function := ({ clif := src, ra := "{}" } : FnInput).func

/-- `%fs` is outside the typed movement scope, inside the float scope. -/
def scopeB : Bool := !Compile.functionET fS && Compile.functionETF fS

/-- The decided premises of `lowerFunction_ok_inT3F`. -/
def premisesB : Bool :=
  sigAbiOk fS.sig && dominatedB fS && lowerScopeTFB fS && Spill.arityOkB fS &&
    Spill.entryParamsB fS && extendsWidenB fS && driverInB fS && Prg.iselInB fS

theorem scope_ok : scopeB = true := by native_decide

theorem premises_ok : premisesB = true := by native_decide

/-- **`lowerFunction` succeeds on `%fs`** by `lowerFunction_ok_inT3F`. -/
theorem lowers : ∃ vc, lowerFunction fS = .ok vc := by
  have h := premises_ok
  simp only [premisesB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨habi, hd⟩, hs⟩, har⟩, hent⟩, hw⟩, hdrv⟩, hin⟩ := h
  exact lowerFunction_ok_inT3F habi hd hs har hent hw hdrv hin

end E2E.FloatScopeInputT3FWitness
