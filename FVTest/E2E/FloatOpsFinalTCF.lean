import FV.E2E.VerifiableT
import FVTest.E2E.FloatFinalT
import FVTest.Backend.FloatScopeFLOWitness
import FV.E2E.EmitSize

/-!
Non-vacuity of `fcopysign` and `fma` in the typed final theorem (#35).

The functions of `FVTest/Backend/FloatScopeFLOWitness.lean`: `fCs` (`fcopysign.f64`), `fCs32`
(`fcopysign.f32`), `fFma` (`fma.f64`), `fFmaNegZ` (`fma.f32` with an `fneg` addend:
`rule_lower_609`, `fnmsub`), `fFmaNegX` (`fma.f64` with an `fneg` first operand: `fmadd` rule 2,
`fmsub`). Each is in `InSubsetTCF` (`Compile.functionETCF`), its whole pipeline succeeds
(`CompiledTCF`: the validator `lowerCheckTCF` accepts it) and the prepared code's forms are
covered (`FormsCovered`: `ushr`/`sli`, the `fpu_rrrr` forms): these are `backend_correct_finalTCF`'s
premises besides the run/link contracts. `backend_correct_finalTCF_cs` and
`backend_correct_finalTCF_fmaNegZ` apply it to `fCs` and `fFmaNegZ`.

Checks by `native_decide` (witness only). `lake build FVTest.E2E.FloatOpsFinalTCF`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E FloatScopeFLOWitness

namespace FloatOpsFinalTCF

open FloatFinalT

/-- `CompiledTCF` of a function at `k = 0`, each stage decided. -/
local macro "compiled_tcf" f:term : tactic => `(tactic| (
  refine ⟨?_, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (lowerFunction $f).toBool = true := by native_decide
    unfold FloatDriverT.vcOf
    cases h : lowerFunction $f with
    | error e => rw [h] at hok; cases hok
    | ok vc => rfl
  · have hok : (Backend.prepare (FloatDriverT.vcOf $f)).toBool = true := by native_decide
    unfold vcpOf
    cases h : Backend.prepare (FloatDriverT.vcOf $f) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (vcpOf $f) (rfOf $f)).isOk = true := by native_decide
    cases h : checkAlloc (vcpOf $f) (rfOf $f) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (vcpOf $f) (rfOf $f)).toBool = true := by native_decide
    unfold afOf
    cases h : lowerRFunc (vcpOf $f) (rfOf $f) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (afOf $f)).toBool = true := by native_decide
    unfold faOf
    cases h : emitFunc 0 (afOf $f) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (faOf $f).layout.toBool = true := by native_decide
    unfold fbOf
    cases h : (faOf $f).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl))

/-- `backend_correct_finalTCF`'s decided premises for `f`: the subset, the compiled code, the
covered forms. -/
def Premises (f : Clif.Function) : Prop :=
  InSubsetTCF { funcs := [] } f ∧
    CompiledTCF f 0 (FloatDriverT.vcOf f) (vcpOf f) (rfOf f) (afOf f) (faOf f) (fbOf f) ∧
    FormsCovered ⟨(faOf f).k, (afOf f).slotBase⟩ (vcpOf f)

/-- **Witness**: `fcopysign.f64` meets them. -/
theorem premises_cs : Premises fCs :=
  ⟨InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl, by compiled_tcf fCs,
    (formsCoveredB_iff _ _).mp (by native_decide)⟩

/-- **Witness**: `fcopysign.f32` meets them. -/
theorem premises_cs32 : Premises fCs32 :=
  ⟨InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl, by compiled_tcf fCs32,
    (formsCoveredB_iff _ _).mp (by native_decide)⟩

/-- **Witness**: `fma.f64` meets them. -/
theorem premises_fma : Premises fFma :=
  ⟨InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl, by compiled_tcf fFma,
    (formsCoveredB_iff _ _).mp (by native_decide)⟩

/-- **Witness**: `fma.f32` with an `fneg` addend (`fnmsub`) meets them. -/
theorem premises_fmaNegZ : Premises fFmaNegZ :=
  ⟨InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl, by compiled_tcf fFmaNegZ,
    (formsCoveredB_iff _ _).mp (by native_decide)⟩

/-- **Witness**: `fma.f64` with an `fneg` first operand (`fmsub`) meets them. -/
theorem premises_fmaNegX : Premises fFmaNegX :=
  ⟨InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl, by compiled_tcf fFmaNegX,
    (formsCoveredB_iff _ _).mp (by native_decide)⟩

/-- **The typed final theorem applies to an `fcopysign`** (`fCs`): with its subset, compiled code
and form coverage discharged above, the Arm run of the compiled function (`ushr` + `sli`) refines
the CLIF run, under the remaining run/link contracts. -/
theorem backend_correct_finalTCF_cs
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk (frameW K (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase
      (RAFrame.compute (vcpOf fCs) (rfOf fCs)).size (afOf fCs) s) K X H (vcpOf fCs).CallSite)
    (hCT : (∃ B ∈ fCs.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase
        (RAFrame.compute (vcpOf fCs) (rfOf fCs)).size (afOf fCs) s) X H (vcpOf fCs).TrySite)
    (hTls : hasTls fCs = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase
        (RAFrame.compute (vcpOf fCs) (rfOf fCs)).size (afOf fCs) s) K X H)
    (hX : ∀ s, XCallsOk env (fCs.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase
        (RAFrame.compute (vcpOf fCs) (rfOf fCs)).size (afOf fCs) s, syms,
        slotOff, (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase⟩ fCs sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs fCs) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase
        (RAFrame.compute (vcpOf fCs) (rfOf fCs)).size (afOf fCs) s, syms,
        slotOff, (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase⟩ fCs sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (afOf fCs).slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (fbOf fCs) base ra s) (hres : StackAvail K (afOf fCs) s)
    (hbe : BodyEntry (afOf fCs) s w₀)
    (hargs : ArgsIn fCs.sig args s) (hcs : ClifEntry fCs args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase
      (RAFrame.compute (vcpOf fCs) (rfOf fCs)).size (afOf fCs) s,
      syms, slotOff, (RAFrame.compute (vcpOf fCs) (rfOf fCs)).intBase⟩ fCs
        cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesT (fbOf fCs) base ra (ArmStepX X H (faOf fCs)) s
      (Clif.runLoop env { funcs := [] } fuel cs) :=
  backend_correct_finalTCF premises_cs.1 premises_cs.2.1 premises_cs.2.2 hC hCT hTls hX hXI hsym
    hslot hent hres hbe hargs hcs hrel htr fuel

/-- **The typed final theorem applies to an `fma` with an `fneg` addend** (`fFmaNegZ`,
`fnmsub`), as `backend_correct_finalTCF_cs`. -/
theorem backend_correct_finalTCF_fmaNegZ
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk (frameW K (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase
      (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).size (afOf fFmaNegZ) s) K X H
      (vcpOf fFmaNegZ).CallSite)
    (hCT : (∃ B ∈ fFmaNegZ.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase
        (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).size (afOf fFmaNegZ) s) X H
        (vcpOf fFmaNegZ).TrySite)
    (hTls : hasTls fFmaNegZ = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase
        (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).size (afOf fFmaNegZ) s) K X H)
    (hX : ∀ s, XCallsOk env (fFmaNegZ.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase
        (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).size (afOf fFmaNegZ) s, syms,
        slotOff, (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase⟩ fFmaNegZ sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs fFmaNegZ) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase
        (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).size (afOf fFmaNegZ) s, syms,
        slotOff, (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase⟩ fFmaNegZ sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (afOf fFmaNegZ).slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (fbOf fFmaNegZ) base ra s) (hres : StackAvail K (afOf fFmaNegZ) s)
    (hbe : BodyEntry (afOf fFmaNegZ) s w₀)
    (hargs : ArgsIn fFmaNegZ.sig args s) (hcs : ClifEntry fFmaNegZ args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase
      (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).size (afOf fFmaNegZ) s,
      syms, slotOff, (RAFrame.compute (vcpOf fFmaNegZ) (rfOf fFmaNegZ)).intBase⟩ fFmaNegZ
        cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesT (fbOf fFmaNegZ) base ra (ArmStepX X H (faOf fFmaNegZ)) s
      (Clif.runLoop env { funcs := [] } fuel cs) :=
  backend_correct_finalTCF premises_fmaNegZ.1 premises_fmaNegZ.2.1 premises_fmaNegZ.2.2 hC hCT
    hTls hX hXI hsym hslot hent hres hbe hargs hcs hrel htr fuel

end FloatOpsFinalTCF
