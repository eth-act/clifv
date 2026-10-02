import FV.Backend.Proof.PrepareSound
import FV.Backend.Proof.PrepareComplete

/-!
# `prepare` is correct (M7, no validator)

`prepCheck` is complete on `PrepDomain` VCode (`PrepareComplete.prepCheck_complete`) and sound
(`PrepareSound.prep_sound`), so `prepare` itself preserves returns and traps, keeps the outgoing
argument area and introduces no `tryCall`/`ElfTlsGetAddr`. The backend still runs `prepCheck`
after `prepare` (`Backend.allocateRegalloc2`), now a double-check that cannot fail on
`PrepDomain` VCode.
-/

namespace Backend.Proof.Prep

open Backend Backend.Proof Backend.Proof.Driver

/-- **`prepare` is correct**: on `PrepDomain` VCode, every VCode return and every trap of `vc`
(from the entry) is one of `prepare vc`, for a semantics satisfying `DriverSem`. -/
theorem prepare_correct {vc vcp : VCode} {sem : Sem} (hds : DriverSem sem)
    (h : prepare vc = .ok vcp) (hd : PrepDomain vc) (ρ₀ : Nat → CV) (w₀ : Arm.ArmState) :
    (∀ us vals w, VRetFrom vc sem ⟨0, 0, ρ₀, w₀⟩ us vals w →
      VRetFrom vcp sem ⟨0, 0, ρ₀, w₀⟩ us vals w) ∧
    (∀ c, VTrapFrom vc sem ⟨0, 0, ρ₀, w₀⟩ c → VTrapFrom vcp sem ⟨0, 0, ρ₀, w₀⟩ c) :=
  prep_sound hds (prepCheck_complete h hd) ρ₀ w₀

/-- `prepare` keeps the outgoing argument area. -/
theorem prepare_outgoing {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : PrepDomain vc) :
    vcp.outgoing = vc.outgoing :=
  outgoing_of_prepCheck (prepCheck_complete h hd)

/-- `prepare` introduces no `tryCall`. -/
theorem prepare_noTryCall {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : PrepDomain vc)
    (hvc : vc.hasTryCall = false) : vcp.hasTryCall = false :=
  noTryCall_of_prepCheck (prepCheck_complete h hd) hvc

/-- `prepare` introduces no `ElfTlsGetAddr`. -/
theorem prepare_noTls {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : PrepDomain vc)
    (hvc : vc.hasTls = false) : vcp.hasTls = false :=
  noTls_of_prepCheck (prepCheck_complete h hd) hvc

end Backend.Proof.Prep
