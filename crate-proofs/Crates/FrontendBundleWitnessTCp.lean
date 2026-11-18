import Crates.FrontendBundleWitnessT
import FV.Front.ExeTCp

/-! # Non-vacuity of the typed frontend theorems through constant-phi removal (#1088)

The bundle `bw` and spec `S` of `Crates.FrontendBundleWitness` (cg_clif's dumps of `wmul_u128` and
the local `wrapping_mul` of the survey crate `g_u128`), `compileExeT S file0 = .ok file`
(`Crates.FrontendBundleWitnessT.compileT_eq`). Constant-phi removal keeps both functions here, so
`S` is its own constant-phi removal (`hcp`, evaluated) and the bundle-level premises of
`Front.bundle_correct_{source,raw}{,_peak}TCp` (`buildSpec bw = .ok S`, `hcp`, the compiler's
success, `SrcScopeB S.input0`, the parsed units and the scoping / raw naming) are discharged; the
instantiated theorems (`*_spec`) are witnesses. `Crates.FrontendBundleWitnessTCpChanged`
instantiates the same theorems where constant-phi removal changes the compiled function.
-/

namespace Crates.FrontendBundleWitnessTCp

open Crates.FrontendBundleWitness
open Crates.FrontendBundleWitnessRaw (scd scd_ok)
open E2E.LinkCheck

deriving instance DecidableEq for FnInput

/-- Constant-phi removal keeps the bundle's functions. -/
theorem hcp : S.funcs = S.input0.funcs.map FnInput.cp := by
  native_decide -- witness: native_decide

/-- The bundle's program is in the source domain. -/
theorem hsrc0 : SrcScopeB S.input0 = true := by native_decide -- witness: native_decide

/-- **Witness**: `Front.bundle_correct_sourceTCp` applies to the bundle. -/
theorem sourceTCp_spec :
    type_of% (@Front.bundle_correct_sourceTCp bw S S file0 file buildSpec_eq hcp
      FrontendBundleWitnessT.compileT_eq hsrc0 us hus sc) :=
  @Front.bundle_correct_sourceTCp bw S S file0 file buildSpec_eq hcp
    FrontendBundleWitnessT.compileT_eq hsrc0 us hus sc

/-- **Witness**: `Front.bundle_correct_source_peakTCp` applies to the bundle. -/
theorem source_peakTCp_spec :
    type_of% (@Front.bundle_correct_source_peakTCp bw S S file0 file buildSpec_eq hcp
      FrontendBundleWitnessT.compileT_eq hsrc0 us hus sc) :=
  @Front.bundle_correct_source_peakTCp bw S S file0 file buildSpec_eq hcp
    FrontendBundleWitnessT.compileT_eq hsrc0 us hus sc

/-- **Witness**: `Front.bundle_correct_rawTCp` applies to cg_clif's program of the bundle. -/
theorem rawTCp_spec :
    type_of% (@Front.bundle_correct_rawTCp bw S S file0 file buildSpec_eq hcp
      FrontendBundleWitnessT.compileT_eq hsrc0 us hus scd scd_ok) :=
  @Front.bundle_correct_rawTCp bw S S file0 file buildSpec_eq hcp
    FrontendBundleWitnessT.compileT_eq hsrc0 us hus scd scd_ok

/-- **Witness**: `Front.bundle_correct_raw_peakTCp` applies to cg_clif's program of the bundle. -/
theorem raw_peakTCp_spec :
    type_of% (@Front.bundle_correct_raw_peakTCp bw S S file0 file buildSpec_eq hcp
      FrontendBundleWitnessT.compileT_eq hsrc0 us hus scd scd_ok) :=
  @Front.bundle_correct_raw_peakTCp bw S S file0 file buildSpec_eq hcp
    FrontendBundleWitnessT.compileT_eq hsrc0 us hus scd scd_ok

end Crates.FrontendBundleWitnessTCp
