import Crates.FrontendBundleWitnessRaw
import FV.Front.ExeT

/-! # Non-vacuity of the typed frontend theorems on a real codegen unit (S11e6, #419)

The bundle `bw`, `LinkSpec` `S`, executable and scopings of `Crates.FrontendBundleWitness` and
`Crates.FrontendBundleWitnessRaw` (cg_clif's dumps of `wmul_u128` and the local `wrapping_mul` of
the survey crate `g_u128`). `Link.DeadCleanup.compileExeT` is `compileExe` on this integer input
(`compileExeT_eq`), so it succeeds, and the bundle-level premises of `Front.bundle_correct_sourceT`,
`Front.bundle_correct_source_peakT`, `Front.bundle_correct_rawT` and `Front.bundle_correct_raw_peakT`
(the bundle's `LinkSpec`, the compiler's success, the source domain, the parsed units and the
scoping / raw naming) are discharged; the instantiated theorems (`*_spec`) are witnesses.
-/

namespace Crates.FrontendBundleWitnessT

open Crates.FrontendBundleWitness
open Crates.FrontendBundleWitnessRaw (scd scd_ok)

/-- `compileExeT` succeeds on the bundle's `LinkSpec` (the integer branch). -/
theorem compileT_eq : Link.DeadCleanup.compileExeT S file0 = .ok file := by
  rw [Link.DeadCleanup.compileExeT_eq inScope]
  exact compile_eq

/-- The bundle's program is in the source domain. -/
theorem hsrc : E2E.LinkCheck.SrcScopeB S.inputCleanup = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    FrontendBundleWitness.facts
  exact h

/-- **Witness**: `Front.bundle_correct_sourceT` applies to the bundle. -/
theorem sourceT_spec :
    type_of% (@Front.bundle_correct_sourceT bw S file0 file buildSpec_eq compileT_eq hsrc us hus
      sc) :=
  @Front.bundle_correct_sourceT bw S file0 file buildSpec_eq compileT_eq hsrc us hus sc

/-- **Witness**: `Front.bundle_correct_source_peakT` applies to the bundle. -/
theorem source_peakT_spec :
    type_of% (@Front.bundle_correct_source_peakT bw S file0 file buildSpec_eq compileT_eq hsrc us
      hus sc) :=
  @Front.bundle_correct_source_peakT bw S file0 file buildSpec_eq compileT_eq hsrc us hus sc

/-- **Witness**: `Front.bundle_correct_rawT` applies to cg_clif's program of the bundle. -/
theorem rawT_spec :
    type_of% (@Front.bundle_correct_rawT bw S file0 file buildSpec_eq compileT_eq hsrc us hus scd
      scd_ok) :=
  @Front.bundle_correct_rawT bw S file0 file buildSpec_eq compileT_eq hsrc us hus scd scd_ok

/-- **Witness**: `Front.bundle_correct_raw_peakT` applies to cg_clif's program of the bundle. -/
theorem raw_peakT_spec :
    type_of% (@Front.bundle_correct_raw_peakT bw S file0 file buildSpec_eq compileT_eq hsrc us hus
      scd scd_ok) :=
  @Front.bundle_correct_raw_peakT bw S file0 file buildSpec_eq compileT_eq hsrc us hus scd scd_ok

end Crates.FrontendBundleWitnessT
