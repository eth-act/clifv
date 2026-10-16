import Crates.FrontendBundleWitnessRaw
import FV.Front.RawExeUnwind
import FV.Link.ExeUnwindWitness

/-! # Non-vacuity of `Front.bundle_correct_raw_unwind` on a real codegen unit (S10f)

The bundle `bw` of `Crates.FrontendBundleWitness` (`g_u128`'s `wmul_u128` and its local callee
`wrapping_mul`), its `LinkSpec` `S`, in an executable that, beside the region's placeholder,
carries the region's unwind sections as lean-backend and rust-lld write them
(`Link.DeadCleanup.UnwindWitness.ehSegOf`: `.eh_frame_hdr` with its search table and
`PT_GNU_EH_FRAME`, `.eh_frame`, `.gcc_except_table`):

* `compile_eq`: `Link.DeadCleanup.compileExeU` (what `lake exe lean-link` decides) succeeds;
* **`bundle_unwind_witness`**: `Front.bundle_correct_raw_unwind` instantiated at cg_clif's
  `wmul_u128` (`Crates.FrontendBundleWitnessRaw`'s naming `scd`): `compileExe` succeeds (so
  `bundle_correct_raw` applies), `wmul_u128`'s compiled function is a function of the compiled
  program, and `UnwindStmt` holds for the executable.
-/

namespace Crates.FrontendBundleUnwindWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary Backend Opt.Legalize128
open Crates.FrontendBundleWitness (bw S buildSpec_eq us hus f0)
open Crates.FrontendBundleWitnessRaw (scd scd_ok rawLink_eq)
open Crates.CompileExeSourceWitness (n)
open Link.DeadCleanup.UnwindWitness (exeWith ehSegOf gccOf)

/-- The compiled functions. -/
def arts : List Art := (tabOf (Link.DeadCleanup.parResultsCleanupT S.input0)).map (·.2)

/-- **The executable before the compiler**: the region's placeholder, the unwind sections,
the link map's symbols. -/
def file0 : ByteArray :=
  exeWith S.R S.size
    [(0x2000000, ehSegOf arts 0x2000000 0x2100000 0x2200000), (0x2100000, (gccOf arts).1 ++ [0, 0, 0, 0])]
    (12 + 8 * arts.length) (S.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem compile_ok : (Link.DeadCleanup.compileExeU S file0).toBool = true := by native_decide

def file : ByteArray := getOk (Link.DeadCleanup.compileExeU S file0)

theorem compile_eq : Link.DeadCleanup.compileExeU S file0 = .ok file := getOk_eq compile_ok

theorem raw_f : (Front.rawLink us scd).func? n = some f0 := by
  rw [rawLink_eq]; exact Crates.FrontendBundleWitness.hf0

/-- **`Front.bundle_correct_raw_unwind` on cg_clif's `wmul_u128`.** -/
theorem bundle_unwind_witness : ∃ σ : Clif.Ren,
    Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd ∧
    Link.DeadCleanup.compileExe S file0 = .ok file ∧
    legalize (f0.rename σ.fwd) ∈ (prog S.inputCleanup).funcs ∧
    Link.DeadCleanup.UnwindStmt S file := by
  obtain ⟨σ, hσ, -⟩ := Crates.FrontendBundleWitness.alpha
  rw [← rawLink_eq] at hσ
  exact ⟨σ, hσ, Front.bundle_correct_raw_unwind buildSpec_eq compile_eq hus scd_ok hσ raw_f⟩

end Crates.FrontendBundleUnwindWitness
