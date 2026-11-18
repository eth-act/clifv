import Crates.FrontendBundleInput
import Crates.LeanLinkWitness
import FV.Front.ExeTCp
import FV.Front.RawExe

/-! # Non-vacuity of the typed frontend theorems where constant-phi removal changes a function (#1088)

`Crates.FrontendBundleWitnessTCp` instantiates `Front.bundle_correct_{source,raw}{,_peak}TCp` on a
bundle that constant-phi removal leaves unchanged. Here the bundle `bc` holds one codegen unit with
one function in the patched cg_clif's dump format (the dump header of `Crates.FrontendBundleInput`'s
`wmul_u128`, an external-name table): `cpwit(v0: i64) -> i64`, whose `block1(v2)` receives only
the constant `v1 = iconst.i64 7` from `block0`, so constant-phi removal changes it
(`S0.cpChanged = ["cpwit"]`: `block1` loses its parameter, `v3 = iadd v0, v1`).

As in `lean-link` on the `compileExeT` route: `S0` is `buildSpec bc`, the compiled spec `S` is the
cleanup placement of `S0.cp` (`TypedStockShared.placedFrom S0.cp A`, `A` the cleanup results of
`S0.cp`), so `hcp` holds by `rfl` (`Front.placedFrom_cp_funcs`), `S`'s function is NOT `S0`'s
(`changed`), and `compileExeT S file0` succeeds on the region placeholder of
`Crates.LeanLinkWitness`. The remaining bundle-level premises (`SrcScopeB S0.input0`, the parsed
units, the scoping, the raw naming) are discharged; the instantiated theorems (`*_spec`) are
witnesses. Decided by `native_decide` (witness only).
-/

namespace Crates.FrontendBundleWitnessTCpChanged

open E2E E2E.LinkCheck Backend Backend.Proof
open Link (LinkSpec)

/-- The patched cg_clif's dump header (settings, target), from a real dump. -/
def hdr : String :=
  (Crates.FrontendBundleInput.fn26.dump.splitOn "; symbol wmul_u128\nfunction").headD ""

/-- `cpwit` in the patched cg_clif's dump format: `block1`'s parameter is the constant `7`. -/
def cpDump : String := hdr ++ "; symbol cpwit\nfunction u0:0(i64) -> i64 system_v {\n; symbol cpwit\n\nblock0(v0: i64):\n    v1 = iconst.i64 7\n    jump block1(v1)\n\nblock1(v2: i64):\n    v3 = iadd v0, v2\n    return v3\n}\n\n; clifv-extnames 1\n; decl u0:0 func export \"cpwit\"\n; end clifv-extnames\n"

/-- The codegen unit: `cpwit` only (no data object; no regalloc2 answer: the spill allocation). -/
def unit0 : Front.Cgu :=
  { tag := "cp0", funcs := [{ name := "cpwit", dump := cpDump, ra := "null" }], data := [],
    locals := [], names := [] }

/-- The bundle without the sizes: `cpwit`'s Lean code at 16 MiB. -/
def b0 : Front.Bundle :=
  { units := [unit0], symbols := [("cpwit", 0x400000)], markers := [("cpwit", 0x1000000)],
    sizes := [] }

/-- The cleanup pipeline's sizes of the assembled functions, by linked name. -/
def sizes0 : List (String × Nat) :=
  match Front.assemble b0 with
  | .ok A => A.names.zip (A.funcs.map fun fi =>
      (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size)
  | .error _ => []

/-- **The bundle.** -/
def bc : Front.Bundle := { b0 with sizes := sizes0 }

theorem buildSpec_ok : (Front.buildSpec bc).toBool = true := by native_decide -- witness: native_decide

/-- The bundle's `LinkSpec`. -/
def S0 : LinkSpec := getOk (Front.buildSpec bc)

theorem buildSpec_eq : Front.buildSpec bc = .ok S0 := getOk_eq buildSpec_ok

/-- The spec `lean-link` compiles on the `compileExeT` route: the cleanup placement of `S0.cp`. -/
def S : LinkSpec :=
  Link.TypedStockShared.placedFrom S0.cp (Link.TypedStockShared.cleanupArts S0.cp)

/-- `lean-link`'s `hcp`. -/
theorem hcp : S.funcs = S0.input0.funcs.map FnInput.cp := Front.placedFrom_cp_funcs _ _

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder S.R S.size (S.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem compileT_ok : (Link.DeadCleanup.compileExeT S file0).toBool = true := by
  native_decide -- witness: native_decide

/-- The executable. -/
def file : ByteArray := getOk (Link.DeadCleanup.compileExeT S file0)

/-- **The typed executable compiler compiles the placed constant-phi removal.** -/
theorem compileT_eq : Link.DeadCleanup.compileExeT S file0 = .ok file := getOk_eq compileT_ok

/-- The bundle's program is in the source domain. -/
theorem hsrc : SrcScopeB S0.input0 = true := by native_decide -- witness: native_decide

/-- **Constant-phi removal changes `cpwit`**: the compiled spec's function is not the bundle's. -/
theorem changed : S0.cpChanged = ["cpwit"] ∧ S.funcs ≠ S0.input0.funcs := by
  have h1 : S0.cpChanged = ["cpwit"] := by native_decide -- witness: native_decide
  have h2 : ((S.funcs.headD default).clif != (S0.input0.funcs.headD default).clif) = true := by
    native_decide -- witness: native_decide
  refine ⟨h1, fun h => ?_⟩
  rw [h] at h2
  simp at h2

theorem units_ok : (bc.units.mapM Front.parseUnit).toBool = true := by native_decide -- witness: native_decide

/-- The parsed units. -/
def us : List Front.PCgu := getOk (bc.units.mapM Front.parseUnit)

theorem hus : bc.units.mapM Front.parseUnit = .ok us := getOk_eq units_ok

/-- The pre-renaming scoping: every name as the frontend wrote it. -/
def sc : Nat → String → String := fun _ x => x

theorem sc_ok : Front.ScopingOk us sc := Front.scopingDecB_sound (by native_decide) -- witness: native_decide

/-- The declarations' naming of cg_clif's program. -/
def scd : Nat → String → String :=
  fun i a => match us[i]? with | some u => sc i (u.ren a) | none => sc i a

theorem scd_ok : Front.RawScopingOk us scd := Front.rawScoping_of (Front.units_ok hus) sc_ok

/-- **Witness**: `Front.bundle_correct_sourceTCp` applies where constant-phi removal changes the
compiled function. -/
theorem sourceTCp_spec :
    type_of% (@Front.bundle_correct_sourceTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq hsrc
      us hus sc) :=
  @Front.bundle_correct_sourceTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq hsrc us hus sc

/-- **Witness**: `Front.bundle_correct_source_peakTCp`, same instance. -/
theorem source_peakTCp_spec :
    type_of% (@Front.bundle_correct_source_peakTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq
      hsrc us hus sc) :=
  @Front.bundle_correct_source_peakTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq hsrc us hus
    sc

/-- **Witness**: `Front.bundle_correct_rawTCp` applies to cg_clif's program of the bundle. -/
theorem rawTCp_spec :
    type_of% (@Front.bundle_correct_rawTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq hsrc us
      hus scd scd_ok) :=
  @Front.bundle_correct_rawTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq hsrc us hus scd
    scd_ok

/-- **Witness**: `Front.bundle_correct_raw_peakTCp`, same instance. -/
theorem raw_peakTCp_spec :
    type_of% (@Front.bundle_correct_raw_peakTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq hsrc
      us hus scd scd_ok) :=
  @Front.bundle_correct_raw_peakTCp bc S0 S file0 file buildSpec_eq hcp compileT_eq hsrc us hus scd
    scd_ok

end Crates.FrontendBundleWitnessTCpChanged
