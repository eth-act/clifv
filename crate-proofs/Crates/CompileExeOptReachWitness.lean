import Crates.CompileExeWitness
import FV.Link.DeadCleanupOptExe

/-! # Non-vacuity of the optimising executable compiler's totality on input conditions (S1, S2)

`total_reach_opt_witness`: every hypothesis of `Link.compileExeOpt_total_reach_input` holds on
`a_arith`'s 58 functions (`Crates.LeanLinkWitness.spec`), on which the mid-end changes every
function (`changed`) and every optimised function prints and parses back (`noFallbacks`): the
input conditions `InScopeIn`, the layout and the reach of the optimised functions' references
from the region (`layoutOkB`, `reachOkB`), all with the sizes of the optimised functions'
compiled code (`S.opt.placed`), and an executable with a `PT_TLS` segment for that layout
(`file0O`, `Crates.CompileExeWitness.placeholderTls`). `total_reach_opt_cleanup_witness`: the same
for the shipped compiler (`Link.DeadCleanup.compileExeOpt_total_reach_input`).
-/

namespace Crates.CompileExeOptReachWitness

open E2E E2E.LinkCheck Link Crates.LeanLinkWitness Crates.CompileExeWitness

/-- The mid-end changes every function of `a_arith`. -/
theorem changed : (spec.funcs.zip spec.opt.funcs).all (fun p => decide (p.1.func ≠ p.2.func)) =
    true := by native_decide

/-- Every optimised function prints and parses back. -/
theorem noFallbacks : spec.optFallbacks = [] := by native_decide

/-- rust-lld's executable for the layout of the optimised `a_arith`. -/
def file0O : ByteArray :=
  placeholderTls spec.R spec.opt.placed.size
    (spec.opt.placed.addrs.map fun p => (BinCheck.symName p.1, p.2))

def phsO : List Elf.Phdr := (Elf.phdrs (Elf.fileRd file0O)).getD []

theorem hphO : Elf.phdrs (Elf.fileRd file0O) = some phsO := by native_decide

theorem inScopeO : InScopeIn spec.opt.placed.input0 = true := by native_decide

theorem layoutO : spec.opt.placed.layoutOkB = true := by native_decide

theorem file0O_ok : spec.opt.placed.file0OkB file0O phsO = true := by native_decide

theorem reachO : spec.opt.placed.reachOkB = true := by native_decide

/-- **Non-vacuity of `compileExeOpt_total_reach_input`** on `a_arith`. -/
theorem total_reach_opt_witness :
    compileExeOpt (spec.withSizes spec.opt.sizesOf) file0O =
      .ok (patch file0O (offsetOf phsO spec.R) (regionOf spec.opt.placed (Elf.tpOff phsO))) :=
  compileExeOpt_total_reach_input inScopeO layoutO hphO file0O_ok reachO

/-- rust-lld's executable for the shipped compiler's layout of the optimised `a_arith`. -/
def file0OC : ByteArray :=
  placeholderTls spec.R (DeadCleanup.placed spec.opt).size
    ((DeadCleanup.placed spec.opt).addrs.map fun p => (BinCheck.symName p.1, p.2))

def phsOC : List Elf.Phdr := (Elf.phdrs (Elf.fileRd file0OC)).getD []

theorem hphOC : Elf.phdrs (Elf.fileRd file0OC) = some phsOC := by native_decide

theorem inScopeOC : InScopeIn (DeadCleanup.placed spec.opt).input0 = true := by native_decide

theorem layoutOC : (DeadCleanup.placed spec.opt).layoutOkB = true := by native_decide

theorem file0OC_ok : (DeadCleanup.placed spec.opt).file0OkB file0OC phsOC = true := by
  native_decide

theorem reachOC : (DeadCleanup.placed spec.opt).reachOkB = true := by native_decide

/-- **Non-vacuity of `DeadCleanup.compileExeOpt_total_reach_input`** on `a_arith`. -/
theorem total_reach_opt_cleanup_witness :
    DeadCleanup.compileExeOpt (spec.withSizes (DeadCleanup.sizesOf spec.opt)) file0OC =
      .ok (patch file0OC (offsetOf phsOC spec.R)
        (DeadCleanup.regionOf (DeadCleanup.placed spec.opt) (Elf.tpOff phsOC))) :=
  DeadCleanup.compileExeOpt_total_reach_input inScopeOC layoutOC hphOC file0OC_ok reachOC

end Crates.CompileExeOptReachWitness
