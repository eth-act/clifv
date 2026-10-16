import FV.Link.ExeInputReachCleanup
import FV.E2E.LinkScopeInput

/-! # The shipped compiler is total on input conditions decided without compiling (V7)

`Link.DeadCleanup.compileExe_total_reach` (`FV/Link/ExeInputReachCleanup.lean`) with `InScopeIn`
(`FV/E2E/LinkScopeInputDefs.lean`) for `InScopeP` (`E2E.LinkCheck.inScopeP_of_input`). The
cleanup pipeline's `prepare (prune vc)` needs no further condition: it succeeds from
`prepare vc` (`prune_prepare_ok`), which `Prep.prepare_ok` proves. The cleanup files are
unchanged.
-/

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- **The shipped compiler succeeds on input conditions decided without compiling**
(`compileExe_total_reach` with `InScopeIn`). -/
theorem compileExe_total_reach_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn (placed S).input0 = true) (hl : (placed S).layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : (placed S).file0OkB file0 phs = true)
    (hreach : (placed S).reachOkB = true) :
    compileExe (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs))) :=
  compileExe_total_reach (inScopeP_of_input hin) hl hph hf hreach

end Link.DeadCleanup
