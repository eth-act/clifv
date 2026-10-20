import FV.Link.ExeInputReach
import FV.E2E.LinkScopeInput

/-! # The executable compiler is total on input conditions decided without compiling (V7)

`Link.compileExe_total_reach` (`FV/Link/ExeInputReach.lean`) takes `InScopeP`, whose per-function
conjunct `lowersB` is decided by running `lowerFunction` and `prepare`. Here it takes `InScopeIn`
(`FV/E2E/LinkScopeInputDefs.lean`): conditions on the CLIF functions alone, the lowering's and
`prepare`'s success proven (`E2E.LinkCheck.inScopeP_of_input`). The shipped compiler:
`FV/Link/ExeInputReachCleanupIn.lean`.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- **The executable compiler succeeds on input conditions decided without compiling**: on the
CLIF input (`InScopeIn`), the layout (`layoutOkB`), the reach of the CLIF functions' references
from the region (`reachOkB`), rust-lld's executable `file0` (`file0OkB`), with the Lean
compiler's layout (`S.placed`). -/
theorem compileExe_total_reach_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn S.placed.input0 = true) (hl : S.placed.layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : S.placed.file0OkB file0 phs = true)
    (hreach : S.placed.reachOkB = true) :
    compileExe S.placed file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf S.placed (tpOff phs))) :=
  compileExe_total_reach (inScopeP_of_input hin) hl hph hf hreach

end Link
