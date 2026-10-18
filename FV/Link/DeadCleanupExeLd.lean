import FV.Link.DeadCleanupOptExe
import FV.Link.Ld.Spec

/-! # The shipped executable compiler is total on `lean-ld`'s output (L2b stage 3e)

`Link.DeadCleanup.compileExe_total_reach_input` and `compileExeOpt_total_reach_input` with
`lean-ld` (`Link.Ld.link`) as the linker: `file0OkB` is `Link.Ld.file0OkB_ld`, from a successful
link whose plan agrees with the link spec (`Plan.specOkB`). The cleanup files are unchanged.
-/

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec Ld

/-- **The shipped executable compiler succeeds on `lean-ld`'s output**
(`compileExe_total_reach_input` with `file0OkB_ld`). -/
theorem compileExe_total_ld {S : LinkSpec} {o : Opts} {ins : List Input} {r : LinkOut}
    (hin : InScopeIn (placed S).input0 = true) (hl : (placed S).layoutOkB = true)
    (hld : link o ins = .ok r) (hP : r.plan.specOkB (placed S) = true)
    (hreach : (placed S).reachOkB = true) :
    compileExe (placed S) r.img.write =
      .ok (patch r.img.write (offsetOf r.img.phs S.R) (regionOf (placed S) (tpOff r.img.phs))) :=
  compileExe_total_reach_input hin hl (phdrs_write (link_ok hld).2.1) (file0OkB_ld hld hP) hreach

/-- **The shipped optimising executable compiler succeeds on `lean-ld`'s output**
(`compileExeOpt_total_reach_input` with `file0OkB_ld`). -/
theorem compileExeOpt_total_ld {S : LinkSpec} {o : Opts} {ins : List Input} {r : LinkOut}
    (hin : InScopeIn (placed S.opt).input0 = true) (hl : (placed S.opt).layoutOkB = true)
    (hld : link o ins = .ok r) (hP : r.plan.specOkB (placed S.opt) = true)
    (hreach : (placed S.opt).reachOkB = true) :
    compileExeOpt (S.withSizes (sizesOf S.opt)) r.img.write =
      .ok (patch r.img.write (offsetOf r.img.phs S.R) (regionOf (placed S.opt) (tpOff r.img.phs))) :=
  compileExeOpt_total_reach_input hin hl (phdrs_write (link_ok hld).2.1) (file0OkB_ld hld hP) hreach

end Link.DeadCleanup
