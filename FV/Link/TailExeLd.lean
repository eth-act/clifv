import FV.Link.TailExe
import FV.Link.Ld.Spec

/-! # The executable compiler with self tail calls as loops is total on `lean-ld`'s output (S8)

`Link.DeadCleanup.compileExeTail_total_reach_input` with `lean-ld` (`Link.Ld.link`) as the linker:
`file0OkB` is `Link.Ld.file0OkB_ld`, from a successful link whose plan agrees with the link spec
(`Plan.specOkB`), as `Link.DeadCleanup.compileExeOpt_total_ld` (`FV/Link/DeadCleanupExeLd.lean`).
-/

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec Ld

/-- **The executable compiler with self tail calls as loops succeeds on `lean-ld`'s output**
(`compileExeTail_total_reach_input` with `file0OkB_ld`). -/
theorem compileExeTail_total_ld {S : LinkSpec} {o : Opts} {ins : List Input} {r : LinkOut}
    (hin : InScopeIn (placed S.tail).input0 = true) (hl : (placed S.tail).layoutOkB = true)
    (hld : link o ins = .ok r) (hP : r.plan.specOkB (placed S.tail) = true)
    (hreach : (placed S.tail).reachOkB = true) :
    compileExeTail (S.withSizes (sizesOf S.tail)) r.img.write =
      .ok (patch r.img.write (offsetOf r.img.phs S.R) (regionOf (placed S.tail) (tpOff r.img.phs))) :=
  compileExeTail_total_reach_input hin hl (phdrs_write (link_ok hld).2.1) (file0OkB_ld hld hP) hreach

end Link.DeadCleanup
