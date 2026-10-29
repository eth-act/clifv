module

public import FV.Link.ExeInputReach
public import FV.Link.OptExe
public import FV.Link.Ld.Spec

@[expose] public section

/-! # The executable compiler is total on `lean-ld`'s output (L2b stage 3e)

`compileExe_total_reach` and `compileExeOpt_total_reach_input` ask of the executable `file0` the
outside part is linked into that it pass `file0OkB`, checks of the linker's output. With
`lean-ld` (`Link.Ld.link`, `lake exe lean-ld`) as the linker, `file0OkB` is a theorem
(`Link.Ld.file0OkB_ld`): the premises are that the link succeeded and that the link spec agrees
with `lean-ld`'s plan (`Plan.specOkB`, decided on the plan and the spec, not on the output's
bytes).

* `compileExe_total_ld`: `compileExe` succeeds on `lean-ld`'s output;
* `compileExeOpt_total_ld`: `compileExeOpt` likewise.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec Ld

/-- **The executable compiler succeeds on `lean-ld`'s output**: on the CLIF input (`InScopeIn`),
the layout (`layoutOkB`), the reach of the CLIF functions' references from the region
(`reachOkB`), a successful `lean-ld` link whose plan agrees with the link spec
(`Plan.specOkB`), with the Lean compiler's layout (`S.placed`). -/
theorem compileExe_total_ld {S : LinkSpec} {o : Opts} {ins : List Input} {r : LinkOut}
    (hin : InScopeIn S.placed.input0 = true) (hl : S.placed.layoutOkB = true)
    (hld : link o ins = .ok r) (hP : r.plan.specOkB S.placed = true)
    (hreach : S.placed.reachOkB = true) :
    compileExe S.placed r.img.write =
      .ok (patch r.img.write (offsetOf r.img.phs S.R) (regionOf S.placed (tpOff r.img.phs))) :=
  compileExe_total_reach hin hl (phdrs_write (link_ok hld).2.1) (file0OkB_ld hld hP) hreach

/-- **The optimising executable compiler succeeds on `lean-ld`'s output**
(`compileExeOpt_total_reach_input` with `file0OkB_ld`). -/
theorem compileExeOpt_total_ld {S : LinkSpec} {o : Opts} {ins : List Input} {r : LinkOut}
    (hin : InScopeIn S.opt.placed.input0 = true) (hl : S.opt.placed.layoutOkB = true)
    (hld : link o ins = .ok r) (hP : r.plan.specOkB S.opt.placed = true)
    (hreach : S.opt.placed.reachOkB = true) :
    compileExeOpt (S.withSizes (sizesOf S.opt)) r.img.write =
      .ok (patch r.img.write (offsetOf r.img.phs S.R) (regionOf S.opt.placed (tpOff r.img.phs))) :=
  compileExeOpt_total_reach_input hin hl (phdrs_write (link_ok hld).2.1) (file0OkB_ld hld hP) hreach

end Link
