import FVTest.Link.Coverage
import FV.E2E.LegalProgramT
import FV.Front.ExeTCp
import FV.Link.DeadCleanupCompileT
import FV.Link.DeadCleanupCompileT3
import FV.Link.DeadCleanupExe
import FV.Link.DeadCleanupExeLd
import FV.Link.DeadCleanupExePeak
import FV.Link.DeadCleanupExePeakT
import FV.Link.DeadCleanupExeSourceCp
import FV.Link.DeadCleanupExeSourceTCp
import FV.Link.DeadCleanupOptExe
import FV.Link.DeadCleanupOptExeSourceCp
import FV.Link.Exe
import FV.Link.ExeInputReach
import FV.Link.ExeInputReachCleanup
import FV.Link.ExeInputReachCleanupIn
import FV.Link.ExeLd
import FV.Link.ExeLdIn
import FV.Link.ExeSourceCp
import FV.Link.ExeUnwind
import FV.Link.Ld.Spec
import FV.Link.MidSourceRoutes
import FV.Link.MidSourceRoutesSyms
import FV.Link.MidSourceTB
import FV.Link.MidSourceTBSyms
import FV.Link.OptExe
import FV.Link.OptExeSourceCp
import FV.Link.OptExeUnwind
import FV.Link.ProductionExe
import FV.Link.ProductionExeWith
import FV.Link.ReturnPinExeSourceCp
import FV.Link.ReturnPinExeWith
import FV.Link.SemanticCompileT
import FV.Link.SemanticCompileWith
import FV.Link.SemanticExeSourceCp
import FV.Link.SemanticExeSourceTB
import FV.Link.SemanticExeSourceTCp
import FV.Link.SemanticExeWith
import FV.Link.TailExe
import FV.Link.TailExeLd
import FV.Link.TypedCompileModes
import FV.Link.TypedCompileSourceCp

/-! # Tests of `lean-link`'s claim table (#1104)

Every theorem name `FVTest.Link.Coverage` can produce exists and is a theorem (as
`FVTest.E2E.BinVerdictTest`, `FVTest.Backend.FnVerdictTest`); a false premise names no theorem.
`lake build FVTest.Link.CoverageTest`. -/

namespace FVTest.Link.CoverageTest

open Lean Elab Command FVTest.Link.Coverage

-- every name of the route table is a declared theorem
run_cmd do
  let env ← getEnv
  for (what, ns) in routeClaims do
    for n in ns do
      match env.find? n.toName with
      | some (.thmInfo _) => pure ()
      | some _ => throwError "{what}: {n} is not a theorem"
      | none => throwError "{what}: {n} does not exist"

-- the table covers every route, and every printed claim takes its names from it
#guard allRoutes.length = 12
#guard allRoutes.all fun r => r.claim.thms.all fun n => routeClaims.any (·.2.contains n)
#guard allRoutes.all fun r => r.writtenClaim.thms.all fun n => routeClaims.any (·.2.contains n)
-- a false premise names no theorem
#guard (Route.stock.source false).text = "no theorem is named (SrcScopeB of the bundle's program fails)"
#guard (Route.stock.source true).text =
  "Link.SemanticCompilerWith.attempt_correct_sourceCp, Link.SemanticCompilerWith.attempt_correct_source_peakCp"
#guard ((Route.exe true .tail).source true).holds = false
#guard ((Route.exe true .tail).source true).text = "no theorem is named (a source theorem for this route fails)"
#guard (unwindClaim false false).text = "no theorem is named (Link.DeadCleanup.unwOkB fails)"
#guard (unwindClaim false false).pick (fun n => n) = ""
#guard (totalLdClaim true .plain false).pick (fun n => n) "x" = "x"
#guard (sourceTBClaim false true).text = "no theorem is named (SrcScopeTB of the route's input fails)"
#guard srcText .returnPin false = "; outside SrcScopeB: about the legalised program only"
#guard srcText (.exe true .tail) true = "; in SrcScopeB, but no source theorem is named for this compiler"
#guard ({ thms := ["a", "b"], premises := [("p", true), ("q", false)] } : Claim).text =
  "no theorem is named (q fails)"
-- the printed fragments of the gate's routes
#guard (Route.exe true .plain).claim.names =
  "Link.DeadCleanup.compileExe_correct, Link.DeadCleanup.compileExe_correct_peak"
#guard (Route.totalClaim false .plain).names = "Link.compileExe_total_reach"
#guard (Route.totalClaim false .opt).names = "Link.compileExeOpt_total_reach_input"
#guard midName "X.attempt_correct_sourceCp, X.attempt_correct_source_peakCp" =
  "X.attempt_correct_sourceMid, X.attempt_correct_source_peakMid"
#guard midNameS "X.attempt_correct_sourceCp, X.attempt_correct_source_peakCp" =
  "X.attempt_correct_sourceMidS, X.attempt_correct_source_peakMidS"
#guard shortName totalLdInThm = "compileExe_total_ldIn"

end FVTest.Link.CoverageTest
