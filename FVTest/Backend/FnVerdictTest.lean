import FVTest.Backend.FnVerdict
import FV.E2E.DeadCleanupFinal
import FV.E2E.Final
import FV.E2E.CompiledSemanticReturnPins
import FV.E2E.LegalWideCleanup
import FV.E2E.Legal
import FV.E2E.PassX
import FV.E2E.OptX
import FV.E2E.LegalOptX
import FV.E2E.DeadCleanupT
import FV.E2E.FinalT
import FV.E2E.DeadCleanupPairTC
import FV.E2E.FinalTC
import FV.E2E.FinalTCF
import FV.E2E.DeadCleanupUnwindFinal
import FV.E2E.FinalUnwind
import FV.E2E.LegalUnwind
import FV.E2E.OptUnwind
import FV.E2E.LegalOptUnwind

/-! # Tests of `lean-backend`'s per-function verdict (#1096)

Every theorem name `FVTest.Backend.FnVerdict` can produce exists and is a theorem; the name per
path; a failing decided premise names no theorem. -/

namespace FVTest.Backend.FnVerdictTest

open Lean Elab Command FVTest.Backend.FnVerdict

/-- Every combination of the facts that selects a theorem. -/
def allFacts : List Facts := Id.run do
  let mut out := []
  for scope in [Scope.integer, .typedT, .typedTC, .typedTCF] do
    for path in [Path.stock, .legacy] do
      for cleanup in [true, false] do
        for opt in [true, false] do
          for optProven in [true, false] do
            for legal in [true, false] do
              for cp in [true, false] do
                for cpSrc in [true, false] do
                  for d0 in [true, false] do
                    out := { scope, path, cleanup, opt, optProven, legal, cp, cpSrc, d0 } :: out
  return out

/-- The declaration name of a printed theorem (without its `(T := …)`). -/
def declOf (t : String) : String := (t.splitOn " (").headD t

-- every theorem the verdict and the unwinding table name is a declared theorem
run_cmd do
  let env ← getEnv
  let names := (allFacts.filterMap fun x => (verdict x).thm) ++
    (Id.run do
      let mut u := []
      for c in [true, false] do
        for o in [true, false] do
          for l in [true, false] do
            for p in [true, false] do
              u := unwindThm c o l p "Opt.ConstPhi.run" :: u
      return u)
  for n in names.eraseDups do
    match env.find? (declOf n).toName with
    | some (.thmInfo _) => pure ()
    | some _ => throwError "{n} is not a theorem"
    | none => throwError "{n} does not exist"

-- the Stock path names the route-independent theorem, about the compiled function when a
-- transformation ran
#guard (verdict { scope := .integer, path := .stock }).thm =
  some "E2E.backend_correct_world_niX_semantic_return_pins"
#guard (verdict { scope := .integer, path := .stock }).about = "the source function"
#guard (verdict { scope := .integer, path := .stock, legal := true }).about =
  "the compiled function, after the i128 legalisation (not composed on this path)"
-- the legacy path: backend_correct_final_cleanup, composed with what ran
#guard (verdict { scope := .integer, path := .legacy }).thm = some "E2E.backend_correct_final_cleanup"
#guard (verdict { scope := .integer, path := .legacy, cleanup := false }).thm =
  some "E2E.backend_correct_final"
#guard (verdict { scope := .integer, path := .legacy, legal := true }).thm =
  some "E2E.backend_correct_legal_wide_cleanup"
#guard (verdict { scope := .integer, path := .legacy, cp := true }).thm =
  some "E2E.backend_correct_pass_cleanup (T := Opt.ConstPhi.run)"
#guard (verdict { scope := .integer, path := .legacy, opt := true }).thm =
  some "E2E.backend_correct_opt_exe_cleanup"
#guard (verdict { scope := .integer, path := .legacy, opt := true, legal := true }).thm =
  some "E2E.backend_correct_legal_opt_wide_cleanup"
-- not composable: the plain theorem about the compiled function
#guard (verdict { scope := .integer, path := .legacy, cp := true, cpSrc := false }).thm =
  some "E2E.backend_correct_final_cleanup"
#guard (verdict { scope := .integer, path := .legacy, cp := true, cpSrc := false }).about =
  "the compiled function, after constant-phi removal (not composed on this path)"
#guard (verdict { scope := .integer, path := .legacy, opt := true, optProven := false }).thm =
  some "E2E.backend_correct_final_cleanup"
-- a Stock.D0 function on the legacy path: the route-independent theorem
#guard (verdict { scope := .integer, path := .legacy, d0 := true }).thm =
  some "E2E.backend_correct_world_niX_semantic_return_pins"
-- the typed scope, on either path
#guard (verdict { scope := .typedTCF, path := .stock }).thm = some "E2E.backend_correct_world_cleanupTCF"
#guard (verdict { scope := .typedT, path := .legacy }).thm = some "E2E.backend_correct_final_cleanupT"
#guard (verdict { scope := .typedTC, path := .legacy, cleanup := false }).thm =
  some "E2E.backend_correct_finalTC"
-- a failing decided premise names no theorem
#guard (verdict { scope := .integer, path := .stock, covered := false }).thm = none
#guard (verdict { scope := .integer, path := .legacy, alloc := false }).thm = none
#guard (verdict { scope := .integer, path := .legacy, record := false }).thm = none
#guard (verdict { scope := .typedTCF, path := .stock, typed := some "x" }).thm = none
#guard (verdict { scope := .typedTCF, path := .stock, typed := some "x" }).fail = some "typed: x"
-- the printed lines cargo fv reads
#guard line (verdict { scope := .integer, path := .stock, covered := false }) =
  "compiled, unverified (outside backend_correct): formsCoveredB fails on the prepared code"
#guard (line (verdict { scope := .integer, path := .legacy }) true (.error "x")).startsWith
  "compiled, verified for normal returns by E2E.backend_correct_final_cleanup (about "
#guard (line (verdict { scope := .integer, path := .legacy }) true
  (.ok (unwindThm true false false false "Opt.ConstPhi.run"))).startsWith
  "compiled, verified by E2E.backend_correct_final_cleanup (about "
#guard unwindThm true false true true "Opt.ConstPhi.run" =
  "E2E.backend_correct_legal_pass_unwind_any (T := Opt.ConstPhi.run)"

end FVTest.Backend.FnVerdictTest
