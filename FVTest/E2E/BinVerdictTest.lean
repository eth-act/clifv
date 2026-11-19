import FVTest.E2E.BinVerdict
import FV.E2E.ReturnPinExecProven
import FV.E2E.SemanticExecTS
import FV.E2E.DeadCleanupExecProvenT
import FV.E2E.DeadCleanupExecPeakT
import FV.E2E.GotTab
import FV.E2E.MidValExecProven

/-! # Tests of `link-check`'s verdict (#1092, #1093)

Every theorem name `link-check` can print exists, and is a theorem; a failing decided premise
(the checker, the binary checks, `codeMapB`, `GotOk`) names no theorem. -/

namespace FVTest.E2E.BinVerdictTest

open Lean Elab Command FVTest.E2E.BinVerdict

-- every theorem `binTheorem` names is a declared theorem
run_cmd do
  let env ← getEnv
  for c in [Checker.integer, .typedStock, .typed] do
    let (t, p) := theorems c
    for n in [t, p] do
      match env.find? n.toName with
      | some (.thmInfo _) => pure ()
      | some _ => throwError "{n} is not a theorem"
      | none => throwError "{n} does not exist"

#guard binVerdict .integer false true true true true =
  "theorem: E2E.ReturnPinExecBytes.binary_correct_exec_proven"
#guard binVerdict .typedStock true true true true true =
  "theorem: E2E.SemanticExecBytes.binary_correct_exec_provenTS (E2E.SemanticExecBytes.binary_correct_exec_peak_provenTS for the functions whose calls reach a call cycle: their stack stays a premise)"
#guard binVerdict .typed false true true true true =
  "theorem: E2E.DeadCleanupExecBytes.binary_correct_exec_provenT"
-- a wrong code map or a bad GOT slot: no theorem
#guard binVerdict .integer false true true false true = "theorem: none (codeMapB fails)"
#guard binVerdict .typedStock false true true true false = "theorem: none (GotOk fails)"
#guard binVerdict .integer false true false true true = "theorem: none (the binary checks fail)"
#guard binVerdict .typed false false true true true = "theorem: none (the checker typed (okBCleanupT) fails)"

-- #1119: every `_mid` theorem `binTheoremMid` names is a declared theorem; a failing
-- `midValidatedB` names none
run_cmd do
  let env ← getEnv
  for c in [Checker.integer, .typedStock, .typed] do
    let (t, p) := theoremsMid c
    for n in [t, p] do
      match env.find? n.toName with
      | some (.thmInfo _) => pure ()
      | some _ => throwError "{n} is not a theorem"
      | none => throwError "{n} does not exist"
#guard binVerdictMid .integer false true true true true true =
  "theorem: E2E.ReturnPinExecBytes.binary_correct_exec_proven_mid (about the program of the unoptimised dumps)"
#guard binVerdictMid .integer false true true true true false = "theorem: none (Link.midValidatedB fails)"
#guard binVerdictMid .typed false true true false true true = "theorem: none (codeMapB fails)"

-- the GOT decider's soundness and the `ldr` form it keys on
example : E2E.GotTab.ldrFormB (E2E.BinCheck.ldrW 3 3 5) = true := E2E.GotTab.ldrFormB_ldrW (by decide) (by decide)
-- an `adrp`/`add` pair's second word (a relaxed GOT pair) is not the `ldr` form
#guard E2E.GotTab.ldrFormB 0x91000000#32 = false
#check @E2E.SemanticExecBytes.gotTabB_sound
#check @E2E.DeadCleanupExecBytes.gotTabB_sound

end FVTest.E2E.BinVerdictTest
