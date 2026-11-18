/-! # The theorem `link-check`'s binary check instantiates (#1092, #1093)

`link-check` decides, for the (pruned) program and the executable, the premises of an
executable-word theorem about the program's results in the checker it selected:

| checker | premises decided by `link-check` | theorem |
|---|---|---|
| `integer` (the return-pin production checks) | `ReturnPinStackBound.okB` (`okB:`), `BinOkWithResults` (`binary:`), `codeMapB` (`code map:`), `SemanticExecBytes.GotOk` (`GOT:`, `gotTabB_sound`) | `E2E.ReturnPinExecBytes.binary_correct_exec_proven` |
| `typed Stock (okRWithTS)` | `SemanticStackBound.okBTS`, `BinOkWithResults`, `codeMapB`, `SemanticExecBytes.GotOk` | `E2E.SemanticExecBytes.binary_correct_exec_provenTS` |
| `typed (okBCleanupT)` | `okBCleanupT`, `DeadCleanupBinCheck.BinOk`, `codeMapB`, `DeadCleanupExecBytes.GotOk` | `E2E.DeadCleanupExecBytes.binary_correct_exec_provenT` |

The acyclic theorem's `¬ CycleFrom` is the stack bound (`stack:`); for a function whose calls
reach a call cycle the `_peak_` sibling applies, its stack a premise. `binTheorem` is the name;
`binVerdict` names it only when every decided premise holds, else the first failing one.
`FVTest.E2E.BinVerdictTest` checks that every name exists and the verdict of each case.
-/

namespace FVTest.E2E.BinVerdict

/-- The checker `link-check` selected. -/
inductive Checker where
  | integer | typedStock | typed
  deriving DecidableEq, Repr

/-- The checker's name as `link-check` prints it (`checker:`). -/
def Checker.label : Checker → String
  | .integer => "integer"
  | .typedStock => "typed Stock (okRWithTS)"
  | .typed => "typed (okBCleanupT)"

/-- The acyclic theorem and its `_peak_` sibling. -/
def theorems : Checker → String × String
  | .integer => ("E2E.ReturnPinExecBytes.binary_correct_exec_proven",
      "E2E.ReturnPinExecBytes.binary_correct_exec_peak_proven")
  | .typedStock => ("E2E.SemanticExecBytes.binary_correct_exec_provenTS",
      "E2E.SemanticExecBytes.binary_correct_exec_peak_provenTS")
  | .typed => ("E2E.DeadCleanupExecBytes.binary_correct_exec_provenT",
      "E2E.DeadCleanupExecBytes.binary_correct_exec_peak_provenT")

/-- **The theorem the checks instantiate**, with the `_peak_` sibling for a program whose calls
reach a call cycle. -/
def binTheorem (c : Checker) (recursive : Bool) : String :=
  let (t, p) := theorems c
  if recursive then
    s!"{t} ({p} for the functions whose calls reach a call cycle: their stack stays a premise)"
  else t

/-- **The verdict**: `theorem: <binTheorem>` when every premise `link-check` decides holds
(`ok`: the checker; `binOk`: the binary checks; `codeOk`: `codeMapB`; `gotOk`: `GotOk`), else
`theorem: none (<first failing premise>)`. -/
def binVerdict (c : Checker) (recursive ok binOk codeOk gotOk : Bool) : String :=
  if !ok then s!"theorem: none (the checker {c.label} fails)"
  else if !binOk then "theorem: none (the binary checks fail)"
  else if !codeOk then "theorem: none (codeMapB fails)"
  else if !gotOk then "theorem: none (GotOk fails)"
  else s!"theorem: {binTheorem c recursive}"

end FVTest.E2E.BinVerdict
