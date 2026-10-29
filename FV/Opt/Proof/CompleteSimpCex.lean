module

public import FV.Opt.Optimize
public meta import FV.Opt.HandRules
public meta import FV.Opt.Optimize

@[expose] public section

/-!
# The simplify stage is incomplete on duplicated `symbol_value`s (M1, #24)

A rule-independent counterexample to the completeness of the simplify stage when `allowed`
admits `symbol_value` (as `Opt.allowedIn` did before it was restricted): two sibling blocks compute the same
`symbol_value`. The second one visited hash-cons-hits the first (`Opt.memoHit`), whose block
does not dominate it, so `Opt.materialize` clones the node: the record `StmtLog.repl` then
inserts a `symbol_value`, which `Opt.insOk` rejects, so `Opt.simpOk` fails and the pipeline
would stop at the simplify stage (`Report.passError`). It happens with every rule set (the rules
are not even run on a hash-consing hit); here the hand rules with `allowed := isPure`.

The completeness theorem (`FV/Opt/Proof/CompleteSimp.lean`) therefore assumes that `allowed`
rejects `symbol_value` (then `clone` fails and the statement is kept), which `Opt.allowedIn` now
does (`Opt.allowedIn_symbolValue`): on `fn` the pipeline no longer stops.
-/

namespace Opt.CompleteSimpCex

open Clif

/-- Block 0 branches to blocks 1 and 2, which both compute `symbol_value.i64 gv0`. -/
def fn : Function where
  name := "w"
  sig := {}
  globals := [(0, .symbol "s" 0 false)]
  blocks := [
    { id := 0, body := [{ results := [0], inst := .iconst .i8 1 }], term := .brif 0 ⟨1, []⟩ ⟨2, []⟩ },
    { id := 1, body := [{ results := [1], inst := .symbolValue .i64 0 }], term := .ret [1] },
    { id := 2, body := [{ results := [2], inst := .symbolValue .i64 0 }], term := .ret [2] }]

/-- `fn` is well-formed, and the simplify validator rejects the pass's output on it when every
pure node is allowed (hand rules). -/
theorem simplify_incomplete_symbolValue :
    ∃ info, check fn = .ok info ∧
      simpOk fn (simplify HandRules.simplify HandRules.simplifySkeleton isPure (fun _ => true)
        false fn info).1 info
        (simplify HandRules.simplify HandRules.simplifySkeleton isPure (fun _ => true)
          false fn info).2.2 = false := by
  have h : (match check fn with
      | .ok info => simpOk fn (simplify HandRules.simplify HandRules.simplifySkeleton isPure
          (fun _ => true) false fn info).1 info
          (simplify HandRules.simplify HandRules.simplifySkeleton isPure (fun _ => true)
            false fn info).2.2 == false
      | .error _ => false) = true := by native_decide
  split at h
  · rename_i info hi
    exact ⟨info, hi, by simpa using h⟩
  · cases h

/-- With `allowedIn` (which rejects `symbol_value`) the pipeline does not stop on `fn`. -/
theorem optimizeReport_symbolValue_ok :
    (optimizeReport { rules := .hand } fn).2.passError = none := by
  native_decide

end Opt.CompleteSimpCex
