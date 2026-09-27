/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat
-/
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in namespace Arm, the `bv_toNat` simp set is now core's `bitvec_to_nat`.
/-
This module implements `bv_omega_bench`, which writes benchmarking results of `bv_omega`
into a user-defined file. This is used for extracting out calls to `bv_omega` that are slow,
and allows us to send bug reports to the Lean developers.
-/
import FV.Arm.Tactics.Attr
import Lean
import Lean.Elab.Tactic.Omega.Frontend
import Lean.Elab.Tactic.Omega
import FV.Arm.Tactics.Simp

namespace Arm

open Lean Elab Meta Tactic Omega

namespace BvOmegaBench

/-- The name of the simp set that `bv_omega` uses to translate `BitVec` goals to `Nat` goals.
(LNSym called this set `bv_toNat`; in Lean v4.34 it is `bitvec_to_nat`.) -/
def bvToNatSimpAttr : Name := `bitvec_to_nat

/-
Make the `SimpContext` that corresponds to using `bv_toNat`
Adapted mkSimpContext:
from https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean#L287
-/
def bvOmegaSimpCtx : MetaM (Simp.Context × Array Simp.Simprocs) := do
  let mut simprocs := #[]
  let mut simpTheorems := #[]

  let some ext ← (getSimpExtension? bvToNatSimpAttr)
    | throwError m!"[omega] Error: unable to find `{bvToNatSimpAttr}"
  simpTheorems := simpTheorems.push (← ext.getTheorems)

  if let some ext ← (Simp.getSimprocExtension? bvToNatSimpAttr) then
    let s ← ext.getSimprocs
    simprocs := simprocs.push s

  let congrTheorems ← Meta.getSimpCongrTheorems
  let config : Simp.Config := { failIfUnchanged := false }
  let ctx ← Simp.mkContext config simpTheorems congrTheorems
  return (ctx, simprocs)

private def logBench (goalStr : Format) (delta : Nat) (err? : Option String) : MetaM Unit := do
  if (← getBvOmegaBenchIsEnabled) && delta ≥ (← getBvOmegaBenchMinMs) then
    let filePath ← getBvOmegaBenchFilePath
    IO.FS.withFile filePath IO.FS.Mode.append fun h => do
      h.putStrLn "\n---\n"
      h.putStrLn s!"goal"
      h.putStrLn goalStr.pretty
      h.putStrLn s!"endgoal"
      h.putStrLn s!"time"
      h.putStrLn s!"{delta}"
      h.putStrLn s!"endtime"
      if let some err := err? then
        h.putStrLn s!"error"
        h.putStrLn err
        h.putStrLn s!"enderror"

/--
Run bv_omega, gather the results, and then store them at the value that is given by the option.
By default, it's stored at `pwd`, with filename `omega-bench`. The file is appended to,
with the goal state that is being run, and the time elapsed to solve the goal is written.

Code adapted from:
- https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean#L406
- https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Omega/Frontend.lean#L685
-/
def run (g : MVarId) (hyps : Array Expr) (bvToNatSimpCtx : Simp.Context)
    (bvToNatSimprocs : Array Simp.Simprocs) : MetaM Unit := do
  let goalStr ← ppGoal g
  let startTime ← IO.monoMsNow
  let mut g := g
  let hypFVars : Array FVarId :=
    hyps.filterMap (fun e => if e.isFVar then some e.fvarId! else none)
  try
     try
       let (result?, _stats) ← g.withContext <|
         simpGoal g bvToNatSimpCtx bvToNatSimprocs (simplifyTarget := true)
           (discharge? := .none) hypFVars
       let .some (_hypFVars', g') := result? | return ()
       g := g'
     catch e =>
       trace[simp_mem.info] "in BvOmega, ran `simp only [bv_toNat]` and got error: \
         {indentD e.toMessageData}"
       throw e
     let some g' ← g.withContext <| g.falseOrByContra | return ()
     g := g'
     g.withContext do
       omega (← getLocalHyps).toList g {}
       logBench goalStr ((← IO.monoMsNow) - startTime) none
  catch e =>
    logBench goalStr ((← IO.monoMsNow) - startTime) (some (← e.toMessageData.toString))
    throw e

/-- Build the default simp context (bv_toNat) and run omega -/
def runWithDefaultSimpContext (g : MVarId) : MetaM Unit := do
  let (bvToNatSimpCtx, bvToNatSimprocs) ← bvOmegaSimpCtx
  g.withContext do
    run g ((← g.getNondepPropHyps).map Expr.fvar) bvToNatSimpCtx bvToNatSimprocs

end BvOmegaBench

/-- `bv_omega_bench` is `bv_omega` (simp with the `BitVec`-to-`Nat` simp set at the
non-dependent propositional hypotheses and the goal, then `omega`), which additionally
logs slow calls when `Tactic.bv_omega_bench.enabled` is set. -/
syntax (name := bvOmegaBenchTac) "bv_omega_bench" : tactic

@[tactic bvOmegaBenchTac]
def bvOmegaBenchImpl : Tactic
| `(tactic| bv_omega_bench) =>
    liftMetaFinishingTactic fun g => do
      BvOmegaBench.runWithDefaultSimpContext g
| _ => throwUnsupportedSyntax

end Arm
