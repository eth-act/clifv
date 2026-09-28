import FV.Opt.Gvn
import FV.Opt.Dce
import FV.Opt.Simplify
import FV.Opt.Licm
import FV.Opt.HandRules
import FV.Compile.Subset
import FV.Isle.Opt.Simplify

/-!
# `Opt.optimize`: the mid-end pipeline (unproven; `docs/contracts/midend.md`)

```
removeUnreachable ; check ;
(simplify ; removeUnreachable ; check ; gvn ; check ; dce) × rounds ;
licm ; check ; gvn ; check ; dce
```

`check` (`Opt.check`) is the well-formedness precondition of every pass. If the input fails
it, the function is returned with only unreachable blocks removed. If a pass's output fails
it (a bug), the pipeline stops and returns the last well-formed function — a cheap
translation-validation guard that the difftests report (`Report.passError`).

When the input function is in the backend subset E (`Compile.functionE`), the simplifier may
only emit nodes in E, so `--opt` never takes a function out of the backend's reach.
-/

namespace Opt

open Clif

/-- The implementation of a rule set. -/
def RuleSetId.fn : RuleSetId → SimplifyFn
  | .cranelift => fun enodes typeOf make st v => Isle.Opt.simplify enodes typeOf make st v
  | .hand => HandRules.simplify

/-- The skeleton rules of a rule set. -/
def RuleSetId.skeletonFn : RuleSetId → SkeletonFn
  | .cranelift => fun enodes typeOf make trapBlock st i =>
    Isle.Opt.simplifySkeleton enodes typeOf make trapBlock st i
  | .hand => HandRules.simplifySkeleton

structure Config where
  rules : RuleSetId := .cranelift
  simplify : Bool := true
  gvn : Bool := true
  dce : Bool := true
  licm : Bool := true
  /-- Rematerialise constants like Cranelift (`remat.isle`, elaboration): the simplifier's
  hash-consing and GVN number `iconst` per block only, so a constant is defined in each block
  using it instead of living across blocks. -/
  rematConst : Bool := false
  /-- LICM hoists `iconst` out of loops (measured better for this backend, which lowers every
  `iconst` even when isel folds it into an immediate). -/
  hoistConst : Bool := true
  /-- Rounds of simplify/gvn/dce before LICM (a second round removed 3 more of 27 761
  instructions on corpus + runtests + fuzz files, so one is the default). -/
  rounds : Nat := 1

structure Report where
  name : String
  /-- The input failed `Opt.check` (not optimised). -/
  illFormed : Option String := none
  /-- A pass produced an ill-formed function (pass name, message); later passes skipped. -/
  passError : Option (String × String) := none
  sizeBefore : Nat := 0
  sizeAfter : Nat := 0
  rewritten : Nat := 0
  /-- Skeleton instructions/terminators simplified. -/
  skeleton : Nat := 0
  gvnRemoved : Nat := 0
  dceRemoved : Nat := 0
  hoisted : Nat := 0
  ruleErrors : Nat := 0
  fired : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Nodes the simplifier may emit into `f`. -/
def allowedIn (f : Function) : Inst → Bool :=
  if Compile.functionE f then fun n => isPure n && Compile.instE n else isPure

/-- Skeleton instructions the simplifier may emit into `f`. -/
def skelAllowedIn (f : Function) : Inst → Bool :=
  if Compile.functionE f then Compile.instE else fun _ => true

/-- Run the pipeline on one function, with a report. -/
def optimizeReport (cfg : Config) (f0 : Function) : Function × Report := Id.run do
  let f := removeUnreachable f0
  let mut r : Report := { name := f.name, sizeBefore := instCount f0 }
  let info ← match check f with
    | .ok i => pure i
    | .error e => return (f, { r with illFormed := some e, sizeAfter := instCount f })
  let allowed := allowedIn f
  let mut g := f
  let mut info := info
  -- `step name pass`: run a pass, re-check; on failure stop with the last good function
  let mut stop := false
  let stages : List String :=
    (List.replicate cfg.rounds ["simplify", "gvn", "dce"]).flatten ++ ["licm", "gvn", "dce"]
  for stage in stages do
    if stop then break
    let enabled := match stage with
      | "simplify" => cfg.simplify | "gvn" => cfg.gvn | "dce" => cfg.dce | _ => cfg.licm
    if !enabled then continue
    let g' ← match stage with
      | "simplify" =>
        let (g', s) := simplify cfg.rules.fn cfg.rules.skeletonFn allowed (skelAllowedIn f) cfg.rematConst g info
        let g' := removeUnreachable g'
        r := { r with rewritten := r.rewritten + s.rewritten, ruleErrors := r.ruleErrors + s.errors,
                      skeleton := r.skeleton + s.skeleton,
                      fired := s.fired.fold (fun m k n => m.insert k ((m.get? k).getD 0 + n)) r.fired }
        pure g'
      | "gvn" =>
        let (g', n) := gvn g info (fun i => cfg.rematConst && match i with
          | .iconst .. => true
          | _ => false)
        r := { r with gvnRemoved := r.gvnRemoved + n }
        pure g'
      | "dce" =>
        let (g', n) := dce g
        r := { r with dceRemoved := r.dceRemoved + n }
        pure g'
      | _ =>
        let (g', n) := licm cfg.hoistConst g info
        r := { r with hoisted := r.hoisted + n }
        pure g'
    match check g' with
    | .ok i => g := g'; info := i
    | .error e => r := { r with passError := some (stage, e) }; stop := true
  return (g, { r with sizeAfter := instCount g })

/-- `Opt.optimize`: the optimised function (`Config` defaults). -/
def optimize (f : Function) (cfg : Config := {}) : Function := (optimizeReport cfg f).1

/-- Optimise every function of a program (functions are optimised independently). -/
def optimizeProgram (p : Program) (cfg : Config := {}) : Program :=
  { p with funcs := p.funcs.map (optimize · cfg) }

end Opt
