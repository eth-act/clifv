import Lean
open Lean

/-! Transitive definition dependencies, for re-exposing what a kernel/`decide`/`rfl` reduction
unfolds. usage: lean --run defdeps.lean ROOTMOD NAME...  (LEAN_PATH: a build where every body is
available, i.e. the mechanical port). Prints `name<TAB>module` for every definition of an
FV/FVTest/Corpus module reachable from the NAMEs through definition bodies and types (not
through theorem proofs), the NAMEs included. -/

def local? (env : Environment) (c : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? c
  let m := env.header.moduleNames[idx.toNat]!
  match m.getRoot with
  | `FV | `FVTest | `Corpus => some m
  | _ => none

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let root := args.head!.toName
  let env ← importModules #[{module := root}] {} (loadExts := true)
  let mut todo : Array Name := (args.drop 1).toArray.map String.toName
  let mut seen : Std.HashSet Name := {}
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let some m := local? env c | continue
    match ci with
    | .defnInfo v =>
      IO.println s!"{c}\t{m}"
      for x in v.value.getUsedConstants do todo := todo.push x
      for x in v.type.getUsedConstants do todo := todo.push x
    | .inductInfo v =>
      for x in v.ctors do todo := todo.push x
    | .ctorInfo v => todo := todo.push v.induct
    | _ => pure ()
