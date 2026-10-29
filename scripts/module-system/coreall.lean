import Lean
open Lean

/-! Which core modules a ported module needs `import all` of, so that `decide`/`rfl`/kernel
reduction can unfold the same core definitions as before the port.

usage: lean --run coreall.lean MODULE...   (LEAN_PATH: the unported build, then the toolchain)

For each MODULE (imported from the unported build, so every body is available), every definition
reachable from MODULE's own declarations (types and values; through definition bodies, not
through theorem proofs) that comes from a core module (Init/Std/Lean) whose public `.olean` does
not carry its body (not exposed) is collected; the output is one line per MODULE:
`MODULE: Init.X Init.Y ...` (the modules of those definitions). -/

def isCore (n : Name) : Bool :=
  match n.getRoot with
  | `Init | `Std | `Lean => true
  | _ => false

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let mods := args.map String.toName
  let env ← importModules (mods.toArray.map ({module := ·})) {} (loadExts := true)
  let pubCache ← IO.mkRef (∅ : Std.HashMap Name (Std.HashSet Name))
  let exposed (m : Name) (c : Name) : IO Bool := do
    if let some s := (← pubCache.get)[m]? then return s.contains c
    let f ← findOLean m
    let (md, _) ← readModuleData f
    let s := md.constants.foldl (init := (∅ : Std.HashSet Name)) fun s ci =>
      match ci with
      | .defnInfo _ => s.insert ci.name
      | _ => s
    pubCache.modify (·.insert m s)
    return s.contains c
  for m in mods do
    let some idx := env.getModuleIdx? m | IO.println s!"{m}: not found"; continue
    let mut todo : Array Name := #[]
    for c in env.header.moduleData[idx.toNat]!.constNames do
      todo := todo.push c
    let mut seen : Std.HashSet Name := {}
    let mut need : Std.HashSet Name := {}
    let mut first := true
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      let some ci := env.find? c | continue
      let some cm := env.getModuleIdxFor? c |>.map (env.header.moduleNames[·.toNat]!) | continue
      let own := cm == m
      if isCore cm then
        if ci matches .defnInfo _ then
          unless ← exposed cm c do need := need.insert cm
      let follow := match ci with
        | .defnInfo v => some v.value
        | .thmInfo v => if own then some v.value else none
        | _ => none
      for x in ci.type.getUsedConstants do todo := todo.push x
      if let some v := follow then
        for x in v.getUsedConstants do todo := todo.push x
      first := false
    let out := need.toArray.qsort (·.toString < ·.toString)
    IO.println s!"{m}: {" ".intercalate (out.map toString).toList}"
