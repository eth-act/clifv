/-
Constant names per module, read from the .olean files without building an environment (for
scripts/shake/shake.py `lean_batches`: modules that define the same name cannot be imported into
one environment, so they go into different batches).

usage: lake env lean --run scripts/shake/Names.lean <out.tsv> <modules.txt> [all]

One line `name<TAB>module` for every constant name that more than one listed module defines
(with `all`: for every constant name of the listed modules).
-/
import Lean
open Lean

def main (args : List String) : IO UInt32 := do
  let (outPath, listPath, all) ← match args with
    | [o, l] => pure (o, l, false)
    | [o, l, "all"] => pure (o, l, true)
    | _ => throw <| .userError "usage: Names.lean <out.tsv> <modules.txt> [all]"
  let mods := (← IO.FS.lines listPath).filter (!·.isEmpty) |>.map String.toName
  initSearchPath (← findSysroot)
  let mut owner : Std.HashMap Name Name := {}
  let mut dup : Array (Name × Name) := #[]
  let h ← IO.FS.Handle.mk outPath .write
  for m in mods do
    let (md, _) ← readModuleData (← findOLean m)  -- mmapped; not freed (names point into it)
    for c in md.constNames ++ md.extraConstNames do
      if all then h.putStrLn s!"{c}\t{m}"
      match owner[c]? with
      | some m' => if m' != m then dup := dup.push (c, m) |>.push (c, m')
      | none => owner := owner.insert c m
  if all then return 0
  for (c, m) in dup do
    h.putStrLn s!"{c}\t{m}"
  return 0
