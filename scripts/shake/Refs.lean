/-
Constant-level references, to find imports that serialize the build for a few lemmas
(scripts/shake/chain.py).

usage: lake env lean --run scripts/shake/Refs.lean <out.jsonl> <modules.txt>

One JSON line per constant of a listed module: {"c": name, "m": module, "aux": bool,
"priv": bool, "pos": [line, endLine] or null, "refs": [[constant, module], ...]} where refs are
the constants of FV/FVTest/Corpus modules that its type or value mentions (other than itself), and
pos is the declaration's source range (for constants with one).
-/
import Lean
open Lean

def internal (m : Name) : Bool := m.getRoot == `FV || m.getRoot == `FVTest || m.getRoot == `Corpus

def main (args : List String) : IO UInt32 := do
  let [outPath, listPath] := args | throw <| .userError "usage: Refs.lean <out.jsonl> <modules.txt>"
  let mods := (← IO.FS.lines listPath).filter (!·.isEmpty) |>.map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := false)
  let wanted : NameHashSet := mods.foldl (·.insert ·) {}
  let h ← IO.FS.Handle.mk outPath .write
  for i in [0:env.header.moduleData.size] do
    let m := env.header.moduleNames[i]!
    unless wanted.contains m do continue
    for ci in env.header.moduleData[i]!.constants do
      let mut refs : NameHashSet := {}
      for e in [ci.type] ++ (ci.value? (allowOpaque := true)).toList do
        for c in e.getUsedConstants do
          if c != ci.name then refs := refs.insert c
      let mut out : Array Json := #[]
      for c in refs.toArray do
        if let some j := env.getModuleIdxFor? c then
          let mc := env.header.moduleNames[j]!
          if internal mc then out := out.push (Json.arr #[toString c, toString mc])
      let pos ← match ← (findDeclarationRanges? ci.name : CoreM _).run' { fileName := "", fileMap := default } { env } |>.toBaseIO with
        | .ok (some r) => pure (Json.arr #[r.range.pos.line, r.range.endPos.line])
        | _ => pure Json.null
      let user := (privateToUserName? ci.name).getD ci.name
      h.putStrLn (Json.mkObj [("c", toString ci.name), ("m", toString m),
        ("aux", user.isInternalDetail), ("priv", isPrivateName ci.name), ("pos", pos),
        ("refs", Json.arr out)]).compress
  return 0
