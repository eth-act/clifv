/-
Statement/axiom fingerprints of every constant of the listed modules, to check that an import-only
change changes no statement, definition or axiom set (scripts/shake/sigs-diff.py compares two runs).

usage: lake env lean --run scripts/shake/Sigs.lean <out.tsv> <modules.txt>

One line per constant whose name (without its private prefix) is not an implementation detail
(`Name.isInternalDetail`: `_`-components, `match_n`, `proof_n`, `eq_n`, ...):
  module  name  kind  type-hash  value-hash  axioms
value-hash: of the value of definitions, theorems and opaques (`-` otherwise); axioms: the axioms a
theorem depends on (as `#print axioms` computes them, comma-separated, `-` for non-theorems).
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def refs (ci : ConstantInfo) : Array Name :=
  let s := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => s ++ v.getUsedConstants
  | none => s

def insertSorted (a : Array Name) (x : Name) : Array Name :=
  if a.contains x then a else (a.push x).qsort Name.lt

/-- Axioms of every constant reachable from `roots` (memoised, iterative). -/
def axiomsOf (env : Environment) (roots : Array Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut onStack : NameHashSet := {}
  for r in roots do
    if memo.contains r then continue
    let mut stack : Array (Name × Bool) := #[(r, false)]
    while h : stack.size > 0 do
      let (c, expanded) := stack[stack.size - 1]
      stack := stack.pop
      if memo.contains c then continue
      let some ci := env.find? c | memo := memo.insert c #[]; continue
      if expanded then
        let mut ax : Array Name := if ci matches .axiomInfo _ then #[c] else #[]
        for d in refs ci do
          for x in memo.getD d #[] do ax := insertSorted ax x
        memo := memo.insert c ax
        onStack := onStack.erase c
      else
        if onStack.contains c then continue  -- recursion through `unsafe` definitions
        onStack := onStack.insert c
        stack := stack.push (c, true)
        for d in refs ci do
          if !memo.contains d && !onStack.contains d then stack := stack.push (d, false)
  return memo

def main (args : List String) : IO UInt32 := do
  let [outPath, listPath] := args | throw <| .userError "usage: Sigs.lean <out.tsv> <modules.txt>"
  let mods := (← IO.FS.lines listPath).filter (!·.isEmpty) |>.map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := false)
  let wanted : NameHashSet := mods.foldl (·.insert ·) {}
  let mut rows : Array (Name × ConstantInfo) := #[]
  for i in [0:env.header.moduleData.size] do
    let m := env.header.moduleNames[i]!
    unless wanted.contains m do continue
    for ci in env.header.moduleData[i]!.constants do
      unless ((privateToUserName? ci.name).getD ci.name).isInternalDetail do
        rows := rows.push (m, ci)
  let thms := rows.filterMap fun (_, ci) => if ci matches .thmInfo _ then some ci.name else none
  let memo := axiomsOf env thms
  let h ← IO.FS.Handle.mk outPath .write
  for (m, ci) in rows do
    let v := match ci.value? (allowOpaque := true) with
      | some v => toString v.hash | none => "-"
    let ax := if ci matches .thmInfo _ then
        ",".intercalate ((memo.getD ci.name #[]).toList.map toString) else "-"
    h.putStrLn s!"{m}\t{ci.name}\t{kindOf ci}\t{ci.type.hash}\t{v}\t{ax}"
  return 0
