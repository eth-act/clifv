import FV.Front.Bundle
import Lean.Data.Json

/-!
# Reading a frontend bundle (`cargo fv link-proof`'s `bundle.json`, docs/contracts/frontend.md)

`readBundle dir sizes`: the `Front.Bundle` of `dir/bundle.json` (format
`clifv-frontend-bundle`, version 1): the files it names are read unchanged (each function's
CLIF file and `lean-regalloc` output, each unit's `; data:` lines). Any missing field, file or
malformed entry is an error. Everything the compiler's input is computed from them is computed
by the pure `Front.buildSpec`/`Front.assemble`.
-/

namespace Front

open Lean

/-- The bundle format this reader accepts. -/
def bundleVersion : Nat := 1

private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

private def arr (j : Json) (k : String) : Except String (Array Json) := do (← field j k).getArr?

private def str (j : Json) (k : String) : Except String String := do (← field j k).getStr?

private def pairStr (j : Json) : Except String (String × String) := do
  let a ← j.getArr?
  match a.toList with
  | [x, y] => pure (← x.getStr?, ← y.getStr?)
  | _ => throw s!"expected a pair, got {j.compress}"

private def pairNat (j : Json) : Except String (String × Nat) := do
  let a ← j.getArr?
  match a.toList with
  | [x, y] => pure (← x.getStr?, ← y.getNat?)
  | _ => throw s!"expected a pair, got {j.compress}"

/-- An object `{"k": "v", …}` as pairs. -/
private def strMap (j : Json) : Except String (List (String × String)) := do
  let o ← j.getObj?
  o.toList.mapM fun (k, v) => do pure (k, ← v.getStr?)

private def liftE {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- **Read `dir/bundle.json`** and the files it names; `sizes`: linked name → words. -/
def readBundle (dir : System.FilePath) (sizes : List (String × Nat)) :
    IO (Bundle × String) := do
  let p := dir / "bundle.json"
  let j ← liftE p.toString (Json.parse (← IO.FS.readFile p))
  let fmt ← liftE p.toString (str j "format")
  let ver ← liftE p.toString (do (← field j "version").getNat?)
  if fmt != "clifv-frontend-bundle" || ver != bundleVersion then
    throw (IO.userError s!"{p}: format {fmt} version {ver}, expected clifv-frontend-bundle {bundleVersion}")
  let exe ← liftE p.toString (str j "exe")
  let mut units : Array Cgu := #[]
  for uj in ← liftE p.toString (arr j "units") do
    let tag ← liftE p.toString (str uj "tag")
    let w := s!"{p}: unit {tag}"
    let mut fns : Array FnFile := #[]
    for fj in ← liftE w (arr uj "functions") do
      let name ← liftE w (str fj "name")
      let clif ← liftE w (str fj "clif")
      let ra ← liftE w (str fj "ra")
      fns := fns.push { name, clif := ← IO.FS.readFile clif, ra := ← IO.FS.readFile ra }
    let dataPath ← liftE w (str uj "data")
    let data := ((← IO.FS.readFile dataPath).splitOn "\n").filter (·.startsWith "; data:")
    let locals ← liftE w (do (← arr uj "locals").toList.mapM pairStr)
    let names ← liftE w (do strMap (← field uj "names"))
    let localAddrs ← liftE w (do (← arr uj "local_addrs").toList.mapM pairNat)
    units := units.push { tag, funcs := fns.toList, data, locals, names, localAddrs }
  let symbols ← liftE p.toString (do (← arr j "symbols").toList.mapM pairNat)
  let markers ← liftE p.toString (do (← arr j "markers").toList.mapM pairNat)
  let skipped ← liftE p.toString (do (← arr j "skipped").toList.mapM pairStr)
  pure ({ units := units.toList, symbols, markers, sizes, skipped }, exe)

end Front
