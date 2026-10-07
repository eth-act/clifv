import FV.Link.Image
import Lean.Data.Json

/-! # `lake exe lean-link DIR SIZES`: the Lean linker on an executable (L2b)

`DIR` is `cargo fv link-proof --cgus … --no-check`'s output for an executable linked by
`cargo fv --lean-link` (docs/research/lean-linker.md): the program's functions in placement
order (`functions`: their CLIF with the linked names and `lean-regalloc`'s output), the link
map's addresses of the names they use (`addrs`: the outside part's symbols, read from the
executable, and the functions' own, where rust-lld put the region), the functions whose address
is in a data object (`data_syms`), the CLIF data objects they reach (`data`). `SIZES` has one
line `NAME WORDS` per function: its size in the region object (`cargo fv`'s `leanlink.rs`;
`Link.leanLink` checks it against the compiled code, `sizesOkB`). The tool builds the
`Link.LinkSpec` (the region's base `R`: the first function's address), runs `Link.leanLink`
(placement, the compiler's pipeline, the linker's checks, the checks of rust-lld's output —
among them that rust-lld put every function at its placement, `symsOkB`) and writes the result
over the executable.
-/

open Lean E2E E2E.LinkCheck E2E.Elf Link

/-- The names a function's CLIF takes the address of (as `link-check`'s `addrNames`). -/
def addrNamesOf (f : Clif.Function) : List String :=
  f.globals.filterMap (fun g => match g.2 with | .symbol n _ _ => some n | _ => none) ++
  f.blocks.flatMap fun b => b.body.filterMap fun st => match st.inst with
    | .funcAddr _ fn => (f.extern? fn).map (·.name)
    | _ => none

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The strings of a JSON array field. -/
def strs (j : Json) (k : String) : List String :=
  (((j.getObjVal? k).bind (·.getArr?)).toOption.getD #[]).toList.filterMap (·.getStr?.toOption)

def main (args : List String) : IO UInt32 := do
  let [d, sz] := args | do IO.eprintln "usage: lean-link DIR SIZES (cargo fv link-proof's output, the region's sizes)"; return 2
  let dir : System.FilePath := d
  let j ← match Json.parse (← IO.FS.readFile (dir / "link.json")) with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"lean-link: link.json: {e}"; return 2
  let exe := (j.getObjValAs? String "exe").toOption.getD ""
  let skipped := ((j.getObjVal? "skipped").bind (·.getArr?)).toOption.getD #[]
  if !skipped.isEmpty then
    IO.eprintln s!"lean-link: link-proof skipped {skipped.size} function(s) of the region: {skipped[0]!.compress}"
    return 1
  let fjs := ((j.getObjVal? "functions").bind (·.getArr?)).toOption.getD #[]
  let mut fis : Array FnInput := #[]
  for fj in fjs do
    let clif := (fj.getObjValAs? String "clif").toOption.getD ""
    let ra := (fj.getObjValAs? String "ra").toOption.getD ""
    fis := fis.push { clif := ← IO.FS.readFile (dir / clif), ra := ← IO.FS.readFile (dir / ra) }
  let ajs := ((j.getObjVal? "addrs").bind (·.getArr?)).toOption.getD #[]
  let addrs0 : List (String × Nat) := ajs.toList.filterMap fun a => do
    let arr ← a.getArr?.toOption
    let n ← (arr[0]?.bind (·.getStr?.toOption))
    let v ← (arr[1]?.bind (·.getNat?.toOption))
    pure (n, v)
  let addrMap : Std.HashMap String Nat := addrs0.foldl (fun m p => if m.contains p.1 then m else m.insert p.1 p.2) {}
  let mut sizeMap : Std.HashMap String Nat := {}
  for l in (← IO.FS.readFile sz).splitOn "\n" do
    match l.splitOn " " with
    | [n, w] => sizeMap := sizeMap.insert n w.toNat!
    | _ => pure ()
  -- each CLIF file parsed once here (`FnInput.func` parses)
  let fns := fis.map (·.func)
  let names := fns.toList.map (·.name)
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  let mut sizes : Array Nat := #[]
  for n in names do
    let some w := sizeMap[n]? | do IO.eprintln s!"lean-link: {n}: no size in {sz}"; return 1
    sizes := sizes.push w
  -- `cargo fv`'s self-call aliases (as `link-check` builds them): `f__fvself`, `f`'s body with
  -- its self-call naming `f`, at `f`'s address
  let mut aliases : Array (String × String) := #[]
  let mut aliasFns : Array FnInput := #[]
  for (fi, f) in fis.zip fns do
    let n := f.name
    let a := n ++ "__fvself"
    if f.externs.any (·.2.name == a) && !addrMap.contains a then
      let clif := (fi.clif.replace s!"%{a}(" s!"%{n}(").replace s!"function %{n}(" s!"function %{a}("
      aliasFns := aliasFns.push { fi with clif }
      aliases := aliases.push (a, n)
  let progSet := aliases.foldl (fun s p => s.insert p.1) nameSet
  let outside := addrs0.filter fun p => !progSet.contains p.1
  let symNames := Id.run do
    let mut seen : Std.HashSet String := {}
    let mut out : Array String := #[]
    for n in fns.toList.flatMap addrNamesOf ++ aliasFns.toList.flatMap (addrNamesOf ·.func) ++
        (strs j "data_syms").filter nameSet.contains do
      if !seen.contains n then
        seen := seen.insert n
        out := out.push n
    return out.toList
  let some R := names.head?.bind (addrMap[·]?)
    | do IO.eprintln "lean-link: no function, or the first has no address"; return 1
  let S : LinkSpec := {
    funcs := fis.toList
    names := names
    sizes := sizes.toList
    aliases := aliases.toList
    aliasFns := aliasFns.toList
    outside := outside
    data := BinCheck.parseData (strs j "data")
    symNames := symNames
    R := R }
  let file0 ← IO.FS.readBinFile exe
  match leanLink S file0 with
  | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
  | .ok file =>
    IO.FS.writeBinFile exe file
    IO.println s!"lean-link: {exe}: {names.length} function(s) ({aliases.size} self-call alias(es)), {S.data.length} data object(s), region {hex R}..{hex (R + S.size)} ({S.size} bytes) written by Link.leanLink"
    return 0
