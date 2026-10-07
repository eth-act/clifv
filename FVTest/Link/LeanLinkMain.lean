import FV.Link.Image
import Lean.Data.Json

/-! # `lake exe lean-link DIR`: the Lean linker on an executable (L2b)

`DIR` is `cargo fv link-proof --cgus … --no-check`'s output for an executable linked by
`cargo fv --lean-link` (docs/research/lean-linker.md): the program's functions in placement
order (`functions`: their CLIF with the linked names and `lean-regalloc`'s output), the link
map's addresses of the names they use (`addrs`: the outside part's symbols, read from the
executable, and the functions' own, where rust-lld put the region), the functions whose address
is in a data object (`data_syms`). The tool builds the `Link.LinkSpec` (the region's base `R`:
the first function's address), checks that rust-lld put every function where the placement
does (the outside part's calls and data reach the program through those symbols), runs
`Link.leanLink` (placement, the compiler's pipeline, the relocation checks, the region check)
and writes the result over the executable.
-/

open Lean E2E E2E.LinkCheck E2E.Elf Link

/-- The names a function's CLIF takes the address of (as `link-check`'s `addrNames`). -/
def addrNamesOf (f : Clif.Function) : List String :=
  f.globals.filterMap (fun g => match g.2 with | .symbol n _ _ => some n | _ => none) ++
  f.blocks.flatMap fun b => b.body.filterMap fun st => match st.inst with
    | .funcAddr _ fn => (f.extern? fn).map (·.name)
    | _ => none

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def main (args : List String) : IO UInt32 := do
  let [d] := args | do IO.eprintln "usage: lean-link DIR (cargo fv link-proof's output)"; return 2
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
  let names := fis.toList.map (·.func.name)
  -- `cargo fv`'s self-call aliases (as `link-check` builds them): `f__fvself`, `f`'s body with
  -- its self-call naming `f`, at `f`'s address
  let mut aliases : List (String × String) := []
  let mut aliasFns : List FnInput := []
  for fi in fis do
    let n := fi.func.name
    let a := n ++ "__fvself"
    if fi.func.externs.any (·.2.name == a) && !(addrs0.lookup a).isSome then
      let clif := (fi.clif.replace s!"%{a}(" s!"%{n}(").replace s!"function %{n}(" s!"function %{a}("
      aliasFns := aliasFns ++ [{ fi with clif }]
      aliases := aliases ++ [(a, n)]
  let progNames := names ++ aliases.map (·.1)
  let outside := addrs0.filter fun p => !progNames.contains p.1
  let dataSyms : List String := (((j.getObjVal? "data_syms").bind (·.getArr?)).toOption.getD #[]).toList.filterMap
    (·.getStr?.toOption)
  let symNames := (((fis.toList ++ aliasFns).flatMap fun fi => addrNamesOf fi.func) ++
    dataSyms.filter names.contains).eraseDups
  let some R := names.head?.bind (addrs0.lookup ·)
    | do IO.eprintln "lean-link: no function, or the first has no address"; return 1
  let S : LinkSpec := { funcs := fis.toList, aliases, aliasFns, outside, symNames, R }
  -- rust-lld put the region's functions where the placement does
  let mut moved : List String := []
  for (n, a) in S.progAddrs do
    if addrs0.lookup n != some a then
      moved := moved ++ [s!"{n}: placed at {hex a}, linked at {(addrs0.lookup n).map hex}"]
  if !moved.isEmpty then
    IO.eprintln s!"lean-link: rust-lld did not link {moved.length} function(s) at their placement, e.g. {moved.head!}"
    return 1
  let file0 ← IO.FS.readBinFile exe
  match leanLink S file0 with
  | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
  | .ok file =>
    IO.FS.writeBinFile exe file
    IO.println s!"lean-link: {exe}: {names.length} function(s) ({aliases.length} self-call alias(es)), region {hex R}..{hex (R + S.size)} ({S.size} bytes) written by Link.leanLink"
    return 0
