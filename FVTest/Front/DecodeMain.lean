module

public import FV.Front.Bundle
public import FV.Front.Raw

@[expose] public section

/-! # `lake exe clif-decode DIR STAGE OUT [--split] [--data-file F]`: cg_clif's dumps decoded

`DIR` is a dump directory (`<unit>.clif/`, written by the patched cg_clif,
`scripts/build-cg-clif.sh`); `STAGE` is `unopt` or `opt`. Every `*.STAGE.clif` dump is read
(`Front.readDump`) and decoded under its own declarations (`Front.unitTable [d]`,
`Front.decodeFn`, docs/contracts/frontend.md §2): the function with every external name replaced
by the CLIF name of the symbol cg_clif declared for it. Each dump's table declares every name its
function uses, so the decoding is the one under the unit's declarations whenever those are
consistent (`Front.parseUnit` checks that for the functions of a bundle); a directory may hold
several codegen units. The output text is the dump's header and the printed decoded function,
checked to parse back to it (`Front.mkInput`), so a tool parsing it reads exactly the decoded
function.

* `--split`: `OUT` is a directory; each dump `X.STAGE.clif` that decodes gets `OUT/X.STAGE.clif`,
  each one that does not gets `OUT/X.STAGE.clif.err` with the reason (`cargo fv`: the function
  falls back to cg_clif's code with that reason).
* otherwise `OUT` is one file: the first dump's header, the lines of `--data-file` (`; data:`
  directives), every decoded function (dumps that do not decode are reported on stderr and left
  out).

Exit status 0 unless on an I/O error: a dump that does not decode is not an error of the tool.
-/

open Front

/-- The decoded function under its own declarations and its file text (header, printed
function), checked to parse back. -/
def decodeText (d : Dump) : Except String (Clif.Function × String) := do
  let ρ ← unitTable [d]
  let g ← decodeFn ρ d
  let fi ← mkInput d.header g ""
  pure (g, fi.clif)

def main (args : List String) : IO UInt32 := do
  let flags := args.filter (·.startsWith "--")
  let pos := (args.filter (!·.startsWith "--"))
  let dataFile? := match args.dropWhile (· != "--data-file") with
    | _ :: f :: _ => some f
    | _ => none
  let pos := pos.filter (some · != dataFile?)
  let split := flags.contains "--split"
  let [dir, stage, out] := pos | do
    IO.eprintln "usage: clif-decode DIR STAGE OUT [--split] [--data-file F]"
    return 2
  let sfx := s!".{stage}.clif"
  let mut files : Array System.FilePath := #[]
  for e in ← System.FilePath.readDir dir do
    if e.fileName.endsWith sfx then files := files.push e.path
  let sorted := files.qsort (fun a b => a.toString < b.toString)
  let mut dumps : Array (System.FilePath × Except String Dump) := #[]
  for p in sorted do
    dumps := dumps.push (p, readDump (← IO.FS.readFile p))
  if split then
    IO.FS.createDirAll out
  let mut texts : Array String := #[]
  let mut header : Option (List String) := none
  let mut nok := 0
  for (p, r) in dumps do
    let name := p.fileName.getD p.toString
    match r.bind fun d => (decodeText d).map (d.header, ·) with
    | .ok (hdr, g, t) =>
      nok := nok + 1
      if split then IO.FS.writeFile (System.FilePath.mk out / name) t
      else
        if header.isNone then header := some hdr
        texts := texts.push g.print
    | .error e =>
      if split then IO.FS.writeFile (System.FilePath.mk out / (name ++ ".err")) (e ++ "\n")
      else IO.eprintln s!"clif-decode: {name}: {e}"
  if !split then
    let data ← match dataFile? with
      | some f => pure ((← IO.FS.readFile f).trimAsciiEnd.toString ++ "\n")
      | none => pure ""
    let hdr := String.intercalate "\n" (header.getD [])
    IO.FS.writeFile out (hdr ++ "\n" ++ data ++ "\n" ++ String.intercalate "\n" texts.toList)
  IO.eprintln s!"clif-decode: {dir} {stage}: {nok} of {dumps.size} dumps decoded"
  return 0
