import FV.Backend
import FV.Backend.Lowering.StockReplay
import FV.Opt.Legalize128Pass
import FVTest.Backend.StockConfig

/-! Development differential harness. Stock lowering is not yet composed with
the lowering proof. This harness validates allocation using the existing
allocator checker, and exports bytes for differential tests. The production
compiler continues to use its proved driver. -/

open Backend

def main (argv : List String) : IO UInt32 := do
  let (input, output, config) ← match argv with
    | [input, output] => pure (input, output, none)
    | [input, output, request] => do
      let checked := Lean.Json.parse (← IO.FS.readFile request) >>= StockConfig.parse
      match checked with
      | .ok c => pure (input, output, some c)
      | .error e => throw (IO.userError e)
    | _ => throw (IO.userError "usage: lean-stock-lowering-test INPUT.clif OUTPUT_DIRECTORY [STOCK_CONFIG.json]")
  IO.FS.createDirAll output
  let parsed := Opt.Legalize128.parsedFile128 (Clif.parseFile (← IO.FS.readFile input))
  let some allocator ← Allocator.ofName? "regalloc2" | throw (IO.userError "allocator not found")
  let mut vcs := #[]
  for pf in parsed.file.funcs do
    let f ← match pf.func with
      | .ok f => pure f
      | .error e => throw (IO.userError e.toString)
    let r ← match Stock.lower f with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{pf.name}: {e}")
    unless r.scans.all Stock.ScanEvent.check do
      throw (IO.userError s!"{pf.name}: stock backward-scan replay rejected")
    unless r.blockScans.all Stock.BlockScanEvent.check do
      throw (IO.userError s!"{pf.name}: stock complete block-scan replay rejected")
    -- The production VCode contract attaches arguments to jumps. Test only
    -- cases representable by that contract until its proof migration lands.
    for (b, bi) in r.code.blocks.zipIdx do
      if r.order.successors[bi]!.size > 1 && r.edgeArgs[bi]!.any (!·.isEmpty) then
        throw (IO.userError "per-successor arguments require the pending VCode proof migration")
      if b.insts.isEmpty then throw (IO.userError "empty selected block")
    vcs := vcs.push r.code
  let rejected ← IO.mkRef #[]
  let clif name := parsed.file.funcs.filterMap fun p =>
    if p.name == name then p.func.toOption else none
  let allocated ← match config with
    | none => allocator.run vcs
    | some c => StockConfig.allocate c clif rejected allocator vcs
  for (af, i) in allocated.zipIdx do
    let af ← match af with
      | .ok af => pure af
      | .error e => throw (IO.userError e)
    let a ← match emitFunc i af with
      | .ok a => pure a
      | .error e => throw (IO.userError e)
    let bin ← match a.layout with
      | .ok bin => pure bin
      | .error e => throw (IO.userError e)
    let base := System.FilePath.mk output / a.name
    IO.FS.writeBinFile (base.addExtension "bin") (wordsBytes bin.words)
    IO.FS.writeFile (base.addExtension "s") a.text
    IO.FS.writeFile (base.addExtension "relocs.json") bin.relocsJson
    IO.FS.writeFile (base.addExtension "traps.json") bin.trapsJson
  return 0
