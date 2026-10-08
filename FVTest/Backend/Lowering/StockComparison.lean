import FV.Backend
import FV.Backend.Lowering.StockReplay
import FV.Opt.Legalize128Pass
import FVTest.Backend.StockConfig

/-! Settings-matched artifact comparison for the development stock driver.
Production lowering is unchanged. Allocation, emission, caller rejection, settings
receipts, and ELF/dump artifacts follow the existing comparison contract. -/

open Backend

private def compileStockWith {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    : m FileAsm := do
  -- lowering (per function, in file order)
  let lowered : Array (String × Except String (Clif.Function × VCode)) :=
    pf.funcs.toArray.map fun p => (p.name, match p.func with
      | .error e => .error e.toString
      | .ok f => (do
          let r ← Stock.lower f
          unless r.scans.all Stock.ScanEvent.check && r.blockScans.all Stock.BlockScanEvent.check do
            throw "stock scan replay rejected"
          for (b, bi) in r.code.blocks.zipIdx do
            if r.order.successors[bi]!.size > 1 && r.edgeArgs[bi]!.any (!·.isEmpty) then
              throw "per-successor arguments require the pending VCode proof migration"
            if b.insts.isEmpty then throw "empty selected block"
          pure (f, r.code)))
  let vcs := lowered.filterMap fun (_, r) => r.toOption.map (·.2)
  let afs ← alloc vcs
  let mut done : Array (FnAsm × List String) := #[]
  let mut bad : Array (String × String) := #[]
  let mut unwind : Array (String × List (Nat × Cfi)) := #[]
  let mut lsda : Array (String × List CallSite) := #[]
  let mut rules : Std.HashSet Isle.RuleId := {}
  let mut j := 0
  for ((name, r), k) in lowered.zipIdx do
    match r with
    | .error e => bad := bad.push (name, e)
    | .ok (f, vc) =>
      let af := afs[j]?.getD (.error "allocator returned too few results")
      j := j + 1
      match af.bind fun af => do
          let a ← emitFunc k af
          pure (a, ← unwindRows af a, ← callSites af a) with
      | .ok (a, rows, sites) =>
        done := done.push (a, callees f)
        unwind := unwind.push (a.name, rows)
        if let some s := sites then lsda := lsda.push (a.name, s)
        rules := vc.rulesFired.foldl (·.insert ·) rules
      | .error e => bad := bad.push (name, e)
  -- propagate to callers (fixpoint; at most one round per function)
  for _ in [0:done.size] do
    let (keep, drop) := done.partition fun (_, cs) => cs.all fun c => (bad.find? (·.1 == c)).isNone
    if drop.isEmpty then break
    for (a, cs) in drop do
      let c := (cs.find? fun c => (bad.find? (·.1 == c)).isSome).getD "?"
      bad := bad.push (a.name, s!"calls %{c}, which is not compiled")
    done := keep
  let funcs := done.toList.map (·.1)
  let text := "  .text\n" ++ String.join (funcs.map (·.text ++ "\n"))
  let unverified := funcs.map (fun f => (f.name, "development stock lowering (proof migration incomplete)"))
  let unvalidated := []
  pure { text, funcs, unsupported := bad.toList, unverified, unvalidated,
         rules := rules.toArray.qsort (· < ·) |>.toList,
         unwind := unwind.toList.filter fun (n, _) => funcs.any (·.name == n),
         lsda := lsda.toList.filter fun (n, _) => funcs.any (·.name == n) }

def main (argv : List String) : IO UInt32 := do
  let (input, output, configPath, receiptPath, dump, traps) ← match argv with
    | [i, o, "--stock-config", c, "--config-receipt", r, "--dump", d, "--traps", t] =>
      pure (i, o, c, r, d, t)
    | _ => do
      IO.eprintln "usage: lean-stock-lowering-compare INPUT OUTPUT.o --stock-config REQUEST --config-receipt RECEIPT --dump DIR --traps TABLE"
      return 2
  let src ← IO.FS.readFile input
  let request ← match Lean.Json.parse (← IO.FS.readFile configPath) with
    | .ok j => pure j
    | .error e => do IO.eprintln e; return 2
  let checked := StockConfig.parse request
  let error := match checked with | .ok _ => none | .error e => some e
  IO.FS.writeFile receiptPath ((StockConfig.receipt request error).pretty ++ "\n")
  let c ← match checked with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"unsupported stock configuration: {e}"; return 3
  let source := Clif.parseFile src
  let pf := (Opt.Legalize128.parsedFile128 source).file
  let clif (name : String) : List Clif.Function :=
    (source.funcs ++ pf.funcs).filterMap fun p => if p.name == name then p.func.toOption else none
  let rejected ← IO.mkRef (#[] : Array (String × String))
  let some allocator ← Allocator.ofName? "regalloc2" | return 2
  let fa ← compileStockWith (StockConfig.allocate c clif rejected allocator) pf
  IO.FS.writeFile receiptPath
    ((StockConfig.receipt request none (some (← rejected.get).toList)).pretty ++ "\n")
  let fa := if c.unwind then fa else { fa with unwind := [] }
  match fa.layout with
  | .error e => IO.eprintln s!"encoding failed: {e}"; return 1
  | .ok fbs =>
    IO.FS.writeBinFile output (elfObject fbs fa.unwind fa.lsda none)
    IO.FS.createDirAll dump
    for (_, fb) in fbs do
      let base := System.FilePath.mk dump / fb.name
      IO.FS.writeBinFile (base.addExtension "bin") (wordsBytes fb.words)
      IO.FS.writeFile (base.addExtension "relocs.json") fb.relocsJson
      IO.FS.writeFile (base.addExtension "traps.json") fb.trapsJson
      let metadata := Lean.Json.mkObj [
        ("name", Lean.toJson fb.name), ("alignment", Lean.toJson (4 : Nat)),
        ("unwind_disabled", Lean.toJson (!c.unwind)),
        ("stack_maps", Lean.toJson ([] : List String)),
        ("exception_metadata_comparison_supported", Lean.toJson false)]
      IO.FS.writeFile (base.addExtension "metadata.json") (metadata.pretty ++ "\n")
  IO.FS.writeFile traps fa.tableJson
  for (name, why) in fa.unverified do IO.eprintln s!"%{name}: compiled, unverified: {why}"
  for (name, why) in fa.unsupported do IO.eprintln s!"%{name}: unsupported: {why}"
  return 0
