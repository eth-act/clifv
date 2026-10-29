module

public import FV.Link.ProductionImage
public import FV.Link.Ld.Spec
public import FVTest.E2E.ProductionLinkProof
public import FV.Backend.Lowering.StockProduction

@[expose] public section

/-! Actual Stock callback → actual byte writer → ordinary emitted Lean proofs.
A fixed integration witness; it does not activate a production class. -/
set_option autoImplicit false
namespace FVTest.StockProductionLinkedFixture
open Backend _root_.E2E _root_.E2E.LinkCheck _root_.E2E.BinCheck _root_.E2E.Elf Link


private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def get {α : Type} (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)

private def oracle (vc : VCode) : Except String Lean.Json := do
  let mut rows : Array (Array String) := #[]
  for b in vc.blocks do
    for i in b.insts do
      let ops ← i.operands
      rows := rows.push (Array.replicate ops.size "x0")
  pure <| Lean.Json.mkObj [("ok", Lean.toJson true), ("checker", Lean.toJson "ok"),
    ("allocs", Lean.toJson rows), ("edits", Lean.Json.arr #[]),
    ("num_spillslots", Lean.toJson (0 : Nat))]

private def sourceText (name : String) : String :=
  "function %" ++ name ++ "(i64) -> i64 system_v {\nblock0(v0: i64):\n    nop\n    jump block1\nblock1:\n    nop\n    return v0\n}\n"

private def plan (s : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + s.size
  { base := 0x200000, entry := s.R,
    segs := [{kind := 1, vaddr := 0x200000, offset := 0, filesz := size, memsz := size}],
    tlsAddr := 0x200000 + size, tlsOff := size, tlsFilesz := 0, tlsMemsz := 0, tlsAlign := 1,
    ehOff := 0, ehAddr := 0, ehSize := 0, size, pieces := [], secs := #[],
    syms := s.addrs.toArray.map fun (n, value) =>
      {name := symName n, value, info := 18, shndx := 0xfff1} }

private def checkCase (out : System.FilePath) (count : Nat) (cleanup fallback : Bool) (mixed : Bool := false) : IO Unit := do
  let names := (List.range count).map fun i => s!"actual_stock_prologue_{i}"
  let clif := String.join (names.zipIdx.map fun (n,i) =>
    if mixed && i+1 == count then
      "function %" ++ n ++ "(i64) -> i64 system_v {\n    fn0 = colocated %" ++ names[0]! ++
      "(i64) -> i64 system_v\nblock0(v0: i64):\n    v1 = call fn0(v0)\n    v2 = iconst.i64 1\n    v3 = iadd v1, v2\n    return v3\n}\n"
    else sourceText n)
  let mut funcs : List FnInput := names.zipIdx.map fun (_, k) => {clif, ra := "null", k, j := k+1}
  let mut answers : Array Lean.Json := #[Lean.Json.null]
  for fi in funcs do
    let raw ← get (Stock.Production.lower fi.func)
    let prep ← get (prepare (productionStage cleanup fi.func raw))
    let answer ← if mixed then pure Lean.Json.null else get (oracle prep)
    if !mixed then
      require (checkAlloc prep (← get (buildRFunc prep (← get (parseRAOut answer))))).isOk
        "fixed oracle rejected actual prepared Stock code"
    answers := answers.push answer
  let ra := (Lean.Json.mkObj [("functions", Lean.Json.arr answers)]).compress
  funcs := funcs.map fun fi => {fi with ra}
  let initial : LinkSpec := {funcs, names, sizes := [], outside := [], symNames := names, R := 0x200160}
  let mut sizes : List Nat := []
  for fi in funcs do
    let a ← get (initial.input0.pipeProduction cleanup fi)
    sizes := sizes ++ [a.fb.words.size]
  let spec := {initial with sizes}
  let pl := plan spec
  let image ← get (Link.Ld.assemble pl)
  require (pl.specOkB spec) "actual fixture failed default ELF plan provenance"
  let file ← get (leanLinkProduction spec image.write cleanup)
  let input := {spec.inputProduction cleanup with fallback}
  let results := input.resultsProduction cleanup
  require (okRWith (productionStage cleanup) input results) "actual callback program checks failed"
  for e in results do
    let a ← get e.2
    let old ← get (lowerFunction e.1)
    if mixed && e.1.name == names[count-1]! then
      require (a.vc.rulesFired == old.rulesFired) "legacy caller did not retain its route"
    else require (!(a.vc.rulesFired == old.rulesFired)) "fixture lost distinct actual Stock history"
  let ex : Excerpt := [(0, file)]
  let index := _root_.symIndex file
  let cert := input.addrs.filterMap fun p => (index.get? (symName p.1, p.2)).map (p.1, ·)
  require (hdrB ex && symsB input ex cert &&
    codeBProduction input cleanup ex input.funcs)
    "actual callback ELF/code-table checks failed"
  let bg : BinGen := ⟨ex, [ex, ex], [], ex, cert, []⟩
  let ci : ProductionStackBound.CompilerInput := {toLinkInput := input, cleanup}
  let stack := ProductionStackBound.stackB ci
  require stack.isSome "fixed no-call program has no stack bound"
  for perEntry in (if count > 32 then [false,true] else [false]) do
    let label := s!"StockProduction{count}{if mixed then "Mixed" else ""}{if cleanup then "Cleanup" else "Plain"}{if fallback then "Fallback" else "Strict"}{if perEntry then "Entries" else "Global"}"
    let executable := out / (label ++ ".elf")
    IO.FS.writeBinFile executable file
    if count == 2 && fallback && !mixed then
      let bundle := out / (label ++ "-bundle")
      IO.FS.createDirAll bundle
      let data := bundle / "data.clif"
      IO.FS.writeFile data ""
      let mut functions : Array Lean.Json := #[]
      for (name, i) in names.zipIdx do
        let dump := bundle / (name ++ ".clif")
        let answer := bundle / (name ++ ".ra.json")
        IO.FS.writeFile dump ("; symbol " ++ name ++ "\n" ++
          ((sourceText s!"u0:{i}").replace "function %" "function ") ++
          s!"; clifv-extnames 1\n; decl u0:{i} func export " ++
          (Lean.toJson name).compress ++ "\n; end clifv-extnames\n")
        IO.FS.writeFile answer ((Lean.Json.mkObj [
          ("functions",Lean.Json.arr #[answers[i+1]!])]).compress)
        functions := functions.push (Lean.Json.mkObj [
          ("name",Lean.toJson name),("dump",Lean.toJson dump.toString),
          ("ra",Lean.toJson answer.toString)])
      let unit := Lean.Json.mkObj [("tag",Lean.toJson "stock-production"),
        ("functions",Lean.Json.arr functions),("data",Lean.toJson data.toString),
        ("locals",Lean.Json.arr #[]),("names",Lean.Json.mkObj (names.map fun n => (n,Lean.toJson n))),
        ("local_addrs",Lean.Json.arr #[])]
      let body := Lean.Json.mkObj [("format",Lean.toJson "clifv-frontend-bundle"),
        ("version",Lean.toJson (2 : Nat)),("exe",Lean.toJson executable.toString),
        ("units",Lean.Json.arr #[unit]),("symbols",Lean.toJson spec.addrs),
        ("markers",Lean.toJson spec.addrs),("skipped",Lean.Json.arr #[])]
      IO.FS.writeFile (bundle / "bundle.json") body.pretty
    let proof := out / "Crates" / (label ++ ".lean")
    for (path, text) in FVTest.E2E.ProductionLinkProof.leanFilesProduction input names names
        proof.toString label executable.toString cleanup true
        (if perEntry then none else stack) (if perEntry then names else []) bg do
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path text
    IO.println s!"ACTUAL_STOCK_LINK {label}: program/checker/ELF/history/stack/proof emission passed"

def check (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do checkCase out 2 cleanup fallback
  checkCase out 33 true true
  checkCase out 2 false true true
  checkCase out 2 true true true
end FVTest.StockProductionLinkedFixture

def main (args : List String) : IO Unit :=
  FVTest.StockProductionLinkedFixture.check (args.headD "/tmp/stock-production-linked-fixture")
