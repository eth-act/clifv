import FV.E2E.SemanticStackBound
import FV.E2E.SemanticChecksWith
import FV.Link.ProductionImageWith
import FV.Link.Ld.Spec
import FVTest.E2E.SemanticLinkProofWith
import FV.Backend.Lowering.StockLogicalNI
import FV.E2E.StockProductionFixtures
import FV.Backend.LinearScan
import FV.Clif.Print
import FV.E2E.StockLogicalFixtures

/-! Actual Stock callback → actual byte writer → ordinary emitted Lean proofs.
A fixed integration witness; it does not activate a production class. -/
set_option autoImplicit false
namespace FVTest.StockLogicalLinkedFixture
open Backend _root_.E2E _root_.E2E.LinkCheck _root_.E2E.BinCheck _root_.E2E.Elf Link


private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def get {α : Type} (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)

private def oracle (vc : VCode) : Except String Lean.Json := do
  let (_,answers) := allocateLeanAnswers #[vc]
  Lean.Json.parse answers[0]!

private def configFor (i : Nat) : Stock.D0.Configuration :=
  ([.systemVI64, .defaultI32, .systemVI32, .fastI32, .defaultI64, .fastI64] : List Stock.D0.Configuration)[i % 6]!

private def sourceText (name : String) (c : Stock.D0.Configuration)
    (retainedMixed : Bool := false) : String :=
  let f := {E2E.StockLogicalNIWitness.function c with name}
  -- A further dead operation distinguishes retained plain artifacts from the
  -- demand-driven Stock output, exercising consumer reconstruction fallback.
  let f := if retainedMixed then {f with blocks := f.blocks.map fun b =>
    {b with body := b.body ++ [⟨[15],.binary .iadd (Stock.D0.valueType c) 0 1⟩]}} else f
  f.print

private def plan (s : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + s.size
  { base := 0x200000, entry := s.R,
    segs := [{kind := 1, vaddr := 0x200000, offset := 0, filesz := size, memsz := size}],
    tlsAddr := 0x200000 + size, tlsOff := size, tlsFilesz := 0, tlsMemsz := 0, tlsAlign := 1,
    ehOff := 0, ehAddr := 0, ehSize := 0, size, pieces := [], secs := #[],
    syms := s.addrs.toArray.map fun (n, value) =>
      {name := symName n, value, info := 18, shndx := 0xfff1} }

private def checkCase (out : System.FilePath) (count : Nat) (cleanup fallback : Bool) (mixed : Bool := false) (retainedMixed : Bool := false) : IO Unit := do
  let actualLower := if retainedMixed then Stock.Mixed.lowerValidated else Stock.Logical.lowerValidated
  let lowerName := if retainedMixed then "Backend.Stock.Mixed.lowerValidated" else "Backend.Stock.Logical.lowerValidated"
  let names := (List.range count).map fun i => s!"actual_stock_logical_{i}"
  let clif := String.join (names.zipIdx.map fun (n,i) =>
    if !mixed || i == 0 then sourceText n (configFor i) retainedMixed
    else if i == 1 then ({E2E.StockArithmeticNIWitness.function .systemVI64 with name := n}).print
    else if i == 2 then (Stock.Prologue.source n .systemVI64 []).print
    else if i == 3 then (Stock.D0.source n .fastI32 []).print
    else if i == 4 then
      "function %" ++ n ++ "() -> i64 {\nblock0:\n    v0 = iconst.i64 7\n    return v0\n}\n"
    else
      "function %" ++ n ++ "(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v {\n    fn0 = colocated %" ++ names[0]! ++
      "(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v\nblock0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64, v5: i64, v6: i64, v7: i64, v8: i64):\n    v9 = call fn0(v0, v1, v2, v3, v4, v5, v6, v7, v8)\n    v10 = iconst.i64 1\n    v11 = iadd v9, v10\n    return v11\n}\n")
  let mut funcs : List FnInput := names.zipIdx.map fun (_, k) => {clif, ra := "null", k, j := k+1}
  let mut answers : Array Lean.Json := #[Lean.Json.null]
  for fi in funcs do
    let raw ← get (actualLower fi.func)
    let prep ← get (prepare (productionStage cleanup fi.func raw))
    let answer ← if mixed then pure Lean.Json.null else get (oracle prep)
    answers := answers.push answer
  let ra := (Lean.Json.mkObj [("functions", Lean.Json.arr answers)]).compress
  funcs := funcs.map fun fi => {fi with ra}
  let initial : LinkSpec := {funcs, names, sizes := [], outside := [], symNames := names, R := 0x200160}
  let mut sizes : List Nat := []
  for fi in funcs do
    let a ← get (initial.input0.pipeProductionWith actualLower cleanup fi)
    sizes := sizes ++ [a.fb.words.size]
  let spec := {initial with sizes}
  let pl := plan spec
  let image ← get (Link.Ld.assemble pl)
  require (pl.specOkB spec) "actual fixture failed default ELF plan provenance"
  let file ← get (leanLinkProductionWith actualLower spec image.write cleanup)
  let input := {spec.inputProductionWith actualLower cleanup with fallback}
  let results := input.resultsProductionWith actualLower cleanup
  if !(okRSemanticNI (productionStage cleanup) input results) then
    IO.println s!"GLOBAL {bad (globalChks input (progOf results) (tabOf results))}"
    for e in results do IO.println s!"FUNCTION {e.1.name}: {bad (chksSemanticNI (productionStage cleanup) input (progOf results) (tabOf results) e.1 e.2)}"
    throw (IO.userError "actual callback program checks failed")
  for e in results do
    let a ← get e.2
    let old ← get (lowerFunction e.1)
    if !retainedMixed && (!mixed || e.1.name == names[0]!) then
      require (!Backend.Proof.Driver.lowerCheck e.1 a.vc) "raw arithmetic artifact silently took legacy fallback"
    else
      let previous ← get (Stock.Mixed.lowerValidated e.1)
      require (decide (a.vc = previous)) "a retained class changed its actual code or history"
    let selected ← get (actualLower e.1)
    require (a.vc.rulesFired == selected.rulesFired) "fixture changed selected lowering history"
  let ex : Excerpt := [(0, file)]
  let index := _root_.symIndex file
  let cert := input.addrs.filterMap fun p => (index.get? (symName p.1, p.2)).map (p.1, ·)
  require (hdrB ex && symsB input ex cert &&
    SemanticChecksWith.codeBProduction actualLower input cleanup ex input.funcs)
    "actual callback ELF/code-table checks failed"
  let bg : BinGen := ⟨ex, [ex, ex], [], ex, cert, []⟩
  let ci : SemanticStackBound.CompilerInput := {toLinkInput := input, cleanup, lower := actualLower}
  let stack := SemanticStackBound.stackB ci
  require stack.isSome "fixed program has no stack bound"
  for perEntry in (if count > 32 then [false,true] else [false]) do
    let label := s!"StockLogical{count}{if retainedMixed then "Retained" else ""}{if mixed then "Mixed" else ""}{if cleanup then "Cleanup" else "Plain"}{if fallback then "Fallback" else "Strict"}{if perEntry then "Entries" else "Global"}"
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
          ((sourceText s!"u0:{i}" (configFor i) retainedMixed).replace "function %" "function ") ++
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
    for (path, text) in FVTest.E2E.SemanticLinkProofWith.leanFilesSemanticWith lowerName input names names
        proof.toString label executable.toString cleanup true
        (if perEntry then none else stack) (if perEntry then names else []) bg (lowerImport := "FV.Backend.Lowering.StockLogicalNI") do
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path text
    IO.println s!"ACTUAL_STOCK_LINK {label}: program/checker/ELF/history/stack/proof emission passed"

def check (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do checkCase out 6 cleanup fallback
    checkCase out 2 cleanup true
  checkCase out 33 true true
  checkCase out 6 false true true
  checkCase out 6 true true true
  checkCase out 2 false true false true
  checkCase out 2 true true false true
end FVTest.StockLogicalLinkedFixture

def main (args : List String) : IO Unit :=
  FVTest.StockLogicalLinkedFixture.check (args.headD "/tmp/stock-mixed-linked-fixture")
