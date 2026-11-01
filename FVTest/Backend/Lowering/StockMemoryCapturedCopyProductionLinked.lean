import FV.Backend.Lowering.StockMemoryCapturedCopyNI
import FV.Backend.MemoryCapturedCopyNIProduction
import FVTest.Backend.Lowering.StockScalarTestSupport
import FV.E2E.SemanticChecksWith
import FV.E2E.SemanticStackBound
import FV.Link.ProductionImageWith
import FV.Link.Ld.Spec
import FVTest.E2E.SemanticLinkProofWith
import FV.Backend.LinearScan

/-! Actual Stock callback → actual byte writer → ordinary emitted Lean proofs.
A fixed integration witness; it does not activate a production class. -/
set_option autoImplicit false
namespace FVTest.StockMemoryCapturedCopyProductionLinked
open _root_.Backend _root_.Backend.Proof.Driver _root_.E2E _root_.E2E.LinkCheck _root_.E2E.BinCheck _root_.E2E.Elf Link

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def get {α : Type} (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)

private def oracle (vc : VCode) : Except String Lean.Json := do
  let (_,answers) := allocateLeanAnswers #[vc]
  Lean.Json.parse answers[0]!


private def plan (s : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + s.size
  { base := 0x200000, entry := s.R,
    segs := [{kind := 1, vaddr := 0x200000, offset := 0, filesz := size, memsz := size}],
    tlsAddr := 0x200000 + size, tlsOff := size, tlsFilesz := 0, tlsMemsz := 0, tlsAlign := 1,
    ehOff := 0, ehAddr := 0, ehSize := 0, size, pieces := [], secs := #[],
    syms := s.addrs.toArray.map fun (n, value) =>
      {name := symName n, value, info := 18, shndx := 0xfff1} }

private def originalName : String := "_RNxC7fv_demo12HezxnGHZarII"

def fixture (captured : String) (name : String) (i : Nat) : String :=
  if i == 0 then captured.replace originalName name
  else if i == 2 then
    "function %" ++ name ++ "(i64) -> i64 system_v {\nblock0(v0: i64):\n    return v0\n}\n"
  else
    "function %" ++ name ++ "(i64) system_v {\nblock0(v0: i64):\n    nop\n    jump block1\n" ++
      "block1:\n    nop\n    v2 = load.i64 notrap v0+8\n    nop\n" ++
      "    v3 = load.i64 notrap v0\n    nop\n    store.i64 notrap v2, v3\n    nop\n    return\n}\n"

private def checkOne (out : System.FilePath) (captured : String) (cleanup fallback : Bool) : IO Unit := do
  let actualLower := Stock.MemoryCapturedCopy.lowerValidated
  let lowerName := "Backend.Stock.MemoryCapturedCopy.lowerValidated"
  let names := [originalName,"memory_copy1","memory_retained"]
  let fixtureSource := fun name i => fixture captured name i
  let clif := String.join (names.zipIdx.map fun (name,i) => fixture captured name i)
  let parsed := Clif.parseFile clif
  let production ← compileFileMemoryCapturedCopyNIWhen true (fun vcs => do
    for vc in vcs do
      let some source := parsed.funcs.find? (fun p => p.name == vc.name)
        | throw (IO.userError "allocator source missing")
      let f ← match source.func with
        | .ok f => pure f
        | .error error => throw (IO.userError s!"{repr error}")
      let expected ← get ((actualLower f).bind (fun raw => prepare (productionStage cleanup f raw)))
      require (decide (vc = expected)) "allocator missed the actual prepared Stock artifact"
    pure (allocateLean vcs)) parsed [] cleanup
  require (production.funcs.length == 3 && production.unsupported.isEmpty && production.unverified.isEmpty &&
    production.unvalidated.isEmpty) "default production lost a verified stage"
  let stem := s!"memory-{if cleanup then "cleanup" else "plain"}"
  IO.FS.writeBinFile (out / (stem ++ ".o")) (← get production.object)
  IO.FS.writeFile (out / (stem ++ ".json")) production.tableJson
  let prior ← compileFileMemoryLoadStoreNIWhen true (fun vcs => pure (allocateLean vcs)) parsed [] cleanup
  let attempts ← IO.mkRef (0 : Nat)
  let retried ← compileFileMemoryCapturedCopyNIWhen true (fun vcs => do
    let count ← attempts.get
    attempts.set (count+1)
    if count == 0 then pure (vcs.map fun _ => .error "forced memory-attempt failure")
    else pure (allocateLean vcs)) parsed [] cleanup
  require ((← attempts.get) ≥ 2 && decide (retried.object = prior.object)) "complete previous pipeline retry changed its bytes"
  let mut funcs : List FnInput := names.zipIdx.map fun (_,k) => {clif,ra := "null",k,j := k+1}
  let mut answers : Array Lean.Json := #[Lean.Json.null]
  for fi in funcs do
    let raw ← get (actualLower fi.func)
    let prep ← get (prepare (productionStage cleanup fi.func raw))
    answers := answers.push (← get (oracle prep))
  let ra := (Lean.Json.mkObj [("functions",Lean.Json.arr answers)]).compress
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

  for (fi,i) in funcs.zipIdx do
    let a ← get (input.pipeProductionWith actualLower cleanup fi)
    let selected ← get (actualLower fi.func)
    require (decide (a.vc = selected) && a.vc.rulesFired == selected.rulesFired) "actual memory artifact/history binding changed"
    if i < 2 then
      let raw ← get (Stock.lower fi.func)
      require (Stock.MemoryCapturedCopy.check fi.func raw.code && SemanticNI.check fi.func raw.code &&
        decide (a.vc = raw.code))
        "memory class fell back or retained the legacy vreg mapping"
    else
      let prior ← get (Stock.ParameterCfg.lowerValidated fi.func)
      require (decide (a.vc = prior)) "prior production class changed"
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

  for perEntry in [false,true] do
    let label := s!"StockMemoryCapturedCopyProduction{if cleanup then "Cleanup" else "Plain"}{if fallback then "Fallback" else "Strict"}{if perEntry then "Entries" else "Global"}"
    let executable := out / (label ++ ".elf")
    IO.FS.writeBinFile executable file
    let bundle := out / (label ++ "-bundle")
    IO.FS.createDirAll bundle
    let data := bundle / "data.clif"
    IO.FS.writeFile data ""
    let mut functions : Array Lean.Json := #[]
    for (name, i) in names.zipIdx do
      let dump := bundle / (name ++ ".clif")
      let answer := bundle / (name ++ ".ra.json")
      IO.FS.writeFile dump ("; symbol " ++ name ++ "\n" ++
        ((fixtureSource s!"u0:{i}" i).replace "function %" "function ") ++
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
    for (path,text) in FVTest.E2E.SemanticLinkProofWith.leanFilesSemanticWith lowerName input names names
        proof.toString label executable.toString cleanup true
        (if perEntry then none else stack) (if perEntry then names else []) bg
        (lowerImport := "FV.Backend.Lowering.StockMemoryCapturedCopyNI") do
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path text
    IO.FS.writeFile (out / (label ++ ".clif")) clif
    IO.println s!"ACTUAL_STOCK_MEMORY_LINK {label}: source/artifact/ELF/stack/proof emission passed"

def check (out : System.FilePath) (captured : String) : IO Unit := do
  let parsed := Clif.parseFile captured
  let some original := parsed.funcs[0]?
    | throw (IO.userError "the original captured function is missing")
  require (parsed.funcs.length == 1 && original.name == originalName)
    "the original captured function changed its identity"
  let source ← match original.func with
    | .ok f => pure f
    | .error error => throw (IO.userError s!"{repr error}")
  require (Stock.MemoryCapturedCopy.sourceOk source) "the original capture missed the proved source class"
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do checkOne out captured cleanup fallback

end FVTest.StockMemoryCapturedCopyProductionLinked

def main (args : List String) : IO UInt32 := do
  let some capture := ((args.dropWhile (· != "--capture")).drop 1).head?
    | throw (IO.userError "--capture requires the original captured input")
  let captured ← IO.FS.readFile capture
  FVTest.StockMemoryCapturedCopyProductionLinked.check
    (System.FilePath.mk (args[0]?.getD "/tmp/stock-captured-copy-linked")) captured
  pure 0
