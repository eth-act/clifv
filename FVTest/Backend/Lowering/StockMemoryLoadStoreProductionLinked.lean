import FV.Backend.Lowering.StockMemoryLoadStoreNI
import FV.Backend.MemoryLoadStoreNIProduction
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
namespace FVTest.StockMemoryLoadStoreProductionLinked
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

def fixture (resultTy : String) (name : String) (i : Nat) (storeTy : String := "i32") (storeOp : String := "store") : String :=
  if i == 2 then
    "function %" ++ name ++ "(i64) -> i64 system_v {\nblock0(v0: i64):\n    return v0\n}\n"
  else
    let pointer := if i == 0 then "v0" else "v2"
    "function %" ++ name ++ "(i64, " ++ storeTy ++ ", i64) -> " ++ resultTy ++
      " system_v {\nblock0(v0: i64, v1: " ++ storeTy ++ ", v2: i64):\n" ++
      "    v3 = load." ++ resultTy ++ " notrap v0\n    " ++ storeOp ++ "." ++ storeTy ++
      " notrap v1, " ++ pointer ++ "\n    return v3\n}\n"

private def checkOne (out : System.FilePath) (resultTy : String) (cleanup fallback : Bool) (loadTy loadOp : String) : IO Unit := do
  let actualLower := Stock.MemoryLoadStore.lowerValidated
  let lowerName := "Backend.Stock.MemoryLoadStore.lowerValidated"
  let names := ["memory_store0","memory_store1","memory_retained"]
  let fixtureSource := fun name i => fixture resultTy name i loadTy loadOp
  let clif := String.join (names.zipIdx.map fun (name,i) => fixture resultTy name i loadTy loadOp)
  let parsed := Clif.parseFile clif
  let production ← compileFileMemoryLoadStoreNIWhen true (fun vcs => do
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
  let prior ← compileFileMemoryStoreCfgNIWhen true (fun vcs => pure (allocateLean vcs)) parsed [] cleanup
  let attempts ← IO.mkRef (0 : Nat)
  let retried ← compileFileMemoryLoadStoreNIWhen true (fun vcs => do
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
      require (Stock.MemoryLoadStore.check fi.func raw.code && SemanticNI.check fi.func raw.code &&
        decide (a.vc = raw.code) && !Backend.Proof.Driver.lowerCheck fi.func raw.code)
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
    let label := s!"StockMemoryLoadStoreProduction{if cleanup then "Cleanup" else "Plain"}{if fallback then "Fallback" else "Strict"}{if perEntry then "Entries" else "Global"}"
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
        (lowerImport := "FV.Backend.Lowering.StockMemoryLoadStoreNI") do
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path text
    IO.FS.writeFile (out / (label ++ ".clif")) clif
    IO.println s!"ACTUAL_STOCK_MEMORY_LINK {label}: source/artifact/ELF/stack/proof emission passed"

def check (out : System.FilePath) (resultTy : String) (storeTy : String := "i64") (storeOp : String := "store") : IO Unit := do
  require (#["i8","i16","i32","i64"].contains resultTy) "unsupported load fixture type"
  require (#["i8","i16","i32","i64"].contains storeTy) "unsupported store fixture type"
  require (#["store","istore8","istore16","istore32"].contains storeOp) "unsupported store fixture opcode"
  let width := if storeTy == "i8" then 8 else if storeTy == "i16" then 16 else if storeTy == "i32" then 32 else 64
  let written := if storeOp == "store" then width else if storeOp == "istore8" then 8 else if storeOp == "istore16" then 16 else 32
  require (written ≤ width) "store fixture narrows beyond the original value width"
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do checkOne out resultTy cleanup fallback storeTy storeOp

end FVTest.StockMemoryLoadStoreProductionLinked

def main (args : List String) : IO UInt32 := do
  let loadTy := ((args.dropWhile (· != "--load-type")).drop 1).head?.getD "i64"
  let storeTy := ((args.dropWhile (· != "--store-type")).drop 1).head?.getD "i64"
  let storeOp := ((args.dropWhile (· != "--store-op")).drop 1).head?.getD "store"
  FVTest.StockMemoryLoadStoreProductionLinked.check
    (System.FilePath.mk (args[0]?.getD "/tmp/stock-load-store-linked")) loadTy storeTy storeOp
  pure 0
