import FV.Backend.Lowering.StockParameterCfgNI
import FV.Backend.Lowering.StockConditionalForwardCfgNI
import FVTest.Backend.Lowering.StockTwoBlockProductionRuntime
import FV.Backend.Lowering.StockTwoBlockNI
import FV.Backend.Lowering.StockTwoBlockEntryNI
import FVTest.Backend.Lowering.StockScalarTestSupport
import FV.E2E.SemanticStackBound
import FV.E2E.SemanticChecksWith
import FV.Link.ProductionImageWith
import FV.Link.Ld.Spec
import FVTest.E2E.SemanticLinkProofWith
import FV.Backend.Lowering.StockScalarNI
import FV.E2E.StockGeneralDivFixtures
import FV.Backend.LinearScan
import FV.Clif.Print
import FVTest.Backend.Lowering.StockNarrowProductionRuntime
import FVTest.Backend.Lowering.StockMaskProductionRuntime

/-! Actual Stock callback → actual byte writer → ordinary emitted Lean proofs.
A fixed integration witness; it does not activate a production class. -/
set_option autoImplicit false
namespace FVTest.StockGeneralDivProductionLinkedFixture
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
    (layout : StockGeneralDivNIWitness.Layout) (retainedMixed : Bool := false) (i : Nat := 0) : String :=
  let original := if retainedMixed then
    E2E.StockReturnedDivNIWitness.function c (E2E.StockDivNIWitness.operations[i % 4]!) (i / 4 % 2 == 1)
    else E2E.StockGeneralDivNIWitness.function c (E2E.StockDivNIWitness.operations[i % 4]!) (i / 4 % 2 == 1) layout
  let f := {original with name}
  -- Retained mode selects the previous complete Logical lowering on this
  -- same eligible source. Its legacy artifact differs from raw Stock output,
  -- so real consumer reconstruction must discover a non-default route.
  let _ := retainedMixed
  f.print

private def plan (s : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + s.size
  { base := 0x200000, entry := s.R,
    segs := [{kind := 1, vaddr := 0x200000, offset := 0, filesz := size, memsz := size}],
    tlsAddr := 0x200000 + size, tlsOff := size, tlsFilesz := 0, tlsMemsz := 0, tlsAlign := 1,
    ehOff := 0, ehAddr := 0, ehSize := 0, size, pieces := [], secs := #[],
    syms := s.addrs.toArray.map fun (n, value) =>
      {name := symName n, value, info := 18, shndx := 0xfff1} }

private def checkCase (out : System.FilePath) (count : Nat) (cleanup fallback : Bool) (layout : StockGeneralDivNIWitness.Layout) (mixed : Bool := false) (retainedMixed : Bool := false) (narrow : Bool := false) (mask : Bool := false) (cfg : Bool := false) (cfgentry : Bool := false) (cfgscalarentry : Bool := false) (linear : Bool := false) (forward : Bool := false) (conditional : Bool := false) (conditionalForward : Bool := false) (parameter : Bool := false) : IO Unit := do
  let cfgentry := cfgentry || cfgscalarentry || linear || forward || conditional || conditionalForward || parameter
  let cfg := cfg || cfgentry
  let actualLower := if retainedMixed then (if parameter then Stock.ConditionalForwardCfg.lowerValidated else if conditionalForward then Stock.ConditionalCfg.lowerValidated else if conditional then Stock.ForwardCfg.lowerValidated else if forward then Stock.LinearCfg.lowerValidated else if linear then Stock.TwoBlock.Entry.lowerValidated else if cfgentry then Stock.TwoBlock.lowerValidated else if cfg then Stock.Scalar.lowerValidated else Stock.Logical.lowerValidated) else if parameter then Stock.ParameterCfg.lowerValidated else if conditionalForward then Stock.ConditionalForwardCfg.lowerValidated else if conditional then Stock.ConditionalCfg.lowerValidated else if forward then Stock.ForwardCfg.lowerValidated else if linear then Stock.LinearCfg.lowerValidated else if cfgentry then Stock.TwoBlock.Entry.lowerValidated else if cfg then Stock.TwoBlock.lowerValidated else Stock.Scalar.lowerValidated
  let lowerName := if retainedMixed then (if parameter then "Backend.Stock.ConditionalForwardCfg.lowerValidated" else if conditionalForward then "Backend.Stock.ConditionalCfg.lowerValidated" else if conditional then "Backend.Stock.ForwardCfg.lowerValidated" else if forward then "Backend.Stock.LinearCfg.lowerValidated" else if linear then "Backend.Stock.TwoBlock.Entry.lowerValidated" else if cfgentry then "Backend.Stock.TwoBlock.lowerValidated" else if cfg then "Backend.Stock.Scalar.lowerValidated" else "Backend.Stock.Logical.lowerValidated") else if parameter then "Backend.Stock.ParameterCfg.lowerValidated" else if conditionalForward then "Backend.Stock.ConditionalForwardCfg.lowerValidated" else if conditional then "Backend.Stock.ConditionalCfg.lowerValidated" else if forward then "Backend.Stock.ForwardCfg.lowerValidated" else if linear then "Backend.Stock.LinearCfg.lowerValidated" else if cfgentry then "Backend.Stock.TwoBlock.Entry.lowerValidated" else if cfg then "Backend.Stock.TwoBlock.lowerValidated" else "Backend.Stock.Scalar.lowerValidated"
  let names := (List.range count).map fun i => s!"actual_stock_general_div_{i}"
  let narrowSource := fun (name : String) (i : Nat) =>
    let original := (FVTest.StockNarrowProductionRuntime.functions (configFor i))[i % 79]!.1
    ({original with name}).print
  let maskSource := fun (name : String) (i : Nat) =>
    let original := (FVTest.StockMaskProductionRuntime.functions (configFor i))[i % 36]!.1
    ({original with name}).print
  let fixtureSource := fun name i =>
    if cfg then
      let fixtures := if parameter then FVTest.StockTwoBlockProductionRuntime.parameterFunctions (configFor i) else if conditionalForward then FVTest.StockTwoBlockProductionRuntime.conditionalForwardFunctions (configFor i) else if conditional then FVTest.StockTwoBlockProductionRuntime.conditionalFunctions (configFor i) else if forward then FVTest.StockTwoBlockProductionRuntime.forwardFunctions (configFor i) else if linear then FVTest.StockTwoBlockProductionRuntime.linearFunctions (configFor i)
        else if cfgscalarentry then FVTest.StockTwoBlockProductionRuntime.scalarEntryFunctions (configFor i)
        else if cfgentry then FVTest.StockTwoBlockProductionRuntime.entryFunctions (configFor i)
        else FVTest.StockTwoBlockProductionRuntime.functions (configFor i)
      let index := if mixed && i == 0 then (if cfgscalarentry then 76 else if cfgentry then 12 else 9)
        else i % (if parameter then 100 else if conditionalForward then 100 else if conditional then 100 else if linear then 100 else if cfgscalarentry then 96 else if cfgentry then 16 else 12)
      -- The retained mixed callers declare nine i64 arguments and an i64 result.
      let chosen := if (parameter || conditional || conditionalForward) && mixed && i == 0 then
          fixtures.find? (fun (f,ty) => ty == .i64 && f.sig.returns.all (fun p => p.ty == .i64))
        else fixtures[index]?
      let original := (chosen.getD fixtures[0]!).1
      ({original with name}).print
    else if mask && !retainedMixed then maskSource name i
    else if narrow && !retainedMixed then narrowSource name i
    else sourceText name (configFor i) layout retainedMixed i
  let clif := String.join (names.zipIdx.map fun (n,i) =>
    if cfg && (!mixed || i == 0) || (narrow || mask) && !retainedMixed then fixtureSource n i
    else if !mixed || i == 0 then
      if count == 33 && i > 0 then (Stock.D0.source n (configFor i) []).print
      else sourceText n (configFor i) layout retainedMixed i
    else if i == 1 then ({E2E.StockArithmeticNIWitness.function .systemVI64 with name := n}).print
    else if i == 2 then (Stock.Prologue.source n .systemVI64 []).print
    else if i == 3 then (Stock.D0.source n .fastI32 []).print
    else if i == 4 then
      FVTest.StockScalarFixture.legacySource n
    else if cfg && i == 6 then
      "function %" ++ n ++ "(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v {\n    sig0 = (i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v\n    fn0 = colocated %" ++ names[0]! ++
      "(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v\nblock0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64, v5: i64, v6: i64, v7: i64, v8: i64):\n    try_call fn0(v0, v1, v2, v3, v4, v5, v6, v7, v8), sig0, block1(ret0), []\nblock1(v9: i64):\n    v10 = iconst.i64 1\n    v11 = iadd v9, v10\n    return v11\n}\n"
    else
      "function %" ++ n ++ "(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v {\n    fn0 = colocated %" ++ names[0]! ++
      "(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v\nblock0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64, v5: i64, v6: i64, v7: i64, v8: i64):\n    v9 = call fn0(v0, v1, v2, v3, v4, v5, v6, v7, v8)\n    v10 = iconst.i64 1\n    v11 = iadd v9, v10\n    return v11\n}\n")
  let mut funcs : List FnInput := names.zipIdx.map fun (_, k) => {clif, ra := "null", k, j := k+1}
  if (parameter || conditional || conditionalForward) && mixed then
    let callee := funcs[0]!.func
    require (decide (callee.sig.params.map (·.ty) = List.replicate 9 Clif.Ty.i64) &&
      decide (callee.sig.returns.map (·.ty) = [Clif.Ty.i64]))
      "conditional mixed callee differs from the retained caller signature"
  if cfg && mixed && count == 7 then
    require (funcs.any fun fi => fi.func.blocks.any (fun b => b.term.isTry))
      "mixed CFG regression lost its retained try-call function"
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
    if cfg && !retainedMixed && (if parameter then Stock.ParameterCfg.eligible e.1 else if conditionalForward then Stock.ConditionalForwardCfg.eligible e.1 else if conditional then Stock.ConditionalCfg.eligible e.1 else if forward then Stock.ForwardCfg.eligible e.1 else if linear then Stock.LinearCfg.eligible e.1 else if cfgentry then Stock.TwoBlock.Entry.eligible e.1 else Stock.TwoBlock.eligible e.1) then
      let raw ← get (Stock.lower e.1)
      require ((if parameter then Stock.ParameterCfg.check e.1 raw.code else if conditionalForward then Stock.ConditionalCfg.rankedCheck e.1 raw.code else if conditional then Stock.ConditionalCfg.check e.1 raw.code else if forward then Stock.ForwardCfg.check e.1 raw.code else if linear then Stock.LinearCfg.check e.1 raw.code else if cfgentry then Stock.TwoBlock.Entry.check e.1 raw.code else Stock.TwoBlock.check e.1 raw.code) && ABIReadCfg.check e.1.sig raw.code &&
        decide (a.vc = raw.code)) "CFG linked consumer fell back from actual Stock"
      if e.1.name == names[0]! then
        let empty := raw.edgeArgs.all (fun row => row.all (·.isEmpty))
        require (if parameter then !empty else if conditionalForward then !empty else if conditional then empty else !empty)
          "CFG linked consumer changed its class-specific successor-copy shape"
    else if cfg && retainedMixed then
      let previous ← get ((if parameter then Stock.ConditionalForwardCfg.lowerValidated else if conditionalForward then Stock.ConditionalCfg.lowerValidated else if conditional then Stock.ForwardCfg.lowerValidated else if forward then Stock.LinearCfg.lowerValidated else if linear then Stock.TwoBlock.Entry.lowerValidated else if cfgentry then Stock.TwoBlock.lowerValidated else Stock.Scalar.lowerValidated) e.1)
      require (decide (a.vc = previous)) "retained CFG legacy artifact changed"
    else if narrow && !retainedMixed then
      let raw ← get (Stock.lower e.1)
      require (Stock.Scalar.sourceOk e.1 && Stock.Scalar.check e.1 raw.code &&
        decide (a.vc = raw.code)) "narrow linked consumer fell back from actual Stock"
    else if !cfg && count == 33 && e.1.name != names[0]! then
      let previous ← get (Stock.Arithmetic.lowerValidated e.1)
      require (decide (a.vc = previous) && Backend.Proof.Driver.lowerCheck e.1 a.vc)
        "small multi-entry fixture changed its existing validated route"
    else if retainedMixed || mixed && e.1.name != names[0]! then
      -- CFG activation extends the previous complete Scalar route. Older
      -- fixture classes retain their historical Mixed baseline.
      let previous ← get ((if parameter then Stock.ConditionalForwardCfg.lowerValidated else if conditionalForward then Stock.ConditionalCfg.lowerValidated else if conditional then Stock.ForwardCfg.lowerValidated else if forward then Stock.LinearCfg.lowerValidated else if linear then Stock.TwoBlock.Entry.lowerValidated else if cfgentry then Stock.TwoBlock.lowerValidated else if cfg then Stock.Scalar.lowerValidated else Stock.Mixed.lowerValidated) e.1)
      require (decide (a.vc = previous))
        s!"retained class {e.1.name} changed its actual code or history"
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
    let label := s!"Stock{if parameter then "CfgParameterProduction" else if conditionalForward then "CfgConditionalForwardProduction" else if conditional then "CfgConditionalProduction" else if forward then "CfgForwardProduction" else if linear then "CfgLinearProduction" else if cfgscalarentry then "CfgScalarEntryProduction" else if cfgentry then "CfgEntryProduction" else if cfg then "CfgProduction" else if mask then "MaskProduction" else if narrow then "NarrowProduction" else "GeneralDivProduction" ++ StockGeneralDivNIWitness.layoutName layout}{count}{if retainedMixed then "Retained" else ""}{if mixed then "Mixed" else ""}{if cleanup then "Cleanup" else "Plain"}{if fallback then "Fallback" else "Strict"}{if perEntry then "Entries" else "Global"}"
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
    for (path, text) in FVTest.E2E.SemanticLinkProofWith.leanFilesSemanticWith lowerName input names names
        proof.toString label executable.toString cleanup true
        (if perEntry then none else stack) (if perEntry then names else []) bg (lowerImport := if parameter then "FV.Backend.Lowering.StockParameterCfgNI" else if conditionalForward then "FV.Backend.Lowering.StockConditionalForwardCfgNI" else if conditional then "FV.Backend.Lowering.StockConditionalCfgNI" else if forward then "FV.Backend.Lowering.StockForwardCfgNI" else if cfgentry then "FV.Backend.Lowering.StockLinearCfgNI" else if cfg then "FV.Backend.Lowering.StockTwoBlockNI" else "FV.Backend.Lowering.StockScalarNI") do
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path text
    IO.println s!"ACTUAL_STOCK_LINK {label}: program/checker/ELF/history/stack/proof emission passed"

def check (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for layout in StockGeneralDivNIWitness.layouts do
    for cleanup in [false,true] do
      for fallback in [false,true] do checkCase out 6 cleanup fallback layout
      checkCase out 2 cleanup true layout
    checkCase out 33 true true layout
    checkCase out 6 false true layout true
    checkCase out 6 true true layout true
  checkCase out 2 false true .unused false true
  checkCase out 2 true true .unused false true
def checkNarrow (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 79 cleanup fallback .unused false false true
    checkCase out 2 cleanup true .unused false false true
    checkCase out 2 cleanup true .unused false true true

def checkMask (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 36 cleanup fallback .unused false false false true
    checkCase out 2 cleanup true .unused false false false true
    checkCase out 2 cleanup true .unused false true false true

def checkCfg (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 6 cleanup fallback .unused false false false false true
    checkCase out 2 cleanup true .unused false false false false true
    checkCase out 2 cleanup true .unused false true false false true
    checkCase out 6 cleanup true .unused true false false false true
    checkCase out 7 cleanup true .unused true false false false true
  checkCase out 33 true true .unused false false false false true

def checkCfgEntry (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 16 cleanup fallback .unused false false false false false true
    checkCase out 2 cleanup true .unused false false false false false true
    checkCase out 2 cleanup true .unused false true false false false true
    checkCase out 6 cleanup true .unused true false false false false true
    checkCase out 7 cleanup true .unused true false false false false true
  checkCase out 33 true true .unused false false false false false true


def checkCfgScalarEntry (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 96 cleanup fallback .unused false false false false false true true
    checkCase out 2 cleanup true .unused false false false false false true true
    checkCase out 2 cleanup true .unused false true false false false true true
    checkCase out 6 cleanup true .unused true false false false false true true
    checkCase out 7 cleanup true .unused true false false false false true true
  checkCase out 33 true true .unused false false false false false true true


def checkCfgLinear (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 100 cleanup fallback .unused false false false false false true true true
    checkCase out 2 cleanup true .unused false false false false false true true true
    checkCase out 2 cleanup true .unused false true false false false true true true
    checkCase out 6 cleanup true .unused true false false false false true true true
    checkCase out 7 cleanup true .unused true false false false false true true true
  checkCase out 33 true true .unused false false false false false true true true
def checkCfgForward (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 100 cleanup fallback .unused false false false false false true true true true
    checkCase out 2 cleanup true .unused false false false false false true true true true
    checkCase out 2 cleanup true .unused false true false false false true true true true
    checkCase out 6 cleanup true .unused true false false false false true true true true
    checkCase out 7 cleanup true .unused true false false false false true true true true
  checkCase out 33 true true .unused false false false false false true true true true
def checkCfgConditional (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 100 cleanup fallback .unused false false false false false false false false false true
    checkCase out 2 cleanup true .unused false false false false false false false false false true
    checkCase out 2 cleanup true .unused false true false false false false false false false true
    checkCase out 6 cleanup true .unused true false false false false false false false false true
    checkCase out 7 cleanup true .unused true false false false false false false false false true
  checkCase out 33 true true .unused false false false false false false false false false true
def checkCfgConditionalForward (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 100 cleanup fallback .unused false false false false false false false false false false true
    checkCase out 2 cleanup true .unused false false false false false false false false false false true
    checkCase out 2 cleanup true .unused false true false false false false false false false false true
    checkCase out 6 cleanup true .unused true false false false false false false false false false true
    checkCase out 7 cleanup true .unused true false false false false false false false false false true
  checkCase out 33 true true .unused false false false false false false false false false false true
def checkCfgParameter (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do
      checkCase out 100 cleanup fallback .unused false false false false false false false false false false false true
    checkCase out 2 cleanup true .unused false false false false false false false false false false false true
    checkCase out 2 cleanup true .unused false true false false false false false false false false false true
    checkCase out 6 cleanup true .unused true false false false false false false false false false false true
    checkCase out 7 cleanup true .unused true false false false false false false false false false false true
  checkCase out 33 true true .unused false false false false false false false false false false false true
end FVTest.StockGeneralDivProductionLinkedFixture

def main (args : List String) : IO Unit :=
  if args.head? == some "--cfgparameter" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfgParameter (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfgparameter-linked-fixture"))
  else if args.head? == some "--cfgconditionalforward" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfgConditionalForward (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfgconditionalforward-linked-fixture"))
  else if args.head? == some "--cfgconditional" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfgConditional (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfgconditional-linked-fixture"))
  else if args.head? == some "--cfgforward" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfgForward (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfgforward-linked-fixture"))
  else if args.head? == some "--cfglinear" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfgLinear (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfglinear-linked-fixture"))
  else if args.head? == some "--cfgscalarentry" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfgScalarEntry (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfgscalarentry-linked-fixture"))
  else if args.head? == some "--cfgentry" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfgEntry (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfgentry-linked-fixture"))
  else if args.head? == some "--cfg" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkCfg (System.FilePath.mk (args[1]?.getD "/tmp/stock-cfg-linked-fixture"))
  else if args.head? == some "--mask" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkMask (System.FilePath.mk (args[1]?.getD "/tmp/stock-mask-linked-fixture"))
  else if args.head? == some "--narrow" then
    FVTest.StockGeneralDivProductionLinkedFixture.checkNarrow (System.FilePath.mk (args[1]?.getD "/tmp/stock-narrow-linked-fixture"))
  else FVTest.StockGeneralDivProductionLinkedFixture.check (args.headD "/tmp/stock-mixed-linked-fixture")
