module

public import FV.Link.ActualCompilerImage
public import FV.Link.Ld.Spec
public import FVTest.E2E.ActualLinkProof
public import FV.E2E.ActualPrologueWitness

@[expose] public section

/-! Actual Stock callback → actual byte writer → ordinary emitted Lean proofs.
A fixed integration witness; it does not activate a production class. -/
set_option autoImplicit false
namespace FVTest.StockActualLinkedFixture
open Backend _root_.E2E _root_.E2E.LinkCheck _root_.E2E.BinCheck _root_.E2E.Elf Link
open E2E.ActualPrologueWitness

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

private def checkCase (out : System.FilePath) (count : Nat) (cleanup fallback : Bool) : IO Unit := do
  let names := (List.range count).map fun i => s!"actual_stock_prologue_{i}"
  let clif := String.join (names.map sourceText)
  let mut funcs : List FnInput := names.zipIdx.map fun (_, k) => {clif, ra := "null", k, j := k+1}
  let mut answers : Array Lean.Json := #[Lean.Json.null]
  for fi in funcs do
    let raw ← get (actualLower fi.func)
    let prep ← get (prepare (stage cleanup fi.func raw))
    let answer ← get (oracle prep)
    require (checkAlloc prep (← get (buildRFunc prep (← get (parseRAOut answer))))).isOk
      "fixed oracle rejected actual prepared Stock code"
    answers := answers.push answer
  let ra := (Lean.Json.mkObj [("functions", Lean.Json.arr answers)]).compress
  funcs := funcs.map fun fi => {fi with ra}
  let initial : LinkSpec := {funcs, names, sizes := [], outside := [], symNames := names, R := 0x200160}
  let mut sizes : List Nat := []
  for fi in funcs do
    let a ← get (initial.input0.pipeOfWithLowering actualLower (stage cleanup) fi)
    sizes := sizes ++ [a.fb.words.size]
  let spec := {initial with sizes}
  let pl := plan spec
  let image ← get (Link.Ld.assemble pl)
  require (pl.specOkB spec) "actual fixture failed default ELF plan provenance"
  let file ← get (leanLinkWithLowering spec image.write actualLower (stage cleanup))
  let input := {spec.inputWithLowering actualLower (stage cleanup) with fallback}
  let results := input.resultsWithLowering actualLower (stage cleanup)
  require (okRWith (stage cleanup) input results) "actual callback program checks failed"
  for e in results do
    let a ← get e.2
    let old ← get (lowerFunction e.1)
    require (!(a.vc.rulesFired == old.rulesFired)) "fixture lost distinct actual Stock history"
  let ex : Excerpt := [(0, file)]
  let index := _root_.symIndex file
  let cert := input.addrs.filterMap fun p => (index.get? (symName p.1, p.2)).map (p.1, ·)
  require (hdrB ex && symsB input ex cert &&
    codeBWithCompilerModes input actualLower (stage cleanup) ex input.funcs)
    "actual callback ELF/code-table checks failed"
  let bg : BinGen := ⟨ex, [ex, ex], [], ex, cert, []⟩
  let ci : ActualStackBound.CompilerInput := {toLinkInput := input, lower := actualLower, cleanup}
  let stack := ActualStackBound.stackB ci
  require stack.isSome "fixed no-call program has no stack bound"
  for perEntry in (if count > 32 then [false,true] else [false]) do
    let label := s!"StockActual{count}{if cleanup then "Cleanup" else "Plain"}{if fallback then "Fallback" else "Strict"}{if perEntry then "Entries" else "Global"}"
    let executable := out / (label ++ ".elf")
    IO.FS.writeBinFile executable file
    let proof := out / "Crates" / (label ++ ".lean")
    for (path, text) in FVTest.E2E.ActualLinkProof.leanFilesWithLowering input names names
        proof.toString label executable.toString "FV.E2E.ActualPrologueWitness"
        "E2E.ActualPrologueWitness.actualLower" cleanup true
        (if perEntry then none else stack) (if perEntry then names else []) bg do
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path text
    IO.println s!"ACTUAL_STOCK_LINK {label}: program/checker/ELF/history/stack/proof emission passed"

def check (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for cleanup in [false,true] do
    for fallback in [false,true] do checkCase out 2 cleanup fallback
  checkCase out 33 true true
end FVTest.StockActualLinkedFixture

def main (args : List String) : IO Unit :=
  FVTest.StockActualLinkedFixture.check (args.headD "/tmp/stock-actual-linked-fixture")
