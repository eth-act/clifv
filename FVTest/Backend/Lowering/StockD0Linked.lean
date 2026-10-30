import FV.Link.Compile
import FV.Link.DeadCleanupCompile
import FV.Link.Placed
import FV.Link.Ld.Spec
import FV.E2E.SrcScopeDefs
import FVTest.E2E.LinkProof

/-! A mixed linked program in the actual first production domain: a Stock
one-block identity and a legacy caller. The ordinary Rust identity regression
has a two-block frontend prologue and deliberately remains on legacy for now. -/
namespace FVTest.StockD0Linked
open Backend Backend.Stock.D0 E2E E2E.LinkCheck E2E.Elf E2E.BinCheck Link

private def identitySource : String :=
  "function %stock_identity(i64) -> i64 system_v {\nblock0(v0: i64):\n    return v0\n}\n"

private def callerSource : String :=
  "function %legacy_caller(i64) -> i64 system_v {\n    fn0 = colocated %stock_identity(i64) -> i64 system_v\nblock0(v0: i64):\n    v1 = call fn0(v0)\n    v2 = iconst.i64 1\n    v3 = iadd v1, v2\n    return v3\n}\n"

private def initialSpec : LinkSpec := {
  funcs := [0, 1].map fun k => {clif := identitySource ++ callerSource, ra := "null", k, j := k}
  names := [], sizes := [], outside := []
  symNames := ["stock_identity", "legacy_caller"]
  R := 0x200160 }

/-- A real plan for the default Lean ELF writer, with its program region left
empty for the executable compiler. Its symbols are the compiler's placement. -/
private def plan (spec : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + spec.size
  { base := 0x200000, entry := (spec.addrs.lookup "legacy_caller").getD spec.R
    segs := [{kind := 1, vaddr := 0x200000, offset := 0, filesz := size, memsz := size}]
    tlsAddr := 0x200000 + size, tlsOff := size, tlsFilesz := 0, tlsMemsz := 0, tlsAlign := 1
    ehOff := 0, ehAddr := 0, ehSize := 0, size, pieces := [], secs := #[]
    syms := spec.addrs.toArray.map fun (name, value) =>
      {name := symName name, value, info := 18, shndx := 0xfff1} }

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Run the default dispatcher, actual executable compiler and default ELF
writer in both cleanup modes, then invoke the CLI's unchanged proof emitter on
those same functions, allocator answers and executable bytes. -/
def check (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (out / "Crates")
  for (fi, i) in initialSpec.funcs.zipIdx do
    let selected ← get (selectWith Stock.lower fi.func)
    require (decide (selected.1 = if i == 0 then Origin.stockD0 else Origin.legacy))
      "mixed linked fixture selected an incorrect lowering origin"
  for cleanup in [false, true] do
    let spec := if cleanup then DeadCleanup.placedPar initialSpec else initialSpec.placedPar
    let pl := plan spec
    let image ← get (Link.Ld.assemble pl)
    require (pl.specOkB spec) "mixed fixture failed default-linker plan/spec provenance"
    let file ← get (if cleanup then DeadCleanup.compileExe spec image.write
      else Link.compileExe spec image.write)
    let input := if cleanup then spec.inputCleanup else spec.input
    require (SrcScopeB input) "mixed fixture left the original source theorem's scope"
    require (if cleanup then okBCleanup input else okB input)
      "mixed fixture failed the actual program checker"
    let ex : Excerpt := [(0, file)]
    let index := _root_.symIndex file
    let cert : List (String × Nat × Nat) := input.addrs.filterMap fun p =>
      (index.get? (symName p.1, p.2)).map (p.1, ·)
    require (hdrB ex && symsB input ex cert &&
      (if cleanup then E2E.DeadCleanupBinCheck.codeB input ex input.funcs
       else E2E.BinCheck.codeB input ex input.funcs))
      "mixed fixture failed generated-proof binary checks"
    let bg : BinGen := ⟨ex, [ex], [], ex, cert, []⟩
    let label := if cleanup then "StockD0MixedCleanup" else "StockD0MixedPlain"
    let executable := out / (label ++ ".elf")
    IO.FS.writeBinFile executable file
    let proof := out / "Crates" / (label ++ ".lean")
    let writer := if cleanup then leanFilesCleanup else leanFiles
    for (path, contents) in writer input spec.names spec.names proof.toString label
        executable.toString true none [] bg do
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path contents
    IO.println s!"MIXED_STOCK_LINK {label}: Stock identity, legacy caller, default ELF plan, compiler/checker/binary agreement and proof emission passed"
end FVTest.StockD0Linked

def main (args : List String) : IO Unit :=
  FVTest.StockD0Linked.check (args.headD "/tmp/stock-d0-linked-fixture")
