import FVTest.Link.DeadCleanupWitness
import FVTest.E2E.LinkProof
import FV.E2E.DeadCleanupStackBound

/-!
# `lake exe dead-cleanup-generate [DIR]`

Writes the closed cleanup crate fixtures of #137, `DIR/DeadCleanupGenerated.lean` (one function)
and `DIR/DeadCleanupGeneratedSplit{.lean,/}` (33 functions, two slices), default
`crate-proofs/Crates` (called by `scripts/regen-crate-proofs.sh`, #745). Each function is the
CLIF `cleanup_unused` fixture of `E2E.DeadCleanupExecutableWitness` under its own name; the
executable is `Link.DeadCleanup.compileExe` of the program placed at `R = 0x1000000` into that
witness's `placeholder` file. The checks (`okBCleanup`, the binary checks) are run here first;
the proofs are `leanFilesCleanup`'s, with the whole file as every excerpt.
-/
namespace FVTest.DeadCleanupGenerate
open E2E E2E.LinkCheck E2E.Elf E2E.BinCheck Link Backend

def fixture (n : String) : FnInput :=
  { clif := s!"function %{n}() \{\nblock0:\n v0 = iconst.i64 17\n return\n}\n", ra := "{}" }

private def get {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- Compile `names` (each a copy of the fixture), check the program and the executable, and
write the fixture module `module` into `outDir`. -/
def gen (names : List String) (module label : String) (outDir : System.FilePath) : IO Unit := do
  let funcs := names.map fixture
  let spec : LinkSpec :=
    { funcs, names := funcs.map (·.func.name),
      sizes := ← funcs.mapM fun f => do
        pure (← get (pipeCleanupT f.func f.k 0 (raJ f.ra f.j))).fb.words.size,
      outside := [], symNames := [], R := 0x1000000 }
  let file0 := E2E.DeadCleanupExecutableWitness.placeholder spec.R spec.size
    (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))
  let file ← get (DeadCleanup.compileExe spec file0)
  let I := spec.inputCleanup
  unless okBCleanup I do throw (IO.userError s!"{module}: okBCleanup fails")
  let idx := _root_.symIndex file
  let cert : List (String × Nat × Nat) := I.addrs.filterMap fun p =>
    (idx.get? (symName p.1, p.2)).map (p.1, ·)
  let ex : Excerpt := [(0, file)]
  unless hdrB ex && symsB I ex cert && E2E.DeadCleanupBinCheck.codeB I ex I.funcs do
    throw (IO.userError s!"{module}: binary checks fail")
  let fns := I.funcs.map (·.func.name)
  let nSl := max ((fns.length + sliceSize - 1) / sliceSize) 1
  let bg : BinGen := ⟨ex, List.replicate nSl ex, ex, ex, cert, []⟩
  let stack := DeadCleanupStackBound.stackB I
  let out := outDir / s!"{module}.lean"
  let dir := outDir / module
  if ← dir.isDir then
    for e in ← dir.readDir do
      if e.fileName == "Input.lean" || (e.fileName.startsWith "Slice" && e.fileName.endsWith ".lean") then
        IO.FS.removeFile e.path
  for (p, t) in leanFilesCleanup I fns fns out.toString module label true stack fns bg do
    if let some pd := (p : System.FilePath).parent then IO.FS.createDirAll pd
    IO.FS.writeFile p t
    IO.println s!"  wrote {p}"
  IO.println s!"{module}: {fns.length} functions, {spec.size} bytes, stack {stack}"

end FVTest.DeadCleanupGenerate

open FVTest.DeadCleanupGenerate in
def main (args : List String) : IO Unit := do
  let outDir : System.FilePath := args.headD "crate-proofs/Crates"
  gen ["cleanup_unused"] "DeadCleanupGenerated" "closed cleanup linker witness" outDir
  gen (["codeB", "okB", "crate_correct"] ++ (List.range 30).map (s!"cleanup_split_{·}"))
    "DeadCleanupGeneratedSplit" "closed cleanup split witness" outDir
