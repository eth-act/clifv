import FV.Compile
import FVTest.Compile.Cases

/-!
# `emit`: write the corpus as `.clif` filetests

```
lake exe emit <outdir>
```
For every case of `FVTest.Compile.cases` writes `<outdir>/<mangled name>.clif`: the compiled
program (`Compile.compile`), `; run:` lines whose expectations are `denote`'s results encoded
per the ABI (directly on the function, or on its generated test wrappers,
`Compile.Harness`), and, if the program calls the map runtime, the CLIF runtime
(`Compile.Runtime`). Programs that call the runtime are also written without it to
`<outdir>/extrt/<mangled name>.clif` (for linking the Rust `flat-runtime` natively), and the
runtime alone to `<outdir>/runtime.clif`. Fails if an emitted program leaves subset E.
-/

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: emit <outdir>"; pure 2
  IO.FS.createDirAll out
  IO.FS.createDirAll s!"{out}/extrt"
  let rt ← IO.ofExcept Compile.Runtime.functions
  IO.FS.writeFile s!"{out}/runtime.clif" (Clif.print { header := Compile.Harness.header, funcs := rt })
  let mut files := 0
  let mut runs := 0
  let mut extrt := 0
  for tc in FVTest.Compile.cases do
    let p ← IO.ofExcept (Compile.Harness.testProgram tc)
    let body := p.funcs.filter fun f => !Compile.Runtime.names.contains f.name
    unless Compile.onlySubsetE { funcs := body } do
      IO.eprintln s!"{tc.fn.name}: emitted code outside subset E"
      return 1
    let name := Compile.mangle tc.fn.name
    IO.FS.writeFile s!"{out}/{name}.clif" (Clif.print p)
    files := files + 1
    runs := runs + (p.funcs.map (·.runs.length)).sum
    if Compile.Harness.usesRuntime p.funcs then
      let q ← IO.ofExcept (Compile.Harness.testProgram tc (withRuntime := false))
      IO.FS.writeFile s!"{out}/extrt/{name}.clif" (Clif.print q)
      extrt := extrt + 1
  IO.println s!"emit: {files} files ({extrt} also without the CLIF runtime in extrt/), {runs} run lines -> {out}"
  pure 0
