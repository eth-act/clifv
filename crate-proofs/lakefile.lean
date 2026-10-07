import Lake
open Lake DSL System

/-! # Crate-level instances of `backend_correct_program`

The proof files `cargo fv link-proof` / `lake exe link-check --lean` generate (`Crates/*.lean`,
docs/USAGE.md "Proving a crate"). Their `native_decide` proofs evaluate the checker
`E2E.LinkCheck.okB`, the stack bound of `E2E.StackBound`, the binary checks of `E2E.BinCheck`,
the code map check `E2E.LinkCheck.codeMapB` and the input conditions and linker facts of
`E2E.LinkCheck.InScopeP`/`linkerOkB` (L2a); Lean's interpreter runs a compiled definition
natively when its module's code is in a loaded shared library, so the library `Crates` loads
`fvcheck`: the compiled code of the
checker modules (`checkRoots`) and of every module they import, linked into one shared library
(a separate package because the shared library of `FV` itself cannot be built: the C of some
`bv_decide` proof modules is too large for Clang). -/

package crateProofs

require fv from ".."

/-- The checker modules whose compiled code `fvcheck` holds (`FV.E2E.StackBound`,
`FV.E2E.CodeMap` and `FV.E2E.LinkScopeDefs` import `FV.E2E.LinkCheck`; `FV.Link.Image`: the Lean
linker, `Link.leanLink`). -/
def checkRoots : Array Lean.Name :=
  #[`FV.E2E.StackBound, `FV.E2E.BinCheck, `FV.E2E.CodeMap, `FV.E2E.LinkScopeDefs, `FV.Link.Image]

/-- The compiled code of the checker modules and of the modules they import, as one shared
library (Lake rebuilds it when any of them changes). -/
target fvcheck pkg : Dynlib := do
  let mut mods : Array Module := #[]
  for r in checkRoots do
    let some mod ← findModule? r
      | error s!"fvcheck: module {r} not found"
    for m in (← (← mod.transImports.fetch).await).push mod do
      unless mods.any (·.name == m.name) do mods := mods.push m
  let objs ← mods.flatMapM fun m => (m.nativeFacets true).mapM (·.fetch m)
  buildLeanSharedLib "fvcheck" (pkg.sharedLibDir / nameToSharedLib "fvcheck") objs #[]

@[default_target]
lean_lib Crates where
  globs := #[.submodules `Crates]
  dynlibs := #[(BuildKey.packageTarget `crateProofs `fvcheck : PartialBuildKey)]
