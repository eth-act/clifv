import Lake
open Lake DSL System

/-! # Crate-level instances of `backend_correct_program`

The proof files `cargo fv link-proof` / `lake exe link-check --lean` generate (`Crates/*.lean`,
docs/USAGE.md "Proving a crate"). Their `native_decide` proofs evaluate the checker
`E2E.LinkCheck.okB`; Lean's interpreter runs a compiled definition natively when its module's
code is in a loaded shared library, so the library `Crates` loads `fvcheck`: the compiled code of
`FV.E2E.StackBound` (which imports `FV.E2E.LinkCheck`) and of every module it imports, linked into one shared library (a separate
package because the shared library of `FV` itself cannot be built: the C of some `bv_decide`
proof modules is too large for Clang). -/

package crateProofs

require fv from ".."

/-- The compiled code of `FV.E2E.StackBound` (the stack bound, `stackB`) and of the modules it
imports (`FV.E2E.LinkCheck`, …), as one shared library (Lake rebuilds it when any of them
changes). -/
target fvcheck pkg : Dynlib := do
  let some mod ← findModule? `FV.E2E.StackBound
    | error "fvcheck: module FV.E2E.StackBound not found"
  let imps ← (← mod.transImports.fetch).await
  let objs ← (imps.push mod).flatMapM fun m => (m.nativeFacets true).mapM (·.fetch m)
  buildLeanSharedLib "fvcheck" (pkg.sharedLibDir / nameToSharedLib "fvcheck") objs #[]

@[default_target]
lean_lib Crates where
  globs := #[.submodules `Crates]
  dynlibs := #[(BuildKey.packageTarget `crateProofs `fvcheck : PartialBuildKey)]
