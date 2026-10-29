module

public import Lean
-- Importers evaluate the builtin simprocs of the simp sets they load.
public meta import Lean.Meta.Tactic.Simp.BuiltinSimprocs

@[expose] public section

open Lean Elab Command in
/-- `attribute [s] p₁ … pₙ` for core builtin simprocs `pᵢ` in a module: core does not mark its
builtin simprocs `meta`, so the simproc attribute's `meta` check rejects them (they are compiled
into Lean). This module re-exports
`public meta import Lean.Meta.Tactic.Simp.BuiltinSimprocs`, which importers need for that. -/
elab "builtin_simproc_attr " s:ident ps:ident+ : command => liftTermElabM do
  let some ext ← Meta.Simp.getSimprocExtension? s.getId | throwError "no simp set `{s.getId}`"
  for p in ps do
    Meta.Simp.addSimprocAttrCore ext (← realizeGlobalConstNoOverload p) .global true
