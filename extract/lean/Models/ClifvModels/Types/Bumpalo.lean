/-
Handwritten executable model of the `bumpalo` 3.20.2 arena type.

Memory is not modeled: arena allocations are returned as values (`alloc_slice_*` return the slice
contents), so an arena carries no observable state. The operations are in
`ClifvModels.Funs.Bumpalo`.
-/
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [bumpalo::Bump]: a bump arena (no observable state in the value model). -/
structure bumpalo.Bump (MIN_ALIGN : Std.Usize) : Type where
  mk ::
