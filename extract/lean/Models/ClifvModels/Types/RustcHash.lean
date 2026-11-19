/-
Handwritten executable model of the `rustc-hash` 2.1.1 type `FxHasher` (x86_64: `usize` = 64 bits).
-/
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [rustc_hash::FxHasher]: `pub struct FxHasher { hash: usize }`. -/
structure rustc_hash.FxHasher where
  hash : Std.Usize
