/-
Handwritten executable models of the `log` 0.4.28 record types.

`log::Level` is an extracted type (not visible here), so the level is kept as its `usize`
discriminant (`Error = 1` .. `Trace = 5`). The source location (`file`, `line`) of a record is not
kept: `core::panic::Location` has no model, and no consumer reads it (the only `Log` used is the
global logger, which natively is the no-op logger: see `ClifvModels.Funs.Log`).
-/
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [log::Metadata]: `{ level: Level, target: &str }`. -/
structure log.Metadata : Type where
  level : Std.Usize
  target : Str

/-- [log::Record]: `{ metadata, args, module_path, .. }`. -/
structure log.Record : Type where
  metadata : log.Metadata
  args : core.fmt.Arguments
  module_path : Option Str
