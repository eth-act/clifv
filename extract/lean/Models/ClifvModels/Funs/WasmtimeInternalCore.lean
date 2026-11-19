/-
Handwritten executable models of the `wasmtime-internal-core` (pinned Wasmtime tree,
`crates/core/src/error/oom.rs`) functions used by the extracted code.

Both are formatting impls that only write text to the formatter (no other trait calls). As in the
Aeneas `core::fmt` model, a `Formatter` carries no output, so writing succeeds and leaves it
unchanged.
-/
module
public import Aeneas
public import ClifvGen.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-- [wasmtime_internal_core::error::oom::{core::fmt::Display<wasmtime_internal_core::error::oom::OutOfMemory>}::fmt]:
`write!(f, "out of memory (failed to allocate {} bytes)", ..)`. -/
def wasmtime_internal_core.error.oom.OutOfMemory.Insts.CoreFmtDisplay.fmt
  :
  wasmtime_internal_core.error.oom.OutOfMemory → core.fmt.Formatter →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ f => ok (.Ok (), f)

/-- [wasmtime_internal_core::error::oom::{core::fmt::Debug<wasmtime_internal_core::error::oom::OutOfMemory>}::fmt]:
`f.debug_struct("OutOfMemory").field("requested_allocation_size", ..).finish()`. -/
def wasmtime_internal_core.error.oom.OutOfMemory.Insts.CoreFmtDebug.fmt
  :
  wasmtime_internal_core.error.oom.OutOfMemory → core.fmt.Formatter →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ f => ok (.Ok (), f)
