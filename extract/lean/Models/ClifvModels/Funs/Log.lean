/-
Handwritten executable models of the `log` 0.4.28 functions used by the extracted code,
transcribed from `log-0.4.28/src/{lib,__private_api}.rs` (features: none, so `kv` is off and
`STATIC_MAX_LEVEL = LevelFilter::Trace`).

The native build installs no logger: `log::logger()` is the `NopLogger` and the dynamic maximum
level `max_level()` keeps its initial value `LevelFilter::Off` (`MAX_LOG_LEVEL_FILTER = 0`). So
every `log!` macro expansion (`lvl <= STATIC_MAX_LEVEL && lvl <= max_level()`) skips the call to
`__private_api::log`, and the `GlobalLogger` methods forward to the no-op logger.

Not modeled: `__private_api::loc` (`Location::caller()` of the macro call site). Its result type
`core::panic::Location` has no model, and the call-site location is not an argument of the
extracted function; it is only evaluated inside the disabled `log!` branches.
-/
module
public import Aeneas
public import ClifvGen.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.Log

/-- `Level as usize` (`#[repr(usize)]`, `Error = 1` .. `Trace = 5`). -/
def levelDiscr : log.Level → Nat
  | .Error => 1 | .Warn => 2 | .Info => 3 | .Debug => 4 | .Trace => 5

/-- `LevelFilter as usize` (`Off = 0` .. `Trace = 5`). -/
def filterDiscr : log.LevelFilter → Nat
  | .Off => 0 | .Error => 1 | .Warn => 2 | .Info => 3 | .Debug => 4 | .Trace => 5

/-- `Level as usize`, as a `usize`. -/
def levelUsize : log.Level → Std.Usize
  | .Error => 1#usize | .Warn => 2#usize | .Info => 3#usize | .Debug => 4#usize
  | .Trace => 5#usize

end ClifvModels.Log

open ClifvModels.Log

/-- [log::max_level]: `MAX_LOG_LEVEL_FILTER`, never set natively: `LevelFilter::Off`. -/
def log.max_level : Result log.LevelFilter := ok .Off

/-- [log::STATIC_MAX_LEVEL]: no `max_level_*`/`release_max_level_*` feature is enabled:
`LevelFilter::Trace`. -/
def log.STATIC_MAX_LEVEL : Result log.LevelFilter := ok .Trace

/-- [log::{core::cmp::PartialOrd<log::Level, log::LevelFilter>}::partial_cmp]:
`Some((*self as usize).cmp(&(*other as usize)))`. -/
def log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp
  : log.Level → log.LevelFilter → Result (Option Ordering) :=
  fun l f => ok (some (compare (levelDiscr l) (filterDiscr f)))

/-- [log::{core::cmp::PartialEq<log::Level, log::LevelFilter>}::eq]:
`*self as usize == *other as usize`. -/
def log.Level.Insts.CoreCmpPartialEqLevelFilter.eq
  : log.Level → log.LevelFilter → Result Bool :=
  fun l f => ok (levelDiscr l == filterDiscr f)

/-- [log::__private_api::{log::__private_api::sealed::KVs<'a, ()>}::into_kvs]: `None`. -/
def Tuple.Insts.Log__private_apiSealedKVs.into_kvs
  : Unit → Result (Option (Slice (Str × Str))) :=
  fun _ => ok none

/-- [log::__private_api::{log::Log<log::__private_api::GlobalLogger>}::enabled]:
`logger().enabled(metadata)`; `logger()` is the `NopLogger`: `false`. -/
def log.__private_api.GlobalLogger.Insts.LogLog.enabled
  : log.__private_api.GlobalLogger → log.Metadata → Result Bool :=
  fun _ _ => ok false

/-- [log::__private_api::{log::Log<log::__private_api::GlobalLogger>}::log]:
`logger().log(record)`; the `NopLogger` does nothing. -/
def log.__private_api.GlobalLogger.Insts.LogLog.log
  : log.__private_api.GlobalLogger → log.Record → Result Unit :=
  fun _ _ => ok ()

/-- [log::__private_api::{log::Log<log::__private_api::GlobalLogger>}::flush]: the `NopLogger`
does nothing. -/
def log.__private_api.GlobalLogger.Insts.LogLog.flush
  : log.__private_api.GlobalLogger → Result Unit :=
  fun _ => ok ()

/-- [log::__private_api::enabled]:
`logger.enabled(&Metadata::builder().level(level).target(target).build())`. -/
def log.__private_api.enabled
  {L : Type _} (LogInst : log.Log L) : L → log.Level → Str → Result Bool :=
  fun logger level target =>
    LogInst.enabled logger ⟨levelUsize level, target⟩

/-- [log::__private_api::log]: `log_impl(logger, args, level, &(target, module_path, loc),
kvs.into_kvs())`: panics if `kvs` is `Some` (the `kv` feature is off), else builds the record
and calls `logger.log(&record)`. -/
def log.__private_api.log
  {K : Type _} {L : Type _} (sealedKVsInst : log.__private_api.sealed.KVs K)
  (LogInst : log.Log L) :
  L → core.fmt.Arguments → log.Level → (Str × Str ×
    core.panic.location.Location) → K → Result Unit :=
  fun logger args level (target, module_path, _) kvs => do
    let kvs ← sealedKVsInst.into_kvs kvs
    if kvs.isSome then fail .panic
    else
      LogInst.log logger
        { metadata := ⟨levelUsize level, target⟩, args,
          module_path := some module_path }
