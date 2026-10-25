# Two-block source class and consumer compatibility

Based on main `efe8b677`, this batch proves complete instruction-zero return
and trap simulation for a direct two-block class. Entry constants/nops forward
their new results; previously held entry parameters remain available to the
successor. The successor return block supports the existing scalar/division/mask
families, including narrow integers and actual division traps. Coverage of
inherited and newly defined successor values follows from original availability
and source structure, rather than a machine-value certificate.

The ABI prelude is executed on the same canonical entry core used by body/jump
composition. The source theorems take the existing general `SourceEntry`
contract, retaining placed-slot consumers as well as executable `enterFunc`
fixtures. They retain return ABI pins, implicit return semantics, memory
deallocation, source fuel and actual trap codes. Old theorem variants remain.

For this direct single-successor class, actual collection and assembly prove
that every selected per-edge vector equals its legacy branch-argument field.
`EdgeLegacyCompatible` transports the full observation to existing VCode
semantics and `Scalar.Domain`. Nonempty successor copies are supported. This
does not flatten general multi-successor vectors or assume equality between
independently chosen compiler cores.

The new `Stock.TwoBlock.eligible`, `sourceOk` and `check` predicates derive that
domain from ordinary source/scope/dominance/ABI checks and replay the actual
Stock result. Existing selectors, compiler/checker/linker defaults and consumers
are unchanged; this predicate is not activated in production yet.

## Evidence

- Full FV/FVTest: 4031/4031, all current input keys checked.
- New audit: 20/20 roots; all 17 general roots use standard axioms only.
  The combined branch audit is 38/38 roots across three files.
- Real entered-source 7+9=16 return and zero-divisor trap witnesses execute from
  instruction zero. The zero-divisor fixture's compiler execution is kernel
  checked (23 seconds, 7.0 GiB cgroup peak under an 8 GiB cap).
- Fixed witness facts remain labelled: the old inherited fixture's dominance,
  its newly replayed original-input checker verdict, and the new trap fixture's
  original-input dominance. No general theorem uses a finite/native fact and
  no new emitted-code-shape native fact is introduced.
- Two bundled transitive MCP witness reviews report no source warnings.
  Logs and source hashes are retained under `/tmp/stock-cfg-entry-*`, including
  failed drafts and the distinct successful runs. All 3995 baseline FV/FVTest
  Lean files remain unchanged; no runtime/identity/stage gain is claimed.

## Next production gate

The existing ABI-read models admit next/return/halt control, and reject jumps.
The single-successor compatibility bridge alone therefore does not establish
paired physical execution or activate compiler/checker/linker/generated-proof
routes. Add a CFG ABI-read model and prove control-flow transport/realization,
including the actual entry-only argument-read invariant. Preserve the old
models/checks and theorem variants. Do not simply accept `.jump` in a checker
whose model still excludes `.goto`.

Then connect this class through existing validated production consumers,
default selection with legacy fallback, encoded/native and identity/stage
gates, and a substantive production PR. Continue more function classes and
every original #140 control/critical-edge/loop/effect/call/whole-driver/
completeness obligation afterward. This batch does not finish #140 or justify
claiming production CFG activation.
