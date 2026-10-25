# Original-block source and machine body composition

Validated source: `c7e249b175e35fad058bba5a9299cff40d246c7f`, based on main `ab1abdfc` (#624).
This packet is a CFG production prerequisite. It does not activate general
branches, loops, effects or calls, and does not complete original #140.

`StockQuietBlockSourceRecords` derives quiet metadata, unsunkness and source
records for arbitrary original blocks. `StockMaskBlockRecords` classifies their
actual records, including colored division and zero-result nop.
`StockMaskBlockRefines` reuses existing record semantics to compose whole-body
returning and trapping behavior. Actual executable source runs supply the source
steps internally.

`StockLocalSourceContinuation.actual_local_source_trap_or_continue` retains
arbitrary terminators and caller stacks. A later block's trap yields a normally
executed current body and a trapping source continuation. It cannot be attributed
to the current body. All old return-only and single-block variants remain.

`StockSourceEdgeDFG` transfers source consistency between actual scan contexts
and through successful original successor binding. Original dominance, SSA and
parameter freedom derive parameter/inherited-value facts. It adds no accepted
input certificate. Source consistency alone does not establish machine branch
execution or the guarded demand/value relation at a successor.

Real witnesses use one actual two-block Stock run: an unused constant and nop,
two successor arguments, then division and bmask. Original ABI worlds inhabit
the machine entry guards. Source executions cover both a later zero-divisor trap
and return with divisor one. The successor witness additionally executes both
entry statements and the actual nonempty successor binding. The fourteen new
general roots use only standard axioms. Seven witnesses cover actual source/compiler/machine contracts. Compiler-backed
witnesses reuse fixed compiler-run and input-dominance facts; general results
depend on neither fact.

Validation:

- Full normal FV/FVTest: 3,984/3,984 keys; eight rebuilt, 3,976 existing keys restored.
- All 79 repository audit files pass: 3,540 reports / 3,389 distinct roots.
- All 626 preserved prior axiom sets match exactly. All 3,967 existing FV/FVTest
  Lean source files are byte-exact against main, preserving their theorem bodies,
  interfaces and import dependencies.
- Quiet/body/source-edge audit packets contain 30 reports, including the fourteen
  general roots, seven witnesses and nine retained roots. Bundled MCP reviews
  report only standard axioms and the two identified finite witness facts,
  with no source-scan warnings.

The CFG additions live in new modules. The original QuietSourceRecords and
LocalSourceTrap modules are restored exactly, so future CFG edits do not
invalidate existing consumer proofs. The earlier cba3a9e0 validation batch was
ended after its healthy GeneralDivChecks finished (1,116 seconds); that partial
batch is not a full validation pass. Final current normal replay takes 0.6 min.
An attempted combined retained-audit fixture encountered existing mutually
exclusive LowerSimT/Concurrency.IselDriverT imports. Its failure is preserved;
the successful individual audits cover all 626 prior roots exactly.

No compiler, scope predicate, checker, allocator, encoding, linker or production
consumer implementation changes. Their runtime input sources and old module
keys remain unchanged; current author gates are normal builds and trust audits.
No new byte-agreement gain is claimed. The last measured 887/4,543 symbol
comparisons remain historical production evidence, not a completion percentage.

Next: machine branch execution and actual successor value/demand/world transfer,
then per-successor preparation/allocation/checker/physical/encoding/compiler/
linker/generated-proof integration, critical edges and loops. Reuse existing
preparation totality/checker completeness. Every original memory/effect/ABI/
call/unwind, whole-driver simulation and Stock-only/downstream completeness
obligation remains in scope. See the plan and obligation ledger.
