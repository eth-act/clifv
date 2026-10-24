# Returned division at arbitrary scalar body positions

The default Stock compiler, checker, linker and generated-proof consumers now
accept previously proved scalar computations before and after a returned
signed or unsigned i32/i64 division or remainder. The division need not be the
last statement. Original arbitrary arguments, stack arguments, memory and slots,
zero and overflow traps, accepted identities and old theorem variants remain.

The actual return request supplies positive demand. The real driver preserves
that demand and the definition's unsunk state through all intervening scans,
then derives emitted result binding. Shared scalar/division record handlers
compose guarded original-source fall and trap behavior into the existing
universal Scalar.Domain. The fixed source checker derives the domain internally.
No successful Stock run is presented as a completeness theorem.

Validated implementation: `b1990ec02ff083882720dcc436d638c0db5f2b04`, based on main
`f52b714ae48e0c5df9f996dd3dbeaa8bdbc61370`. Each gate keeps its actual source head. Release-only documentation
changes do not relabel the evidence.

Author evidence:

- 107 affected normal targets and
  1772 imports; 16 checked-in audits
  covering 497 roots. All
  483 prior required axiom sets and
  14 old public headers are exact.
- 31 ownership gates cover
  6408 standard-only core constants,
  1186 fixed-witness constants and exactly
  42 declared native facts. One bundled domain review
  reports standard axioms and no warnings.
- Complete 96 pipeline configurations and 96 source observations; both real
  allocators, both cleanup modes, six ABI/width configurations (default, System V
  and fast at i32/i64), original stack/unused arguments,
  actual safe-divisor roots and fallback/missing-oracle controls.
- 24 Lean-encoded objects, 8,304 Lean-byte executions and 2,076 Cranelift
  reference executions, zero failures or disagreements. All 14 prior native
  case grids remain exact; the runtime retains all 29 earlier functions and
  adds eight arbitrary-position division functions.
- Current and retained consumer cohorts, fresh generated proofs, original
  flat-multiply artifacts, runtime, encoder, both E2E identity/stage reports
  and both verified default-linked examples pass. Both E2E reports retain all
  original 1,150 and prior 1,159 identities and ordered successful stages.

Complete evidence: `07b9f9384e4209467922f6fe80afae2edc0e45e0` on `agent/stock-returned-div-evidence-20261023T051009Z`.
Archive SHA256 `525b6e05ad4bac5a3cddd29466d339eb76c89bcb61e74168caf613ebd10e9aca`;
60296777 bytes across 28994 files. Failed attempts and historical
records retain their original provenance. The cold current-main compiler proof
build is recorded, not confused with newly written Stock proof work.

One generated ownership audit initially lacked an explicit Lean command import.
The external audit template was repaired and its inputs declared explicitly;
ownership gates were rerun. Passed normal builds, native execution and checked-in
axiom audits were retained. The failed attempt is preserved; compiler source did
not change for that repair.

Full original #140 remains unfinished. Continue with unused or otherwise
consumed division results and genuine sink exclusion, other colored effects,
all original widths/ABIs/control/memory/calls/exceptions, source/block/whole-driver
simulation and Stock-only/downstream completeness. Legacy fallback does not
establish Stock completeness.

Current-main reconciliation: fetched `e6dc1acb147d8a5877c84e8360e44b839c6e7909` has 212 changed files since the validated base, touching none of the actual proof, CLI or declared gate inputs. The Rust tree is exact. Source-bound author records remain on b199; unrelated main proof additions are covered by their own main-gate records.

The branch was then rebased onto that main tip. All 16 implementation files and 1,793 packet/import/audit/configuration input blobs remain byte-exact; normal keys for all affected targets and ten executable targets replay successfully. [Reconciliation receipt](stock-returned-div-main-reconciliation.json) records the actual heads and log hash. Further release changes are documentation only.
