# Stock high-multiply production activation

Validated source `16a5f9634a3b2aeb0b1d51c2be3d3a96b7efd526` reconciles main `6be79a1bc3d84f32a4e2343476439308c9655cf3`.
The default shared Scalar compiler, checker, linker and generated-proof consumers
accept signed/unsigned i32/i64 high multiplication mixed with every prior class.
The original #140 goal remains unfinished.

The existing complete `ScalarHighMul.stock_lower_highmul_source_by_instruction`
bridge supplies actual operand extraction, selected emission, retained binding,
final aliases, fresh-register separation and guarded original-source transfer.
The new family/scan/body/entry-return/domain composition reuses that bridge and
all previous handlers. Exact virtual-register SMULH/UMULH ABI framing extends
shared consumers. No Arm/MInst, allocator, cleanup whitelist, original source
condition or old theorem-variant changes. Source proofs cover 8/16/32/64;
production activation remains i32/i64.

A complete witness appends eight live statements to the comparison function.
All prior computation and comparison/cast roots 811/819/958 remain live;
width-appropriate signed/unsigned roots cover 777/778/779/780. Inputs and the
original explicit slot are arbitrary in all six ABIs and both cleanup modes.
Every prior native test grid is retained exactly.

The newly introduced 33-entry fixture uses one complete high-multiply function
and 32 small D0 companions. It tests both proof slices and per-entry/global
linking without compiling 33 copies of the same large function. High-multiply
entries retain strict semantic-route assertions; D0 companions require exact
existing Arithmetic output and its original checker. The unchanged full
comparison cohort also passes. Failed fixture drafts remain preserved.

All 22 primary checks and 25 ownership partitions pass with explicit source provenance:

- 2,816 normal keys / 2,813 modules; 57 checked-in audits / 1,732 roots. All 1,675 previously recorded axiom sets and 32 public headers remain exact. The new main trap proofs have unchanged source/dependency closures and pass the refreshed audit.
- 5,881 owned core constants use only standard axioms; 1,053 fixed-witness constants use the declared 37 exact native facts. Ownership covers 248 core, 31 witness and 24 executable modules.
- 24 actual objects, 2,832 QEMU comparisons and 708 Cranelift references; zero failures/disagreements. All eleven prior grids are exact.
- Current high-multiply and retained comparison CLI/checker/link/generated-proof cohorts each pass 32/32. Original flat-multiply artifacts remain untouched and pass current proof reconstruction.
- Runtime: 4,737/0/0, with the same seven non-runnable cases. Encoder: 1,321 identical/0 different. Both E2E modes: 1,159 accepted/0 rejected; original/prior identities and ordered stages exact. Verified demo: 21 tests/2 binaries; survey: 53 tests/18 binaries.
- One bundled MCP domain review: standard axioms, no warnings; its 893-source-module closure is unchanged.

The final fixture repair and main reconciliation affected only that fixture,
four additive proof modules, documentation and resource controls. Current normal
keys/trust, the affected executable audit and the repaired cohort were rerun.
Earlier unaffected records keep their actual source head `8eebd1ef`; the JSON
includes a checked source-delta/import-closure/binary-hash applicability
certificate. Every unrelated captured executable is byte-identical. No old
record was relabelled as a run on the new head. Unknown dependencies require
fresh checks.

The linked-fixture logs retain the same pre-existing `StockBlockScan` module
initializer diagnostic as the landed comparison baseline; symbolization and
baseline comparison are preserved. It is separate from test outcomes.

Terminal evidence: `8abeffdf8f3985318f65394ddadb42fd1b506bb1` on `agent/stock-highmul-evidence-20261022T060219Z`.
Archive SHA256 `d5f090c5e3f341c2c2ef8f80211e310c510dafcb4dff98538a84b6704b737114`; 24,694,274 bytes / 1488 files.

Successful `Stock.lower` remains a correctness premise. Universal Stock-only
lowering/downstream completeness is open. Next: division/remainder with real
zero/overflow outcomes; all remaining original widths, ABIs, control, memory,
effects, calls, source/block/whole-driver simulation and completeness. Legacy
fallback is not Stock completeness.
