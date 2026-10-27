# Arbitrary scalar/division production activation

Production packet [#611](https://github.com/eth-act/clifv/pull/611) admits unused,
consumed and multiple i32/i64 divisions/remainders at arbitrary scalar body
positions through the existing default compiler, checker, linker and generated
proof consumers. It preserves previous class selectors, legacy fallback, theorem
variants, original operands/arguments/slots and real zero/overflow traps. The
source-derived return-and-trap domain composes the retained-record/result-binding
and guarded original-source transfers from #604; no new input certificate or
source normalization is required.

Validated code is `cd57ac630b3846a7b7832140b7e5f195452857fc`, based on
`1510186e56b81e8cbb36027746414a411c8e1f37`. All observations below are current
V6 records for that code. Earlier records retain their original heads and results.

## Current validation

| Gate | Observed result |
| --- | --- |
| Full FV/FVTest and affected-tool normal keys | 3,947/3,947; 707 rebuilt; unchanged source; 277.3 minutes |
| Owned-root normal replay | 2,424/2,424; no rebuild |
| Trust and ownership | 19 audit files/577 public roots; all 33 ownership partitions passed their declared policies |
| Previous axiom sets | All 497 production and 13 sink roots exact |
| Previous interfaces/cases | 17 scalar headers, 10 shape headers and 30 native profile/width grids exact |
| Complete fixed pipeline witnesses | 288 configurations, including source outcomes, both cleanup modes and the actual preparation/allocation/emission chain |
| Fresh executable builds | All eleven affected native executables built |
| Native execution | 24 actual Lean-encoded objects; 14,640 Lean-byte executions against 3,660 Cranelift reference executions; zero failures/disagreements |
| Current consumer integration | All 76 command records passed: 50 generated modules, eight CLI proofs, eight link checks, six verified links, runtime/linked fixtures and generated axiom audit |
| Retained consumer integration | All 32 command records passed: 18 generated modules, four CLI proofs, four link checks, two verified links and retained fixtures/audit |
| Encoder | 1,398 compiled functions identical; zero differing; 62,079 words and 1,342 relocations compared |
| Both E2E cleanup modes | 1,159 accepted identities; every original 1,150 and prior 1,159 identity and its ordered successful stages preserved |
| Actual crate proofs | Native checker exports and crate modules passed; actual package-default build completed 1,659 jobs |
| Fault co-simulation | 152 forms, 15,200 vectors, 10,318 faults, zero failures |
| Verified fv-demo | Both executables verified; 21 test outcomes match LLVM |
| Verified survey | All 18 executables verified; 53 test outcomes match LLVM |
| Artifact retention/readiness | Original flat-multiply artifacts/proofs retained; all 17 final readiness checks passed |

The runtime corpus gate records 5,755 Lean passes, no failed Lean runs and no
native disagreements, alongside its existing unsupported/not-runnable cases.
Its raw report remains authoritative; a passing gate does not mean all corpus
functions are supported. Strict missing-binary/oracle negative controls passed.
The semantic source reviewed earlier remains hash-identical; its source-matched
review and axiom requirements are preserved.

## Proof-build repair and provenance

The generated select-rule 2267 integer family is checked in eight kernel chunks
to address an observed memory failure. Generator and generated source agree.
All 21 public facts use exactly `propext` and `Quot.sound`; the ten old headers
remain exact. The repaired module passed at 4 GiB in 88 seconds. This changes
proof compilation granularity, not runtime lowering or semantic assumptions.

The scheduler now saves failed-attempt source hashes and original log/memory/time
files before retry. All twelve V6 failure archives were independently hash-checked;
the final unchanged-source normal run passed. Earlier invalidated/failed runs
remain failed; unrecovered older raw-file gaps are explicit in their evidence.

Complete pre-publication author evidence is remotely backed at
`69182545e98f69505bd1fee79c99bb3f579a5818`, branch
`agent/stock-general-div-progress-20261024T193729Z`: 20,715 files,
45,850,894-byte archive, SHA256
`5761c1a6d90b144adb48d6902592bc01be31012d678390f2e9016361360bf96d`.
The archive contains original manifests, input keys, logs, receipts, failures,
readiness and real-crate object/binary/tool hashes. It does not relabel historical
receipts. Publication changes only documentation; the separate publication
equivalence/replay receipt retains the validated code head above.

## Register agreement and remaining scope

Fresh paired objects from the verified examples yield exact byte/relocation
agreement for 303/1,364 fv-demo and 584/3,179 survey symbol comparisons, across
30 codegen-unit pairs. These are symbol comparisons, not unique source-function
counts or Stock-only coverage. Difference attribution is heuristic. The default
allocator remains Lean; this packet does not activate the separate allocator/
Cranelift-input-numbering work.

Full original #140 remains open: original widths/ABIs and remaining rule families,
control/successor arguments/critical edges/loops, memory/addressing/atomics/traps/
deferred effects, calls/sret/exceptions/unwind, source/scan/block/node/whole-driver
simulation, Stock-only and downstream completeness, optimizer/cleanup and all
consumer integration. Legacy fallback and this scalar production class do not
establish a complete register-aligned driver.
