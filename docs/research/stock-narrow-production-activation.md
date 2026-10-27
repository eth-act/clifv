# Narrow integer Stock production activation

Validated implementation `a1b29bf7ccf976094511285296c0ba3e2201e60b`, based on #611 (`439ca61b`). All current author gates passed; production compiler/proof sources are frozen at this validated head. The publication adds the audit, CLI verification utility and this receipt.

The shared scalar route previously admitted i32/i64 production bodies and signatures. The additive i8/i16 eligibility reuses the existing type-general source return/trap domain. Original body/ABI selectors, old theorem variants, original input conditions and legacy fallback remain. New virtual extended SUBS and immediate ANDS flag producers have physical-argument frame, world-transport, realization and TLS-exclusion proofs. No compiler/checker/linker/proof-consumer stack is duplicated.

The finite witness grid has 231 positive primitive functions and six mixed functions across three calling-convention modes. Both cleanup modes yield 474 complete pipeline configurations. The three i8 byte-swap cases remain explicit negative checks under the unchanged original scope. Source returns and real zero/overflow traps, arbitrary input bits and source-slot addresses, actual raw Stock selection, preparation, allocation and encoding are witnessed. This establishes soundness and these complete witnesses; unconditional Stock-only completeness remains a full-goal obligation.

Current evidence:

- Full normal build: 3,952/3,952 modules, 67 rebuilt. All 11 affected native executables built.
- Narrow native: 12 actual objects, 8,532 Lean-byte executions against 2,133 independent Cranelift references, zero failures/disagreements. Both allocators, both cleanup modes, three calling conventions and nine source samples include signed/truncation/condition boundaries. Checked real regalloc2 read-back and missing-binary negative control pass.
- Ordinary `lean-backend` CLI: all 12 narrow objects and function/trap tables match the checked API exports byte-for-byte, without experimental Stock flags.
- Narrow consumer cohort: 58 command records, 44 generated-proof modules, four CLI proofs, four link checks and two verified links.
- Retained consumer cohort: 32 records. Broader division cohort: 76 records; 24 old-class objects and 14,640 native executions still agree with Cranelift.
- Original flat-multiply data and ELF bytes remain untouched and pass current checker/proof generation and proof compilation in both cleanup modes.
- Current affected axiom audits and 23-root narrow audit pass. Exact 497 prior production and 13 sink axiom sets, 36 old public headers and 32 old native profile/width grids are preserved. The 21 exact two-standard-axiom shape facts inherit through 154 unchanged local import modules and unchanged toolchain/package configuration.
- Fresh exact-source MCP compilation and compiled-import checks agree with the normal kernel audit. Inconsistent cached `lean_verify` wrapper reports are preserved separately and are not counted as passes.
- Ownership: all 38 module partitions pass, with the single identified new fixed native fact allowed only in its two witness modules.
- Runtime corpus: 5,755 runnable Lean passes, zero runnable failures/disagreements; original 7,971 unsupported and seven not-runnable records remain explicitly reported.
- Encoder: 1,398 identical functions, zero differences, 62,005 words and 1,342 relocations compared.
- Both E2E modes: 1,159 accepted, zero rejected. All original 1,150, prior 1,159 and parent 1,159 identities and ordered successful stages remain exact.
- Actual crate-proof closure/default package build passed. Fault co-simulation: 152 forms, 15,200 vectors, 10,318 faults and zero failures.
- Verified examples: fv-demo 2/2 executables and 21 matching tests; survey 18/18 executables and 53 matching tests.
- Final readiness: 20/20 checks passed. Fresh settings-matched real-crate comparison: 30 CGU object pairs, 887/4,543 exact symbol comparisons (fv-demo 303/1,364; survey 584/3,179), unchanged from the parent. These are symbol comparisons, not unique-function counts or a completion percentage.

Generic compiler and ABI proofs use only the required standard axioms. Exactly one identified native fact, `E2E.StockNarrowNIWitness.checks_true._native.native_decide.ax_1`, belongs to the finite witness grid and its derived fixed witnesses.

Applicability is the existing default no-opt/no-TryCall input eligibility. `cargo-fv` compiles each function in its own file; a `try_call` in one Rust function does not disable Stock for unrelated pure functions. Combined CLI inputs containing `try_call`, optimized routes, and the remaining control/memory/call/unwind consumers still need their full integration proofs. The allocator default remains Lean; allocator/Cranelift-input-numbering work is separate. These class results do not establish general register agreement.

Keep #140 open. Remaining work includes original pure bmask/nop composition and reachable look-through cases, CFG/arguments/critical edges/loops, memory/addressing/atomics/traps/deferred effects, calls/sret/TryCall/unwind, source/block/node/whole-driver simulation, unconditional Stock-only and downstream completeness, optimizer/cleanup and all remaining consumers. Reconcile current main, retain all accepted identities and ordered successful stages, preserve source/evidence, squash-merge substantive packets promptly after gates, and keep resource/cleanup discipline.

Reproduction and evidence: `scripts/audit/stock-narrow-production.lean` lists the 23 new/changed public roots and marks fixed native witnesses explicitly. `scripts/check-stock-api-backend-cli.py ARTIFACTS --output OUT` checks ordinary compiler objects against a passed native API matrix. Existing runtime/link/native/integration fixture targets support the narrow cohort and preserve old default behavior. Terminal author receipts retain source head `a1b29bf7`; the final publication-equivalence record separately verifies unchanged production sources and executable hashes. The full original #140 goal remains incomplete.
