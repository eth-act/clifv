# Ranked conditional Stock production activation

PR [#636](https://github.com/eth-act/clifv/pull/636), validated implementation `7170a146609c5d1094e8c0bb4d67f738c8f5abd2`, based on #635 (`91c809f7`).

Wide entry-parameter conditionals now continue through arbitrary ranked scalar jump/return tails. Original source choice, inherited values, nonempty jump argument copies, joins, returns and first/later traps compose through actual retained Stock records, direct/synthetic routes and instruction-zero ABI entry into the unchanged Scalar.Domain. Default compiler/checker/verified-linker/generated-proof consumers append route 10, retaining routes 0–9 and the complete prior conditional pipeline on failure with the same original inputs and settings. No allocator, shared LowerSim or CLIF semantic change.

| Author gate | Result |
| --- | --- |
| FV/FVTest / tools | 4,172 keys / 4,976 jobs |
| Trust / ownership | 96 audits; 3,716 roots; all 3,698 old sets, five headers exact; six partitions |
| Focused roots | 20 standard-only; one fixed checked-driver witness with one inventoried permitted original-input native fact |
| Current / retained conditional / forward / linear | 78 / 78 / 78 / 78 commands |
| Retained scalar-entry / entry / CFG | 70 / 34 / 34 commands |
| Current generated proofs | 64 fresh modules / all 18 root packages, CLI checker, verified linking and generated axioms |
| Actual native bytes | 24,000 executions / 3,000 references; zero failures or disagreements |
| Runtime / encoder | 5,755/0/0 with seven unchanged non-runnable cases / 1,398 identical, zero different |
| Both E2E modes | 1,159 accepted, zero rejected; original 1,150 and parent 1,159 identities and ordered stages exact |
| Verified examples / actual crate-proofs | 21 + 53 tests, all 20 ELFs / 93 modules, 96 commands |
| Actual paired outputs | 4,543 functions; 900→900 exact; zero gains, losses or changed function bytes |

All 2,552 unchanged prior backend proof files remain exact. The paired measurement binds freshly rebuilt candidate/reference objects and the actual source/settings to the hash-verified #635 parent capture, including complete same-compiler reference relocation targets. Candidate output comes directly from the verified example runs, avoiding a duplicate compilation of all 4,543 functions. The historical cross-compiler metric compares bytes and relocation offsets/types/addends. No agreement improvement is claimed.

[Machine receipt](stock-conditional-forward-cfg-production.json) records source and gate hashes. Remote terminal evidence `cd2a1b74f38bff0987c753b571b9ceefe25478a2` preserves 6,446 verified files in two bounded parts (44,065,417 compressed bytes); archive SHA256 `cf2b1424c4a9b9a87de3a678a6387bac84dcfe8351f1607a2f0cf4903ae045ba`. Expendable compiled module outputs are recorded by hash. Historical failed proper-module builds and preflight witnesses remain preserved; failed runs are never counted passed. CI is a post-merge signal, not claimed passed here.

Resources stayed within the 16 GiB/two-heavy-job budget, apart from a short optional scratch compile that crossed the retained-cohort transition and exited without success; this was recorded and further scratch builds deferred. Independent lanes use two CPUs each, four total, nice 10, OMP_NUM_THREADS=2 and OMP_THREAD_LIMIT=2. One warm project cache and four preserved source views remain. A prototype source-hash wrapper failed before starting a proof, was corrected, and its original record is retained separately. These operational failures do not replace any author gate.

Full #140 remains open. Next-control drafts now derive general ranked parameter-conditional return/first-trap continuations and source/domain/ABI witnesses separately; they do not alter this frozen packet. Continue broader computed/narrow conditions, per-edge transfers, tables/loops, effects/calls, uncovered families and original-domain source/block/whole-driver simulation and completeness. Fallback preserves acceptance and is not Stock completeness.
