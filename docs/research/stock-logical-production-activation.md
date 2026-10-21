# Stock logical production activation

Enable complete single-block i32/i64 add/sub/select/AND/OR/XOR functions through
the default compiler, checker, Lean linker and emitted proofs. The source-only
selector covers normal ABI parameters and returns. Prior D0, prologue, scalar,
arithmetic and add/sub/select paths retain their implementations and fallback.

Validated implementation: `0d9f54fe5fa7bf19c69aceac564d65cc74dcdbc8`, on main
`40333cb4c8544fa06d9d6a69e56a49a3632e1410`.
[Terminal gate and provenance receipt](stock-logical-production-activation.json).
The saved logical/EXTR proofs were reconciled; mainline Arm, allocator and linker
models are reused. The executable/proof import separation remains intact.

The complete linker retry list is now Logical → Mixed → Arithmetic → legacy.
`compileWithRoutes` records the successful index and retains every complete
older attempt on the original specification/image/settings. Standard-only spec,
tail-acceptance and legacy-acceptance theorems justify this routing; old compiler
entry points and theorem variants remain. Actual fixed compiler witnesses cover
current, shifted current, retained Mixed, retained Arithmetic and legacy outcomes
across all six ABI configurations and both cleanup modes.

Normal validation covers 2,645 source files, 2,657 library jobs and 3,422 current
library/tool keys, plus crate proofs. All 44 checked-in audits pass. Ownership
scans cover 2,338 standard-only core constants and 566 fixed-witness constants,
with exactly 17 declared native facts (eight prior, nine logical/EXTR); executable
owners also pass separately. The fixed sparse-ID classifier retains Std3 through
structural dominance reflection. All 1,259 prior axiom sets and 30 old theorem
headers are unchanged. One bundled MCP review passes Std3 without warnings.

Strict runtime tests exercise real matched regalloc2 answers, a missing-oracle
negative control, all seven new/retained classes and whole-attempt retry. Native
execution checks 24 actual Lean objects and 792 fresh byte executions against
198 Cranelift reference executions: zero failures or disagreements. The reference
binary hash remains unchanged after the example/tool builds.

Logical and retained-Mixed linked/generated/actual CLI integration each pass
32 subchecks: 12 generated roots, 18 generated sources and four CLI proofs,
including both cleanup modes and 33-function slices. Old D0, prologue/all-ABI,
scalar and arithmetic runtime/oracle/link/generated/default CLI checks pass.
Current default linker checks pass in both modes; earlier linked artifact hashes
remain identical after correcting a diagnostic theorem citation.

Corpus runtime: 4,737 pass, zero failures/disagreements, seven unchanged known
non-runnable cases. Encoding: 1,321 identical functions, zero differences.
Both E2E modes accept 1,159 cases, preserving every original 1,150 and prior
1,159 identity and ordered successful stage. Verified default Lean-linked
fv-demo matches LLVM on 21 tests and both binaries; survey matches on 53 tests
and all 18 binaries.

The receipt verifies 37 primary command gates and six ownership audits, alongside
normal witness, strict runtime/native and MCP evidence. First-stage logs retain
their actual 4f2694da provenance: the only subsequent source change corrects the
linker's printed acceptance-theorem citation. Current keys and actual CLI modes
were rechecked; FV/proof/generator/lowering sources and artifact bytes did not
change. Saved elaboration/resource/audit failures remain preserved. The initial
example harness lacked cargo-fv on PATH; corrected example runs pass. Failed
checks are never counted as passes.

Terminal evidence is remotely verified at recovery snapshot `29f6be2f`, archive
SHA256 `434cef650bc7d1356c3380c52440fecf51d371aba6a839a9417d9bb83343be92`.
It incrementally extends the preserved canonical 1,874-path snapshot and includes
saved logical dirty-source recovery evidence. This is a further complete
production class. All remaining original #140 effects, omitted/sunk execution,
source/block/whole-driver simulation, Stock-only completeness and final consumer
obligations stay open; see the obligation ledger and execution plan.
