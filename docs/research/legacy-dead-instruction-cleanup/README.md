# Legacy cleanup measurement

The conservative cleanup prototype improves exact code-artifact agreement on
the existing lowering driver: **465 → 674 exact matches (+209), no lost matches
and no newly rejected functions**. It removes the redundant instruction in all
three focused cases. This establishes the measurement checkpoint for #60;
semantic/structural proof integration and production enablement remain separate.

| Full official suite | Baseline | Cleanup prototype |
| --- | ---: | ---: |
| Inventoried files | 1,302 | 1,302 |
| Function occurrences | 4,501 | 4,501 |
| Exact code artifacts | 465 | 674 |
| Differing code artifacts | 1,145 | 936 |
| Unsupported operations | 2,413 | 2,413 |
| Unsupported settings | 432 | 432 |
| Expected stock rejections without binaries | 46 | 46 |

| Focused case | Stock bytes | Baseline bytes | Cleanup bytes |
| --- | ---: | ---: | ---: |
| `isa/aarch64/bitops.clif` `%band_not_i64` | 8 | 12 | 8 |
| `runtests/arithmetic.clif` `%msub_i32` | 8 | 12 | 8 |
| `isa/aarch64/stack.clif` `%stack_load_small` | 28 | 32 | 28 |

Exact means the existing comparator's bytes, relocations, alignment and traps,
plus object/dump consistency, stock repeatability and exact-settings receipts.
Execution and full exception/unwind metadata equivalence are not established by
this measurement. Runtime and proof gates are required before production cutover.

Both runs have one existing reference-repeatability gap: `runtests/throw.clif`
embeds a host function pointer in `%throw`, changing under ASLR. All three
functions in that stage are unsupported by Lean; none contributes a match or a
compared output. The delta checker rejects an unstable reference for any
compiled comparison. No stock assertion failed and no official input changed.

## Evidence and reproduction

- [receipt.json](receipt.json): baseline commit, executable hashes, stock pin,
  full inventory hash, both counts and hashes/locations of complete local results.
- [focused.json](focused.json): exact requested settings and focused comparisons.
- [gains.tsv](gains.tsv): all 209 gained identities, including variant and function
  index; duplicate function names are not conflated.
- [delta.json](delta.json): checkpoint verdict and remaining reference gap.
- [DeadCleanupPrototype.lean](DeadCleanupPrototype.lean) and
  [prototype-main.patch](prototype-main.patch): exact experimental compiler edits.
  These files are evidence; the pass is not installed in the production build.

Use an isolated worktree of baseline main
`8959127bf91f93699b674a3148fab441be874140`, and the pinned stock checkout with the
exact checked-in `scripts/patches/prejit-export.patch`. Preserve any other stock
instrumentation. Build the allocator/exporter and `lean-backend` with repository
memory caps, and save the baseline executable before applying the prototype:

```sh
mkdir -p target/legacy-dead-cleanup
LEAN_NUM_THREADS=2 FV_MEMCAP=22G scripts/memcap.sh lake build lean-backend
cp .lake/build/bin/lean-backend target/legacy-dead-cleanup/lean-backend-baseline
cp docs/research/legacy-dead-instruction-cleanup/DeadCleanupPrototype.lean FVTest/Backend/
git apply --unidiff-zero docs/research/legacy-dead-instruction-cleanup/prototype-main.patch
LEAN_NUM_THREADS=2 FV_MEMCAP=22G scripts/memcap.sh lake build lean-backend
export LEAN_REGALLOC="$PWD/rust/target/release/lean-regalloc"
FV_MEMCAP=22G scripts/memcap.sh python3 scripts/stock-compiler-compare.py \
  --out target/legacy-dead-cleanup/baseline-full --jobs 2 \
  --lean-compiler target/legacy-dead-cleanup/lean-backend-baseline
FV_MEMCAP=22G scripts/memcap.sh python3 scripts/stock-compiler-compare.py \
  --out target/legacy-dead-cleanup/candidate-full --jobs 2 \
  --lean-compiler-arg=--dead-cleanup-prototype
python3 scripts/stock-comparison-delta.py \
  target/legacy-dead-cleanup/baseline-full/results.json \
  target/legacy-dead-cleanup/candidate-full/results.json \
  --out target/legacy-dead-cleanup/delta.json --require-full-suite \
  --require-exact isa/aarch64/bitops.clif:%band_not_i64 \
  --require-exact runtests/arithmetic.clif:%msub_i32 \
  --require-exact isa/aarch64/stack.clif:%stack_load_small
```

The two measurements exit **10** with finished `results.json`: suite gaps remain.
The delta check exits **0** for this successful checkpoint. Compiler arguments
are recorded and do not alter or bypass the exact stock-settings receipt check.

## Strengthened boundary liveness

The proof implementation includes reads from the current block in the live-out
set, as well as all other blocks and edge arguments. This conservatively covers
self-loops without a separate SSA premise. Its `discard` predicate uses actual
operand definitions, and a failed operand view always retains the instruction.

A repeated full measurement of this implementation gives **465 -> 671** exact
artifacts: **206 gains, zero losses and zero new rejections**. All three focused
cases remain exact. It retains three dead-chain outputs improved by the original
prototype. See `global-live-out-receipt.json` for source/executable/report hashes
and `global-live-out-delta.json` for the gate and focused results. The original
209-gain prototype evidence above remains unchanged.

This rerun used an opt-in measurement hook in `FVTest/Backend/Main.lean`, cleaning
only the stock allocator callback's VCode array, exactly as in the original
measurement. The hook and candidate executable were isolated in the measurement
worktree; the hook was removed after preserving the executable. Production
integration and its full proof/validation gates are still pending.

## Production default comparison

`default-enabled-receipt.json` records the fresh compiler at `b6b6c9e`, using its
unflagged cleanup default against its explicit `--no-dead-cleanup` path. Both
runs pin the same allocator executable. `default-enabled-delta.json` verifies
the full 1,302-file inventory, **465 → 671 exact artifacts**, **206 gains**, no
lost identities or new rejections, and all three focused cases. This is artifact
comparison evidence; the full proof and runtime gates are checked separately.

After building `lean-backend`, reproduce the two measurements with:

```sh
export LEAN_REGALLOC="$PWD/rust/target/release/lean-regalloc"
FV_MEMCAP=8G scripts/memcap.sh python3 scripts/stock-compiler-compare.py \
  --out target/legacy-dead-cleanup/final-legacy-comparison --jobs 2 \
  --lean-compiler-arg=--no-dead-cleanup
FV_MEMCAP=8G scripts/memcap.sh python3 scripts/stock-compiler-compare.py \
  --out target/legacy-dead-cleanup/final-default-comparison --jobs 2
python3 scripts/stock-comparison-delta.py \
  target/legacy-dead-cleanup/final-legacy-comparison/results.json \
  target/legacy-dead-cleanup/final-default-comparison/results.json \
  --out target/legacy-dead-cleanup/final-default-delta.json --require-full-suite \
  --require-exact isa/aarch64/bitops.clif:%band_not_i64 \
  --require-exact isa/aarch64/arithmetic.clif:%msub_i32 \
  --require-exact isa/aarch64/stack.clif:%stack_load_small
```

## Final implementation validation

[final-validation.json](final-validation.json) records the validated source head,
normal full build (1,417 jobs), normal crate build (1,171 jobs), runtime,
stack-allocator, encoder and Python results, and log hashes.
[final-paired-root-axioms.json](final-paired-root-axioms.json) records exact
original/cleanup axiom-set parity for optimizer-proven, legalization, totality,
emission, input-size-bound totality and executable correctness/totality roots.
The optimizer root also passes Lean MCP verification and source scan.

[e2e-identity-parity.json](e2e-identity-parity.json) compares the same 1,150
function identities and successful checker stages in both modes, including all
161 legalized identities. It records zero losses, gains or changed stages.
Reproduce the manifests after building `lean-e2e-check`:

```sh
FV_MEMCAP=22G scripts/memcap.sh .lake/build/bin/lean-e2e-check \
  --identity-report /tmp/cleanup-identities.json
FV_MEMCAP=22G scripts/memcap.sh .lake/build/bin/lean-e2e-check \
  --no-dead-cleanup --identity-report /tmp/legacy-identities.json
```

Compare the reports' `functions` arrays by file, original function index, name
and successful stages. The top-level `dead_cleanup` field records the mode.
The declaration source inventory preserves all baseline occurrences; it is a
source retention check, not a kernel proof count. The normal builds establish
that the retained declarations and new adapters elaborate together.
