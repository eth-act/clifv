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
git apply docs/research/legacy-dead-instruction-cleanup/prototype-main.patch
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
