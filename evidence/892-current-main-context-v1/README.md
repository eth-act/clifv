# Current-main892/513 context gate

Owner: worker-O execution delegate. Publication belongs exclusively to the execution coordinator.
The protected source view and shared warm cache remain untouched.
No Lean compiler ran during preparation.

The exact source boundary is main3a6719b44b0e6b38e24cd0de82655f93b78272a9 plus the final18production files.
The reconciled892head is36dd36a6c1746acb1741dd5c984b0ead1b8a2d18; its tree is7dbf27cb7545c4a9d137719c8f59d7b05d91c074.
The reconciled513head is328541fa3402deac8d4df8ff7f790e95196c37a3; its tree isa4dcc3fa905fad9d6c0c7f2a49fcd335b5989f84.
Both source trees and every production file hash match the prepared packages.
`reconciled-targets.json` records these boundaries. Main896adds three unrelated files and does not restart this recovery.

## Actual blocker and resource split

Full-gate run41408842551uses exact push head3a6719b4.
Only its Plan artifact existed at the last checkpoint. No successful module-stage artifact was available.
The required2881current-main baseline module keys remain unverified until coherent producer outputs arrive.
This is an artifact-availability blocker. Historical memory profiles do not establish a current OOM.

The parent assigned1GiBto I/O recovery and reserved the remaining2GiBfor a separate short gate.
Watcher3203909runs the I/O-only recovery. It cannot start kernels automatically.
The older watcher's nonzero exit records a controlled resource handoff. No compiler or transfer was killed.
`resource-split-v1.json` preserves that event.
The kernel runner requires a new explicit parent grant after the split.

## Coherent artifact recovery

`recover-ci.py` accepts artifacts only from successful producers at the exact run/head.
Every downloaded artifact records its producer job,head,run,archive hash,and original output mappings.
Each shard archive is bounded to2GiB. An assembled exact-head artifact is bounded to8GiB.
The cumulative download bound is40GiB. At least100GiBmust remain free.
Hashing and extraction use bounded buffers. Compression/extraction threads remain bounded.

All staging and disposable cache metadata live under the owned package's `.lake` directory.
This is temporary artifact staging,not another warm cache. No global cache import occurs.
The runner never changes frozenV's mappings or artifacts. It never runs the old870import scripts.
Before restoration,it removes only owned output links so no writer can modify a shared inode.

The package uses the actual pinned Lake configuration,toolchain,and dependency manifest.
Recovery checks `lake build --no-build` for all2881required baseline targets.
A cache miss cannot start a compiler and cannot count as a pass.
Nonreproducible same-key/different-output copies must satisfy this complete current-input key check before use.
The assembled exact-head artifact becomes the preferred coherent selection when it exists.
`coherent-baseline-output-hashes.json` records every required restored output hash after success.

The initial strict invalidation inventory contained2683modules. It is a broad normal-key rebuild,not a focused gate.
The historical profiles include targets above3GiB. No current OOM was measured.
The narrower old-artifact interface-bridge strategy is explicitly unselected.
Current validation waits for coherent actual-current artifacts instead of relabeling stale import-equality receipts.

## Focused execution after a new grant

The runner compiles12proper892modules and runs six unchanged axiom audits.
It compares the six old typed variants' exact axiom sets with their retained counterparts.
It executes the actual backend's six complete object comparisons.
It reconstructs six complete original integer/typed bundles and runs backend,layout,linker,checker,generated proofs,and audits.
It preserves original complete input hashes and exact actual allocator answers.
It repeats the two final typed compiler modes with their actual source/peak theorem selection.
All eight generated cases must pass68audited roots.

Only then does it run the seven513kernels against the completed892context.
It compares eight full elaborated types and exact axiom outputs with the current892baseline.
The513source context contains226files after current import pruning. No old230-source equality is claimed for it.
The old372headers,203bodies,and eight moved declarations remain preserved separately.

`run-focused.py` requires both a coherent recovery receipt and a new `kernel-grant.json`.
That grant must identify the coordinator,slot3G,exact892head,and explicit approval after the I/O split.
The runner unlinks every owned output before Lean writes it. It preserves unique attempt logs and source hashes.
Every command uses the unchanged source,ABI,heap,world,trace,return,allocation,and cleanup conditions.

This gate is direct current-context kernel/AX and actual-matrix validation.
It is not full candidate normal-key,reverse-importer,library,crate,agreement,or original-goal completion.
The shared broad gates and each PR's exact-head/source/review/tested-merged-tree checks remain separate obligations.

## Cleanup

Retain all sources,configs,producer provenance,mappings,output hashes,generated Lean,diagnostics,and receipts.
Exclude package `.lake` outputs from backups.
After the gate,remove disposable CI stages,cache metadata,and isolated build outputs.
Remove the513output snapshot after its hashes and diagnostics are saved.
Never clean frozenV or alter its one shared warm cache through these scripts.
The delegate owns all temporary output cleanup and must explicitly release its allocation.
