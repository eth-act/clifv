# Stock bmask/nop production activation

This change enables the proved Stock driver for single-block functions containing
`bmask` and `nop`, interleaved with every previously enabled scalar and division
family. Source and result widths vary independently across i8/i16/i32/i64.
The existing ordinary compiler, checker, linker and generated-proof routes share
the extension and retain legacy fallback. Existing selectors, theorem variants,
input conditions, original values/slots and return/trap behavior remain.

The proofs derive actual helper selection, retained result binding, final-alias
machine execution, guarded original-source transfer and complete body/ABI
composition. CSETM has the required ABI-read/flag-frame proofs. The real scan
omits ordinary zero-result nop; this is not a claim that an emitted Nop rule runs.
The global `pureInst` look-through predicate is unchanged.

## Implementation and author evidence

The validated implementation is `0aecff7cbeb8e0dc295855bf27d77c4ffdfffdfa`,
based on main `a946fbc4fa10abe50bf551a0c1842c169f472400` (#623).
All 24 readiness requirements passed on that implementation. Final publication
adds this receipt/ledger/plan and removes one extra EOF blank line; normal input
keys, compiled leaf/executable equivalence, the public audits and ordinary CLI
are checked separately for the publication commit. The original source-head
receipts retain their original provenance.

- Full normal FV/FVTest: 3,976/3,976 modules, 80 rebuilt; all 11 affected tools build.
- Complete fixed pipelines: 216 positive configurations (36 functions across
  three conventions and both cleanup settings), including all 16 independent
  width pairs, nine arguments, a real slot, unused/consumed values and division
  zero/overflow traps.
- Actual encoded execution: 12 objects, 3,888 Lean byte executions against 972
  Cranelift references; zero failures/disagreements. Both real allocators and
  both cleanup settings pass; missing-oracle control passes. All 12 ordinary
  compiler CLI objects exactly match the raw Stock API outputs.
- Actual new and retained Narrow/ReturnedDiv/GeneralDiv CLI, linked artifact and
  generated-proof cohorts pass, including the original flat-multiply artifacts.
- Trust: 656 reports across 23 audit files pass; all 70 ownership partitions pass.
  The 56 new reports include 54 standard-only roots and two finite pipeline
  witness roots sharing one fixed native fact. The 22 production roots pass one
  bundled MCP review. No new handwritten or compiler native axioms.
- Exact prior axiom sets: 497 production roots, 13 sink roots, 23 narrow roots
  and seven changed local-source roots. All 65 old theorem headers in modified
  modules remain; 32 prior native profile/width grids are identical. The 21
  inherited two-axiom shape facts retain their unchanged 154-module import graph.
- Runtime: 5,755 pass, zero failures/disagreements; the original 7,971 unsupported
  and seven non-runnable cases remain explicit. Encoder: 1,398 identical,
  zero different. Both cleanup E2E modes accept 1,159 programs with zero rejects;
  all 1,150 original and 1,159 prior/parent identities and ordered stages remain.
  Crate proofs pass. Fault co-simulation: 15,200 vectors, zero failures.
- Verified fv-demo and survey pass. Fresh paired real-crate comparison retains
  887/4,543 exact symbol comparisons, with zero gained/lost symbols and no
  changed report rows. These are symbol comparisons, not unique function
  coverage or a percentage of goal completion; the default allocator remains Lean.

The full source-bound readiness and consumer/trust/native/identity/example logs
are remotely backed up in evidence commit
`dc34a26a9e01b481fa2515d6ec454917a8f8ff6a` on `agent/stock-mask-progress-20261025T013019Z`:
`evidence/mask-progress.tar.gz`, SHA256 `bea4de2841541e7440207896903fcfe6ddf8ea658ee8d820663761ab9d9d8364`.
The snapshot contains 6,061 files. Local references are
`/tmp/stock-mask-readiness-0aec.json`, `/tmp/stock-mask-component-readiness.json`,
`/tmp/stock-mask-parallel-controller-v1.json`, and
`/tmp/stock-mask-real-crate-parity/{provenance,summary,parent-parity}.json`.
The publication supplement records its own head and replay evidence separately.

## Remaining original goal

This is a production class extension, not completion of #140. Original ABI and
reachable-helper gaps, branches/successor arguments/critical edges/block
parameters/loops, memory/effects/atomics, calls/sret/TryCall/unwind, complete
source/block/traversal/whole-driver simulation and Stock-only/downstream
completeness remain. Existing no-opt/no-TryCall CLI guards remain. Fallback and
successful lowering do not establish completeness.

The next source/block closure derives quiet records for arbitrary original
blocks, then carries the actual successor-specific vectors through the existing
per-edge preparation and all consumers. Reuse the saved entry/edge/CFG proofs;
retain the original scope and all required theorem variants and axioms.
