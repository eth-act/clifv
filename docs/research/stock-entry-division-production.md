# Dividing entry blocks in Stock production

Candidate158ffc0d extends the landed two-block class to constants, nop and
signed/unsigned division/remainder in the entry body, followed by the existing
scalar/division/mask successor. New definitions are forwarded; inherited entry
values remain available regardless of local demand.

Shared source/body/jump composition preserves source definedness and the
original continuation/fuel. A first entry trap ends before the jump; a later
trap follows the completed body, actual successor copies and successor run.
The instruction-zero ABI theorem covers both cases. Old quiet-entry and
whole-function division-carry variants retain their exact interfaces.

The new input-only class checker derives the existing Scalar.Domain under the
original source/scope/dominance/ABI conditions. Existing CfgBoundary and the
CompiledSemanticNI.cfg constructor handle paired physical execution; no new
machine model or output certificate is introduced. Route6 is appended; old
artifact indices0–5 remain fixed. Every candidate failure retries the previous
complete CFG pipeline with original source, allocator and settings. Existing
optimizer/tail and exception selection remains, including checked mixed programs
with a new-class function and retained try calls.

Formal witnesses execute entered7/3, inherited7 and copied2 to return9, and an
entry zero-divisor trap. Compilation is checked in the kernel; the only new
fixed native fact is original-input dominance, confined to labelled witnesses.
The generic source domain uses only the standard three axioms. Two bundled MCP
reviews are clear; all12 new source audit roots and8 carry roots pass.

Native cohort:16 functions, four widths, nine ABI arguments, source slot,
nonempty copies, signed overflow, entry zero and later zero/overflow. The later
signed overflow differs from the entry zero trap so attribution is observable.
Both allocators and cleanup modes pass34 integration checks and3840 Lean byte
executions against480 Cranelift references, zero disagreements. Actual CLI,
verified linking, generated-proof compilation and generated axioms pass. The
prior CFG cohort retains its34 integration checks. Runtime/encoder and both
original/parent identity-stage cohorts pass; verified examples pass.

Terminal author gates on implementation `158ffc0ddf88459d411033bfc37f6577ab102278`
(base main `ce83af2cb49585a64a4e4134001945c729f486da`):

- Full normal build: 4,048/4,048 modules, 80 rebuilt, exit 0.
- All 90 audit files pass, 3,499 reported roots; all 3,486 previous
  axiom sets are exactly unchanged. All six declaration-owner partitions pass.
  The recorded 11 old public headers remain exact; the preceding local-carry
  checkpoint separately preserves its 12 old headers and seven old axiom sets.
- Runtime: 114 corpus, 22 extra and 5,755 runnable cases, no failures or
  disagreements. Encoder: 1,398 identical, zero differences.
- Both E2E modes: 1,159 accepted; all 1,150 original identities and all
  1,159 parent identities retain their ordered successful stages.
- Verified examples: fv-demo 21 matching tests/two verified ELFs;
  survey 53 matching tests/18 verified ELFs.
- Actual crate-proofs package: 93 modules, 96 successful recorded commands.
- Fresh real-crate comparison: 4,543 symbols, 900 exact. Paired against
  `ce83af2c`, using the same captured inputs and settings: 900→900 exact,
  zero gains and zero losses. The prior class's 13 gains are retained.
  Symbol agreement is not unique-function coverage or goal completion.

Raw receipts, generated proofs, original inputs, binaries and hashes are saved
under `/tmp/stock-cfg-entry-body-*` and archived remotely on
`agent/stock-cfg-body-progress-20261025T025359Z`, at
`evidence/cfg-body-progress.tar.gz`. The archive manifest records the exact
source publication and archive SHA-256; subsequent updates preserve history.
Normal, native, post-native and trust controller receipts all bind the same
implementation head. Publication changes after that head are documentation only.

Main #630's CI red was independently traced to the existing #614 `leantar`
Layout-packing panic after its normal shard passed 858/858, not a new Stock
source failure. The log and hash are retained and reported in #261; no CI-green
claim is made. Author-gated merging follows docs/TO-PROVE.md §7.

This advances #140; it does not establish Stock-only compilation success or
complete arbitrary CFG/effect/call/whole-driver simulation. Retained fallback
is acceptance preservation, not a completeness theorem. Broader scalar entry
bodies, conditional/table/critical edges, loops, memory/effects/calls and all
original-domain completeness/consumer obligations remain active.
