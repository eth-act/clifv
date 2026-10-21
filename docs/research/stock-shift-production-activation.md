# Stock shifts in default production

Validated source ca069aa6e6402915b0ecca4482e6bb2edcd37b6e, based on actual
main 1246b455. The default shared scalar route now supports ordinary i32/i64
LSL/LSR/ASR and fused UBFM/SBFM shift pairs, including shifted NOT and count
values whose original source type differs from the shifted value. Original
input conditions, old theorem variants/selectors, required axiom sets, accepted
identities and successful stages remain. The cleanup whitelist is unchanged.

## Proof and production boundary

Actual original-source matching proves eight candidates: Ishl 874/873,
Ushr 893/884/883, Sshr 892/891/890. ShiftComplete.record_source derives the chosen
case internally, reusing six existing bridges. The two fused cases derive
nested original definitions/counts, guarded requests, exact emission and
fresh-write preservation; actual retained binding and demand/availability
transfer establish original source execution. ShiftBody composes source order,
ABI entry/return and no-trap through the existing Scalar.Domain. Generic
compiler/checker/linker/generated-proof consumers are reused. Proved shift
step/frame/transport/machine facts extend the existing scalar ABI read boundary.

The complete witness includes all eight roots across six ABIs and two cleanup
modes, both register and immediate counts, opposite-width count constants,
fused shift pairs, shared values, shifted NOT, dead work, a ninth stack-passed
argument, arbitrary source inputs and the original arbitrary explicit slot.
Only two new fixed native facts enter witnesses; universal compiler proofs
remain standard-only. Successful Stock lowering remains a premise of the
source refinement; fallback does not prove Stock-only completeness.

## Validation

All 18 primary gates and 13 ownership partitions passed on the frozen source:
2,728 normal Lake keys (2,725 scheduled modules), four affected tools and 1,579 crate
keys;49 trust audits / 1,470 roots;all 1,428 previous required axiom sets and 34 old public
headers exact. Ownership audit covers 2,898 standard-only core / 760 fixed-witness constants,
138 core / 25 witness / 12 executable owners and 25 exact native facts (previous 23 + 2).
One bundled domain MCP review reports only standard axioms and no warnings.

Strict real-regalloc2 and Lean allocation exercise whole-attempt retry and
missing-oracle controls.24 actual objects pass 1,512 native comparisons and 378
Cranelift reference executions with zero failures/disagreements. Current shift
and retained-multiply actual CLI/link/generated cohorts each pass 32 subchecks,
including 33-function slices, retained reconstruction, actual bytes, stack and
both preparation modes. Original flat-multiply inputs/ELF/proof sources remain
byte-exact and freshly regenerated current proofs compile in both modes.

Corpus: 4,737 pass / 0 fail with the same 7 known non-runnable cases; encoder: 1,321 identical /
0 different. Both E2E modes retain 1,159 accepted / 0 rejected, preserving original 1,150
and prior 1,159 identities and ordered stages exactly. Verified fv-demo passes 21 tests /
2 binaries; survey: 53 tests / 18 binaries.

## Provenance and recovery

The JSON receipt retains every passing record, input key, source head, log and
output hash. A wrong grouping in the witness expectation and a copied runtime
footer were caught and corrected; failures never count. The corrected arbitrary
input proof builds in 6 seconds with a bounded heartbeat budget. All 72 earlier strict
runtime outputs remain byte-identical to the fresh final run.

The original shift integration command completed all 32 subchecks with unchanged
inputs and intact artifact hashes, but outer reporting used a copied multiply
receipt path. Its failed outer record remains failed. A separate passing gate
verifies the complete original input fingerprint, all 32 successful subgates and
all generated/CLI/artifact hashes; only the known memcap cache exports and scope
INVOCATION_ID added by the validation wrapper are excluded when reproducing the
outer environment. The retained-multiply cohort ran separately with the correct
output path. A copied retained-script input path was repaired before that command
ran. No expensive successful subgate was relabelled or silently replayed.

Terminal evidence and all failures are remotely verified at
de6aae6e05c2a21ae1cc5709ed575fcb67dea354 on agent/stock-shift-evidence-20261021T220650Z.
Archive SHA256 0001730428d06e8ad64bf73e233f45ffd1469369b2e9a3d13f37ba1c04840e51,
10,143,570 bytes / 998 files. It includes next-cast kernel inventory/drafts and unique retained
artifacts. Preserved recovery sources remain untouched; four necessary worktrees,
one warm cache,742 GiB free and max 16 GiB aggregate / max 2 jobs.

Full original #140 remains open: casts and every remaining scalar/effect/control/
call/source/block/whole-driver/completeness/production-consumer obligation.
Next cast inventory is kernel checked: Uextend 810/811/815/808, Sextend 824/819,
Ireduce 946. Reuse existing guarded cast and zero-code alias-reduction bridges;
prove execution/exclusions before claiming complete cast activation.
