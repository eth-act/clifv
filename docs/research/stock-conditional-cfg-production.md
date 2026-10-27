# Conditional Stock production activation

Validated implementation `31a1befea3ed925a3fc1378a0d889fe726f087a8`, based on merged #634 (`d6218f29`).
PR #635 activates wide entry-parameter conditional branches with arbitrary
supported scalar entry/return-leaf bodies. Original source choice, final aliases,
demand/availability, returns and first traps compose through actual direct and
synthetic copy routes and instruction-zero ABI entry into unchanged Scalar.Domain.

Default compiler, checker, verified linker and generated-proof consumers append
route9, retaining0–8 and complete prior ForwardCfg pipeline fallback on the same
original inputs, allocator and settings. The ABI read boundary now proves virtual
integer zero/nonzero branches; old theorem variants and public headers remain.
No allocator, shared LowerSim or CLIF semantic change.

| Author gate | Result |
| --- | --- |
| Normal FV/FVTest / production tools | 4161 keys / 4958 jobs |
| Trust / owned checks | 95 audits,3698 roots,6 partitions; all3592old sets exact |
| Focused roots | 111standard-only;2fixed input-check witnesses share2inventoried permitted native facts |
| Conditional / retained forward / linear | 78 /78 /78 commands |
| Retained scalar-entry / entry / CFG | 70 /34 /34 commands |
| Actual native byte execution | 24000Lean /3000Cranelift references;0fail/0disagree |
| Runtime / encoder | 5755/0/0,7unchangednotrunnable /1398identical,0different |
| Both E2E modes | 1159accepted,0rejected; original1150/prior1159identity and stage parity |
| Verified examples / actual crate-proofs | 21+53tests,20ELFs /93modules,96commands |
| Actual paired capture | 4543functions;900→900matches,0gains/losses/changed bytes |

All candidate/reference source inputs and rebuilt example bytes/relocations bind
to the paired snapshot; an extra check includes full relocation target names.
The historical cross-compiler metric compares instruction bytes and relocation
offsets/types/addends. These measurements show preservation, with no agreement
gain. CI was cancelled and is not claimed passed; author-gate policy applies.

Historical failed harness/memory-cap runs remain saved. The identity command's
output basename collided with its runner record; a separate immutable maintained
gate repaired reporting. Original commands/logs remain, and no failed gate counts
as passed. Remaining cohorts used two8GiB lanes after full/example checks, with
2sharedCPUs and the existing warm cache. The healthy forward cohort completed
before its serial controller was retired; no cohort was duplicated.

[Machine receipt](stock-conditional-cfg-production.json) binds the gates and
source hashes. Remote evidence `34cef2dc4beaa2497220617a5ffa39d644e840c3` preserves
71091files in five bounded parts (167335282compressed bytes),
with every archived file and remote part verified against its hashes. Prior
source/evidence history and dirty saved views are preserved.

Timing evidence is retained per command. Current class validation ran04:11–04:37
UTC; forward retention04:37–05:12; independent full/example gates05:07–05:16;
remaining retention then used both lanes. Follow-up proof work overlapped those
checks and remains separate from this validated implementation.

Full #140 remains open. Next deliver the prepared ranked conditional tail class,
then general conditions/per-edge transfers, table/bit-test/loops, uncovered
families/effects/calls and original-domain source/block/whole-driver simulation,
Stock-only completeness and downstream completeness. Fallback is acceptance
preservation. No first-class or proof-fragment completion claim is made.
