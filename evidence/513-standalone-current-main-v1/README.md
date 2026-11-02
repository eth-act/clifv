# Standalone513 current-main validation

The source boundary is actual main3b586e45bb65855c9e6c0640f3e9f5f75abd4446.
The standalone candidate tree is115baa5cc12179216ffb6ef94cf61d1d1c993ba6.
It contains the exact207-file extraction and no production892implementation.
It preserves372headers,203consumer bodies,and eight moved declarations.

The baseline closure contains224project modules. The candidate closure contains226sources and seven changed targets.
All project modules must compile from the owned source. LEAN_PATH excludes every frozen/global project library.
Only the pinned Lean4.34.1toolchain supplies external artifacts; all11explicit external imports have recorded hashes.
No worktree,warm cache,shared artifact mapping,branch,or publication changed.

## Actual results

- The2GiBattempt freshly compiled119project modules.
- `FV/Backend/Proof/IselData.lean` then exited137. Its measured peak was2147483648bytes; oom1and oom_kill1.
- The parent approved a3GiBattempt after quiescing the1GiBI/O recovery.
- The continuation verified and retained all119successful source/output hashes. It retried only the missing IselData command.
- IselData again exited137. Its measured peak was3221225472bytes; oom1and oom_kill1.
- Both Lean diagnostics were empty. No IselData output file completed.
- The continuation stopped immediately. No further module,candidate kernel,or type/axiom comparison ran.

`state-v1.json`, `state-v2.json`, and both kernel directories preserve the exact commands,memory statistics,source hashes,output hashes,and diagnostics.
`stopped-3g-checkpoint.json` records the reviewed stopping point. No further retry or budget increase occurred.
The3GiBkernel allocation is released. The preserved1GiBI/O recovery resumed under watcher3253618.
The healthy12GiBcompiler and scheduler remain untouched.

The measured result establishes that this IselData invocation needs more than3GiB.
It does not establish the exact sufficient cap or an implementation error.
A further attempt needs an explicit coordinator decision. Preserve the119passed outputs for reuse.
Do not infer success from old focused receipts,signature equality,or historical artifact presence.

## Remaining gates

The fresh baseline still needs105modules,including IselData.
The candidate still needs seven proper kernels and eight full type/axiom comparisons.
The retained historical required axiom sets remain exact obligations.
The prepared review script verifies those sets only after a successful kernel gate.
Full affected normal keys,reverse importers,libraries,audits,tools,runtime,and identity gates remain separate mandatory work.
Neither partial attempt establishes a standalone delivery gate or original140completion.

## Ownership and cleanup

The delegate owns both isolated packages and their temporary outputs.
Retain the119successful outputs while the coordinator chooses the next validation route.
Preserve all sources,diagnostics,hashes,and receipts before deleting expendable outputs.
Exclude `.lake` build outputs from recovery archives.
Never mutate frozenV or its shared warm cache through these scripts.
