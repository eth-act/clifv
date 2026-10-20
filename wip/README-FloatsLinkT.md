# FloatsLinkT WIP (agent/floats-c8l-wip; not for merging)

Unbuilt drafts of the typed link layer (S11e5 Stage C slice 8), waiting for the c5f tree in the
shared cache. Move this directory out before merging; build each module at 6G in order:
LinkArmT, LinkCheckT, (generate the rest), LinkOutT, PipelineCheckT, LinkOutCleanupT,
LinkScopeIntT, ExecProvenT/DeadCleanupExecProvenT chain, Link/ExeT, Link/DeadCleanupExeT,
FVTest/Link/FloatExeT.

Generator: `wip/FloatsLinkT_copy.py` (deps from `wip/FloatsLinkT_deps.lean` via
`lake env lean`, writes /tmp/FloatsLinkT_deps.tsv). Run `python3 wip/FloatsLinkT_copy.py SEEDS TARGETS`
to compute the copy set (/tmp/FloatsLinkT_copyset.json), then `main2(extra_imports)` to emit
`FV/E2E/<Mod>T.lean` (renames: suffix T; LinkSys.Ok.* -> LinkSys.OkT.*). LinkArmT and LinkCheckT
here were generated from the LinkArm/LinkCheck deps and then hand-patched: do NOT regenerate
them over the patches.
