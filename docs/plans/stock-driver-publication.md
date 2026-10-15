# Stock driver publication queue

Updated UTC: 2026-10-14T23:44:00.305659+00:00

The user now authorizes pushes for remote backup and roughly three validated squash-merged PRs per day. This supersedes the earlier no-push/no-merge instruction. The original #140 goal remains incomplete; publication of proof families does not establish production-driver correctness.

Remote backups:

- Validated stack: `agent/stock-driver-validated-backup`, tip `01081291e566bc4eb80419a526c5725406ed62b7`.
- Comparison WIP: `agent/stock-driver-wip-backup-20261014T234241Z`, snapshot `0c6586368a9270105f6d918b1ebcdc5cc578ac71`. Includes all 280 dirty paths without changing the active branch or index. This is a recovery snapshot, not merge-ready work.

Publication queue:

| Order | Batch | Local validated tip | Publication state |
| --- | --- | --- | --- |
| 1 | Fused logical NOT and NOT-of-XOR | `a739ad5` | Merged #180 at `72f2e574eb718903f2534d0b06ddce4b662672f0`; all three CI checks successful |
| 2 | Multiply and fused multiply-add/subtract | `5eb7315` | Merged #181 at `40805b7ecccb10942da89aca3193ad41108e8488`; all three CI checks successful |
| 3 | Scalar shifts and helper foundations | `30f48dc` (includes `b3577ee`) | Merged #182 at `70d187b2fbdb55a1954a9cbcb566b68feab1798b`; all three CI checks successful |

Before publication, committed source hashes and saved gate-log hashes were rechecked for all three batches. Each has full build/crate/runtime/encoder/both-E2E and theorem-audit receipts. Merge only after CI succeeds and the submitted tree is confirmed to match validated evidence. Squash merges only. Further families remain queued in the validated backup stack; comparison work is incomplete and must pass its full-family gates before becoming a merge candidate.

After each publication or merge, update #44 and this queue. Keep unfinished comparison work in driver-proof-resume intact, and continue all original whole-driver/effect/simulation/completeness and production-integration obligations.

Completed three squash merges on October14. All three CI measurements preserve671 exact code artifacts with0 gained/0 lost matches. Publication evidence: `docs/research/stock-driver-publication-20261014.json`. Next continue comparison proofs and keep validated later families queued for subsequent publication batches.

Latest full WIP/publication backup: `agent/stock-driver-wip-backup-20261014T235611Z`.

Adjusted-immediate predecessor checkpoint:241 modules/380 normal roots,16 fresh MCP checks; source/RHS/715 witnesses pass, retained/complete driver integration pending. Remote backup `agent/stock-driver-wip-backup-20261015T000552Z`. Three-PR October14 delivery remains #180/#181/#182.
