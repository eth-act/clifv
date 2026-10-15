# Stock driver publication queue

Updated UTC: 2026-10-15T02:19:51.980555+00:00

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
| 4 | Prove Stock scalar casts, reduction aliases and source-root closure | `8a2786e` | Merged #183 at `90975b2b0c552186d5e0a02174b9375e06fe623b`; all three CI checks successful |
| 5 | Prove Stock negation, bit reversal and byte swaps from original sources | `9bab358` | Merged #184 at `1498523f3514c7e4fab31dade35baa2c39c70df7`; all three CI checks successful |
| 6 | Prove Stock scalar bit counts and rotations through retained records | `3ae4c79` | Merged #185 at `186d1bfae64617a990ae7c54fe2bb2c3a633542b`; all three CI checks successful |
| 7 | Prove Stock scalar add and subtract through original source dispatch | `22894a1` | Merged #186 at `f5176083e121de580b5c9131880ff84fc5b4ba0a`; all three CI checks successful |
| 8 | Prove Stock signed and unsigned high multiply source transfer | `e56bb87` | Merged #187 at `dee89355966cba3d59038b9727a3c36ed7e1b8d1`; all three CI checks successful |
| 9 | Prove Stock division and remainder source execution and traps | `0108129` | Merged #188 at `30cdc5f14c600eecadf25681a6c2059c8acd0a06`; all three CI checks successful |

Before publication, committed source hashes and saved gate-log hashes were rechecked for all three batches. Each has full build/crate/runtime/encoder/both-E2E and theorem-audit receipts. Merge only after CI succeeds and the submitted tree is confirmed to match validated evidence. Squash merges only. Further families remain queued in the validated backup stack; comparison work is incomplete and must pass its full-family gates before becoming a merge candidate.

After each publication or merge, update #44 and this queue. Keep unfinished comparison work in driver-proof-resume intact, and continue all original whole-driver/effect/simulation/completeness and production-integration obligations.

Completed three squash merges on October14. All three CI measurements preserve671 exact code artifacts with0 gained/0 lost matches. Publication evidence: `docs/research/stock-driver-publication-20261014.json`. Next continue comparison proofs and keep validated later families queued for subsequent publication batches.

Latest full WIP/publication backup: `agent/stock-driver-wip-backup-20261014T235611Z`.

Adjusted-immediate predecessor checkpoint:241 modules/380 normal roots,16 fresh MCP checks; source/RHS/715 witnesses pass, retained/complete driver integration pending. Remote backup `agent/stock-driver-wip-backup-20261015T000552Z`. Three-PR October14 delivery remains #180/#181/#182.

Canonical predecessor selection checkpoint:247 modules/386 normal roots,6 fresh MCP checks; accepted original4097/8193 selected-helper witnesses pass, retained/source-step integration remains next. Remote backup `agent/stock-driver-wip-backup-20261015T001800Z`.

Integrated predecessor retained/source checkpoint:267 modules/412 normal roots,26 fresh MCP checks; eight complete original32/64 signed/unsigned Stock.lower/source-step witnesses pass. Other forms/minmax/select/full family gates pending. Remote backup `agent/stock-driver-wip-backup-20261015T003200Z`.

Nonencodable register fallback checkpoint:279 modules/429 normal roots,17 fresh MCP checks; four complete arbitrary32/64 signed/unsigned Stock.lower/source-step witnesses pass with actual constant193-to197 alias. Other forms/minmax/select/full family gates pending. Remote backup `agent/stock-driver-wip-backup-20261015T005914Z`.

Narrow comparison core checkpoint:285 modules/439 normal roots,10 fresh MCP checks. Actual555/556 requests,657 right extensions and5117/5108 RHS preserve full state; original8/16 predicates and actual aliased extended-compare/cset machine values pass. Selection/retained/complete source-step coverage and full family gates pending. Remote backup `agent/stock-driver-wip-backup-20261015T011351Z`.

Narrow source-value composition:288 modules/443 roots,4 fresh MCP checks. Successful RHS internally derives guards/mappings/full state; actual left extension plus715 holds original predicate, with arbitrary-word witnesses in constructed contexts. Retained availability must discharge scratch separation; selection and complete Stock.lower/source witnesses pending. Remote backup `agent/stock-driver-wip-backup-20261015T012335Z`.

Narrow nonconstant retained/source integration:300 modules/456 roots,13 fresh MCP checks. Actual5117/5108/652/715/original958/172 selection, value-independent two-register allocation, availability-derived scratch separation, binding and guarded original source/getter transfer pass. Four complete actual Stock.lower/source-step witnesses cover arbitrary8/16 signed/unsigned pairs. Constant classifications/minmax/select/full family gates pending. Remote backup `agent/stock-driver-wip-backup-20261015T013354Z`.

Narrow constant immediate retained/source integration:314 modules/472 roots,16 fresh MCP checks. Actual5134/652/715/original958/172 first-match, exact producer/full state, original DFG constant semantics, binding and guarded source/getter transfer pass. Four complete actual Stock.lower/source-step witnesses cover arbitrary8/16 inputs against3/129/4096, constant slot193 deliberately777 and demand31=0. Register fallbacks/constant-left/dispatch/minmax/select/full family gates pending. Remote backup `agent/stock-driver-wip-backup-20261015T014755Z`.

2026-10-15T01:59:09.809510+00:00: Merged https://github.com/eth-act/clifv/pull/183 (`90975b2b0c552186d5e0a02174b9375e06fe623b`), Prove Stock scalar casts, reduction aliases and source-root closure. All three fresh CI checks successful; 671 exact artifacts, 0 gained / 0 lost. Submitted/main trees exactly match validated 8a2786e59e71aa6fe0d28a5e953b04df71167a63. #140 remains incomplete; production legacy.

2026-10-15T02:03:09.215313+00:00: Merged https://github.com/eth-act/clifv/pull/184 (`1498523f3514c7e4fab31dade35baa2c39c70df7`), Prove Stock negation, bit reversal and byte swaps from original sources. All three fresh CI checks successful; 671 exact artifacts, 0 gained / 0 lost. Submitted/main trees exactly match validated 9bab3587f95c05902d25209d235dacf9bae50399. #140 remains incomplete; production legacy.

2026-10-15T02:07:49.502849+00:00: Merged https://github.com/eth-act/clifv/pull/185 (`186d1bfae64617a990ae7c54fe2bb2c3a633542b`), Prove Stock scalar bit counts and rotations through retained records. All three fresh CI checks successful; 671 exact artifacts, 0 gained / 0 lost. Submitted/main trees exactly match validated 3ae4c795240a283af0bbb31e3656a7748a12e833. #140 remains incomplete; production legacy.

2026-10-15T02:11:31.416315+00:00: Merged https://github.com/eth-act/clifv/pull/186 (`f5176083e121de580b5c9131880ff84fc5b4ba0a`), Prove Stock scalar add and subtract through original source dispatch. All three fresh CI checks successful; 671 exact artifacts, 0 gained / 0 lost. Submitted/main trees exactly match validated 22894a14dd632b85d5900efc9d93d6094ceec0b5. #140 remains incomplete; production legacy.

2026-10-15T02:15:13.832057+00:00: Merged https://github.com/eth-act/clifv/pull/187 (`dee89355966cba3d59038b9727a3c36ed7e1b8d1`), Prove Stock signed and unsigned high multiply source transfer. All three fresh CI checks successful; 671 exact artifacts, 0 gained / 0 lost. Submitted/main trees exactly match validated e56bb87ddcc83ac2945e7f75ac17341f20864793. #140 remains incomplete; production legacy.

2026-10-15T02:19:28.370577+00:00: Merged https://github.com/eth-act/clifv/pull/188 (`30cdc5f14c600eecadf25681a6c2059c8acd0a06`), Prove Stock division and remainder source execution and traps. All three fresh CI checks successful; 671 exact artifacts, 0 gained / 0 lost. Submitted/main trees exactly match validated 01081291e566bc4eb80419a526c5725406ed62b7. #140 remains incomplete; production legacy.

## Backlog delivery 2026-10-15T02:19:51.980555+00:00

The previously committed, fully validated backlog was delivered in six semantic squash merges: #183 Prove Stock scalar casts, reduction aliases and source-root closure, #184 Prove Stock negation, bit reversal and byte swaps from original sources, #185 Prove Stock scalar bit counts and rotations through retained records, #186 Prove Stock scalar add and subtract through original source dispatch, #187 Prove Stock signed and unsigned high multiply source transfer, #188 Prove Stock division and remainder source execution and traps. All18 fresh CI checks passed; each comparison retained671 exact artifacts with0 gains/0 losses. Each published and merged tree exactly matches its validated local checkpoint. All253 changed proof files are covered by final source hashes; full saved gate-log hashes, normal/MCP results and seven exact compiler theorem trust sets verified. Evidence: `docs/research/stock-driver-backlog-publication.json`.

Ongoing discipline: aim for roughly three coherent, validated PR merges per day; push reviewed work and recovery snapshots promptly for remote backup. PR count is a delivery target, not a reason to split inseparable proofs or bypass gates. No additional routine permission is required for user-authorized pushes/squash merges.

All314 validated comparison sources remain unchanged. Six newer narrow constant fallback modules are preserved but unvalidated (selection heartbeat timeout). Full #140 remains active/incomplete; production is still legacy. Resume remaining comparison fallback/constant-left/dispatch/minmax/select and full-family gates, then remaining families/effects, source/block/whole-driver simulation/completeness and actual compiler/checker/linker/generated-proof consumer integration under the original conditions. Preserve old variants, identities/stages and exact required axiom sets; require fresh complete Stock comparison before production cutover. Remote recovery branch: `agent/stock-driver-wip-backup-20261015T021951Z`.

Narrow constant register fallback checkpoint:330 modules/489 roots;17 fresh MCP checks, all prior314 source hashes/472 trust sets unchanged. Five complete actual Stock.lower/retained/source-step witnesses cover8/16 signed zero/high-bit and16-bit unsigned8193, real193→197 alias and full preservation. Full comparison family/repository gates and full #140 obligations remain. Remote backup `agent/stock-driver-wip-backup-20261015T023042Z`.

Nonzero constant-left and total source classification checkpoint:346 comparison modules/507 roots,18 fresh MCP checks; all330 prior sources/489 axiom sets unchanged. Four complete actual Stock.lower/source-step witnesses cover arbitrary right operands at8/16 with signed high-bit and unsigned left constants; real left constant193→197 and full preservation. Source classification derives typed constant payload or NonConstantSource from original mapped context. Remaining zero-left relational/32–64 left/both-constant paths, unified dispatch/minmax/select and full family/repository gates. Full #140 incomplete, production legacy. Remote backup `agent/stock-driver-wip-backup-20261015T024254Z`.

All-width nonzero constant-left source dispatch:364 comparison modules/528 standard-only roots,21 fresh MCP checks,346 previous hashes/507 sets unchanged. Four complete32/64 signed/unsigned witnesses plus four unified8/16/32/64 source-transfer witnesses pass. Original scope derives scalar width internally; old stronger variants retained. Full comparison-family/repository and original whole-goal gates pending. Remote backup `agent/stock-driver-wip-backup-20261015T025536Z`.

Actual narrow comparison dispatch checkpoint:370 modules/535 standard-only public roots,7 fresh MCP checks;364 prior source hashes/528 axiom sets unchanged. Complete actual-match observations and arbitrary-word actual narrow emitter witnesses pass. Retained binding/source-step integration and full comparison/repository gates remain pending. Six backlog PRs #183–188 are already merged; no remaining previously validated family is waiting for publication. Full #140 active/incomplete, production legacy. Latest remote recovery snapshot `agent/stock-driver-wip-backup-20261015T034701Z`.

Universal actual narrow retained/source integration:395 modules/794 jobs,562 standard-only public roots,27 fresh MCP root audits (26 lean_verify and one standalone import/source scan after a transport timeout).370 prior source hashes/535 trust sets and122 division sources unchanged. All-operand8/16 actual root selection, availability-derived separation, result binding and guarded original source/getter transfer now pass without operand classifications. Twenty complete Stock.lower/retained/source-step witnesses plus four-case arbitrary-word pipeline growth witness verified. Full comparison-family/repository gates remain pending; full #140 active/incomplete, production legacy. Next universal32/64 actual dispatch, minmax/select and all original effect/whole-driver/completeness/production obligations. Use bundled MCP root audits plus original source scans in future batches to avoid repeated witness elaboration. Latest verified recovery branch `agent/stock-driver-wip-backup-20261015T040646Z`.

Universal scalar icmp actual-rule/source dispatch checkpoint:420 modules/819 jobs,589 standard-only public roots; one bundled Lean MCP audit covers all27 new roots and420 original source scans are clean.395 prior source hashes/562 trust sets and122 division sources unchanged. Actual32/64 full12-rule value dispatch,958/172 root/retained binding and guarded original source transfer now compose with universal8/16 into all-original-scalar icmp transfer without operand classifications; the getter-internal variant exposes original reads. Eighteen complete source witnesses include all8 adjusted4097/8193 signed/unsigned cases and both-nonzero3/5 constants with right slot194=777/demand0. All old variants retained, full #140 active/incomplete, production legacy. Next run full repository/identity/trust gates for coherent scalar icmp publication, then minmax/select and every original effect/whole-driver/completeness/production cutover obligation. Latest recovery branch `agent/stock-driver-wip-backup-20261015T042238Z`.
