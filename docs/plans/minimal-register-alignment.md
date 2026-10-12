# Minimal register alignment

User-approved plan, 2026-10-12. Base main bc3a34c. Replacement-driver #135 remains paused.

1. Reproduce the 33 register-only cases from the current 96-case sample and capture prepared allocator requests. Reuse the saved lowering tracer and Stock allocation schedule; distinguish the candidate Stock-model trace from the actual pinned stock binary reference.
2. Test numbering only at the untrusted allocator boundary. Keep original lowering/checking, cleanup, instruction order, constraints and preferences. Permute all virtual-register references and their classes together; original Lean allocation checking still validates returned physical locations/edits.
3. Compare dense source-layout numbering (StockAlloc reserves192 initial IDs) and, only when allocator shapes admit a consistent mapping, numbering supplied by the saved candidate Stock schedule. Reuse construction/flow facts; do not reimplement the driver or resume its proof migration. Validate permutations and refuse inconsistent matches.
4. Measure exact artifacts for every focused identity, then the complete suite for any promising candidate. Require positive full-suite gains, zero lost matches/new rejections, unchanged accepted-input identities and normal required gates before production/default enablement.
5. Publish bounded measurement evidence. If numbering cannot explain the difference or traversal/sinking/constraints are required, stop that expansion and report the boundary. No claims that a numbering change fixes all33 cases.

Public compiler interfaces/theorem statements remain unchanged. Experimental tooling is opt-in. Check sparseIDs, aliases, branch parameters/arguments, multi-result operand reuse, exception reservations, class preservation and malformed mappings. Use Lean MCP when inspecting or changing Lean proofs; no new proof WP is claimed for research-only diagnostics.

## Implemented checkpoint

Dense numbering fixed0/33; schedule-derived numbering fixed28/33. Blind reversal
was rejected after249 gains/236 losses. The actual opt-in wrapper gives671->959
(+288/-0) across all1610 previously compared occurrences, with zero new rejections.
Full1422/crates1171, E2E1150/0, runtime114+22+4672 and encoder1292/0 pass; eight
renaming/refusal tests pass. All compiler/proof sources and defaults remain unchanged.
See docs/research/register-alignment.md and its receipts. The broader active driver
proof/cutover goal is not complete and must not be replaced by this wrapper.
