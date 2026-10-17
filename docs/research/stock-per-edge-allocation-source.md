# Actual indexed allocation and development consumer migration

`RegallocPerEdgePrepare` carries outgoing vectors with blocks through reachable
filtering, critical-edge splitting and reverse postorder. A split edge gets an
empty first copy and moves its original vector onto the new jump. A kernel
witness checks actual filtering, new edge insertion, reordering and equality of
that two-copy route with the original copy for arbitrary register values.

`RegallocPerEdgeSpill` implements selected copies on unique-predecessor entries
(after terminator-result stores), or before single-successor branches into
shared targets. Two-phase copies preserve parallel-copy reads. Outgoing-only
registers receive homes. The new home lookup uses dense value/class keys and
first-occurrence slot numbers, avoiding the standard HashMap's opaque mixHash
operation so complete fallback executions can reduce in Lean's kernel. The old
spill allocator is unchanged.

`RegallocPerEdgeDriver` serializes real vectors to regalloc2 and checks every
selected allocation, including fallback allocations, with checkAllocAt before
lowerRFunc. Oracle failure, Rust/Lean checker rejection, lowering failure or
emission unreadiness selects the checked indexed fallback. The three public
proof roots show that actual successful selection/lowering supplies an accepted
allocation and its full indexed M6 simulation. They do not assume that regalloc2
succeeds or that its answer is sound.

Complete original LowerScope+Dominated Stock conditional and critical-edge
functions inhabit the entire real preparation→forced checked fallback→lowering
pipeline in normal kernel proofs. The critical fixture's synthetic nodes reorder
while preserving their final-alias outgoing values. Both full executions inhabit
the driver-success/M6 interfaces for arbitrary instruction semantics, stores,
virtual register files and worlds. The earlier concrete csem function-entry
return/halt/stuck/divergence witnesses remain unchanged.

StockConfig.allocateAt, StockComparison and StockTest now use this actual
per-successor adapter; the old artificial per-successor rejection is removed
from these development harnesses. Original runtime, allocation and theorem
variants remain. Production lowering is still legacy, and development output
continues to say that its source proof migration is incomplete.

The executable-byte regression compiles distinct branch arguments, swapped
parameter pairs and a critical edge, then directly embeds the Lean encoder's
bytes in freestanding AArch64 executables. QEMU checks all branch outcomes and
zero, signed-boundary, byte-boundary and dirty-word inputs against the original
arithmetic specification. It repeats for real regalloc2 and an unavailable
oracle forcing the checked fallback. Actual requests assert different vectors
for each successor; native diagnostic checks additionally establish that the
real oracle passed both checkers and emitReady rather than silently falling back.

Fresh full comparisons inventory all1,302 official filetests with original
settings/identities, no source modifications or byte normalization:

- Production legacy:671 exact matches,939 different artifacts,2,413 unsupported.
- Indexed Stock development:1,202 exact matches,408 different artifacts,2,413
  unsupported. Every671 production exact match is retained,531 are gained, no
  new rejection. All1,202 matches from the saved full Stock development report
  are also retained, with0 gains/losses/new rejections relative to that report.
- Both measurements finish with exit10 because global artifact equivalence is
  false; runtests/throw.clif retains its nonrepeatable reference-stage gap.
- The delta tool's saved-development comparison exits1 solely because its
  checkpoint predicate requires at least one gained match. Its loss/rejection
  lists are empty; this is preservation evidence, not a new-improvement claim.

The comparison setup reused the existing saved pinned upstream mirror whose
instrumentation passes the exact checked patch; the primary upstream's earlier
instrumentation and all saved source were preserved. The canonical upstream
symlink now names that mirror, recorded with the previous link in the environment
receipt. The exporter uses the existing canonical Rust target through a symlink,
not a separate build cache or new source worktree.

Still required: universal semantic preservation/completeness of the new actual
preparation and fallback, including all call/try/terminator-result cases; source,
block and whole-driver simulation/completeness for every original rule/effect/
trap/sinking case; machine/bytes/compiler/linker/generated-proof consumers;
production cutover under original inputs/theorems; final audits/gates/comparison.
Success-conditioned allocation soundness and these witnesses do not discharge
those universal obligations. Full#140 remains active/incomplete.
