# General CFG composition checkpoint

PR #633 (`ac302a8a`) activates three-block scalar chains in all production
consumers. This checkpoint extends the internal composition machinery; it does
not activate another production class or complete #140.

`StockCfgTraversalScans` derives retained scan order and uniqueness from the
actual driver, and connects two original cores through the actual intervening
fold, including synthetic nodes. `StockCfgTraversalDemand` proves demand
monotonicity for outgoing arguments, every instruction decision, complete scans,
block cores, original/edge nodes and arbitrary traversal segments. Successor
scan demands reach a later predecessor's terminator without adjacency or a
fixed block count. The label-based variant derives the traversal split from
actual bounds and strict label order. Retained input/output demands also survive
to the returned final state. These results impose no instruction-family premise.

Validation on 2026-10-26: all 1,101 targeted module keys pass; the combined
`scripts/audit/stock-cfg-traversal.lean` audit passes all 22 roots. All 17 generic
roots and both critical-edge witnesses use only the standard three axioms. The
three chain witnesses retain the existing, explicitly labelled fixed-input
dominance native fact. MCP checks of the label-based transfer and nonempty-gap
witness report the same sets and no source warnings. Actual witnesses include a
nonempty middle-block traversal and a four-node run with synthetic critical
edges. Existing proof modules and consumer interfaces remain unchanged.

The next checkpoint derives topological order from a strict original source
rank through the actual fuel-bounded DFS, including unreachable nodes and shared
joins. Source-table edges and row sizes are connected to original terminators.
The resulting original-node labels retain source-edge order through critical
node insertion, and directly instantiate the generic demand transfer. Plain
source jumps are proved to select original targets directly, even with other
blocks' critical nodes. An actual conditional compilation crosses both a
middle block and a synthetic node with nonempty arguments; its witness is
kernel-only. All 1,064 combined targeted keys and all 12 additional forward
audit roots pass, using only the standard three axioms. The earlier 22-root
audit remains separate.

Next: compose arbitrary chain/acyclic scalar return and first-trap simulation; reuse existing jump continuations and per-edge
preparation/copy proofs. Then activate the larger class in every consumer and
run the full per-PR gates. Strict label order is now derived for source-ranked acyclic edges; arbitrary
cyclic CFGs are not covered. Backedges need SSA/dominance
and carried-value reasoning beyond this forward-demand result. General branches,
loops, effects/calls and original-domain simulation/completeness remain open.

Source ownership: `agent/stock-general-cfg-20261026`, existing
`.worktrees/stock-cfg-source-20261025`, one shared warm Lean cache, no agents or
additional worktrees. Source checkpoints are pushed for recovery; no proof-only
PR is intended. Keep the exact PR #633 parent executable and captured inputs for
the next production comparison. Preserve unpublished sources and prior evidence.
