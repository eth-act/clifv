# Per-successor preparation and allocation delivery

A Stock conditional branch can supply different parameter vectors to its successors. The comparison harness previously rejected multi-successor blocks carrying arguments. This batch preserves each successor vector through reachability filtering, critical-edge splitting, preparation, indexed allocation checking, spill fallback and lowering. Forward realization proofs compose the actual runtime checks. Split/loop/outer-preparation and actual allocation/control witnesses accompany the interfaces.

This is one coherent delivery unit in original #140. Production still uses the legacy driver. Whole-Stock original-input completeness, remaining semantic families/effects, source/block/whole-driver simulation and the final production cutover remain required. The existing theorem variants and original input conditions are preserved.

The delivery branch contains 52 runtime/proof modules and three Stock harness consumers, selected by import closure from recovery snapshot b74ffb957ef0026dae0771206058705d999fdafd onto published main032d576442e48aeb5de9062103c970d18b8d0739. No working-tree checkout or build cache was copied. The complete recovery snapshot preserves all other unpublished work.

Prior backlog-tree gates passed: full2522jobs, crate-proofs1171, runtime4672/0/0 with the same seven non-runnable cases, encoder1292identical/0different, both E2E1150accepted/0rejected with exact identity-stage parity, and1992normal roots preserving earlier required trust sets. Those receipts predate the latest published-upstream reconciliation; they are historical evidence, not exact-current-PR gate results.

Current-main coherent rebuild is running serially in the canonical worktree. Exact delivery-tree/current-main gates, trust review and CI must pass before this draft is marked ready or squash-merged. New call/sink scratch work is outside this PR and remains backed up separately. The current full-goal checklist is [stock-full-goal-current.md](stock-full-goal-current.md).
