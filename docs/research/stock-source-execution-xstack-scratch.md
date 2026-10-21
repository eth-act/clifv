# Saved-caller exception execution checkpoint

Four scratch modules and nine public roots pass normal kernel checks under8GiB. The12-root/model transitive audit uses only standard axioms. Actual `Clif.step` always retains, pushes or pops one caller; `liftStep` preserves aligned saved exception tables. Actual `raiseIn` and `unwindFrom` preserve the invariant when resuming a caught caller, even after discarding multiple frames. Ordinary entry establishes alignment internally.

Complete nested program-call witnesses throw at a leaf, skip a plain caller and catch in the lower TryCall caller. Both tagged and default handlers bind payload42 at fresh value10, enter the real handler and return42 in complete `runWithX` executions. The actual TryCall push exercises the new normal-step stack-shape and lifted invariant.

The source-specific pending-table/location specialization and generic `stepX`/prefix composition remain required. These generic helper premises are internal composition obligations, not new accepted-program conditions. No full Stock value/world simulation or completeness is claimed. Production remains legacy and original#140 remains active. The canonical2,246source/script freeze and live delivery worker were independently verified. No shared build-cache writes occurred; the temporary five-object input snapshot is archived and removed at batch completion.

[Hashed sources, objects, kernel logs, axiom sets, witnesses and remaining checklist](stock-source-execution-xstack-scratch.json).
