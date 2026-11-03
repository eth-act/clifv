worker-O will prepare an exact definition extraction for #140 in an isolated owned candidate.

The files are `FV/E2E/DeadCleanupExecGot.lean` and the new `FV/E2E/OutsideAvoids.lean`.
The declaration `E2E.DeadCleanupExecBytes.OutsideAvoids` retains its exact bytes, name, type, and fields.
The old file only adds the import and removes that declaration.
All theorem bodies remain unchanged.
Manifest: `f539e16aa33586281432d61a3dc2c37c115c8e2d9d637e07119db135258d9356`.

The candidate must preserve all 23 old headers and axiom sets.
Current source, configuration, normal, and consumer gates remain required.
The immutable broad package will not change.
Physical, atomic/provider, ELF, hardware, and production gates remain open.
This work does not hold independent pair-semantics work.
