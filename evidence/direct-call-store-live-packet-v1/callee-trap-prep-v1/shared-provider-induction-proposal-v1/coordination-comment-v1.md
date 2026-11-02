@kevaundray @codygunton The scoped `LinkTrapCallInd.lean` extraction also factors the existing `thmT_of` body into `thmT_of_provider`.

The new kernel uses the existing mode-aware return callbacks and an internally derived static artifact provider. The old `thmT_of` header remains exact. Its wrapper derives the previous cleanup provider. Direct, indirect, GOT, depth, stack and program cases remain. The shared file needs this small kernel because a new module cannot reuse the old `L.Ok`-specific proof.

The added imports have no cycle. All 60 old linker headers and axiom sets remain required. The real auditor passed the prior 81-root extraction checkpoint. This explicit-callee-trap transfer does not close the separate `MapFaults`/`TrapAtF` obligation. No frozen constructor, CLI, selector or accepted-input change is included.
