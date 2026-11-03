The linked source proof now preserves reachability for every continuing state. The old `runLoop_linkR` theorem remains an exact projection.

The new transport derives linked and callee `MapFaults` from the original full-source mapping. Direct and indirect entry proofs use actual lookups, ABI checks and `enterFunc` outcomes. Source memory, caller frames and all old source conditions remain.

Validation: 372 current normal modules, three source kernels and four direct consumers passed. The real repository auditor passed 41 standard roots. All 30 old theorem headers and axiom sets remain exact. The gate used main `9a3f25fb`; all 372 source/configuration inputs have an exact projection bridge to publication base `40b0222a`. The only intervening changes affect the two native i128 files outside this closure. Peak memory was 646,537,216 bytes, with no OOM.

The 1,095 wider reverse importers remain a broad validation obligation. Complete recursive fault simulation, executable first-fault ordering and production activation remain open under #140.
