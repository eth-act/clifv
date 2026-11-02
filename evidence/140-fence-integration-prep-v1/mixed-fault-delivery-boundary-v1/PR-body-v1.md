The complete mixed function needs machine proofs for its source outcomes. This change transfers its returns and traps to the allocated machine trace. It identifies the actual encoded load/store fault sites.

The unit proves these outcomes under the original source and machine conditions:

- Every source return preserves the ABI result and final memory.
- A division trap preserves its code and the machine error.
- A memory fault reaches the actual encoded instruction and trap-table site.
- Both cleanup modes compile the complete original function.
- The original i64 function preserves legalization identity.

The proofs retain arbitrary arguments, source memory, and divisor. They derive instruction shapes and allocation facts internally. They add no heap acceptance guard or caller execution certificate.

Validation requires the exact current-main context, 47 kernels and 94 audited roots. The audit includes 80 standard roots and 14 marked fixed witnesses. One QUICK, DIRTY, CHEAP direct peer review, exact-head CI and tested/merged-tree equality remain merge gates.

The fault-aware executable proof still needs the no-earlier-fault prefix. Source/peak consumers, generated proofs, default activation and atomic integration also continue separately. The full original #140 goal remains open.
