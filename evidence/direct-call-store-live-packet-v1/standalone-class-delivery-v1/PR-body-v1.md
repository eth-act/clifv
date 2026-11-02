A caller must retain its pointer when a direct call returns a value in x0. This class stores that returned value through the original pointer, then returns it. The actual allocator preserves the pointer in x19.

The new proofs cover these cases:

- Returned calls preserve arbitrary callee memory effects.
- The source store and paired machine run use the actual returned value.
- A default-flag store fault reaches the actual checked machine fault site under the original MapFaults condition.
- Both cleanup modes derive instruction shapes internally.
- The provider selects the proved Stock artifact and preserves complete predecessor retry.

The patch adds 27 modules and one audit. It changes no shared file or route index. The original caller/callee bytes remain exact. It adds no heap admission guard or caller execution certificate.

Validation: 1,097 published import hashes, 27 current normal module keys, and 46 exact audit roots. The audit includes 39 standard roots and seven marked fixed witnesses. All earlier 31/45 axiom sets remain exact. Two baseline artifacts use verified source/config/dependency-key reuse. No broad provider was rebuilt.

One QUICK, DIRTY, CHEAP direct peer review, exact-head CI and tested/merged-tree equality remain merge gates. Generic callee machine/linked trap transfer, actual linked ARM execution, all CLI/generated-proof flows and default production integration continue. The full original #140 goal remains open.
