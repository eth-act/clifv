The original captured mixed caller/callee now has a complete linked execution witness for arbitrary symbolic16-byte source data. The proof establishes actual ArmRet, all16 copied destination bytes, and all16 preserved source bytes in both cleanup modes. It adds no execution certificate or initial-heap acceptance guard.

This coherent packet includes the heap/entry/result adapters needed by that complete execution proof. All14 files match the checked source context. The unchanged audits pass62 roots (58 standard-only generic and four marked fixed roots). Native facts certify only fixed static image/compiler facts; source contents remain symbolic. All25 old binary headers and axiom sets remain exact in the same context.

Stacked on #890. Delivery requires its actual landed receipt, one QUICK, DIRTY, CHEAP direct peer review, exact-head CI, and tested/merged tree equality. Default production activation remains separate.
