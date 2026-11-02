The complete-file route adapter, checker and generated proof emitter now consume ABI-aware program contracts together. The route adapter retains the entire previous sequence. The checker uses the actual complete program and one return-pin context. Existing emitters remain available.

Validation: nine new files; 15 standard-only generic roots and four marked fixed roots. The actual emitter generated and kernel-checked 12 cases with 72 fixed audit roots. Cases include the original mixed caller/callee and prior identity, both cleanup modes, single/split layout, and per-entry/all-entry stack variants. Actual import sources match the checked context.

Stacked on #889. Delivery requires parent receipt, one QUICK, DIRTY, CHEAP direct peer review, exact-head CI and tested/merged tree equality. Production activation follows separately.
