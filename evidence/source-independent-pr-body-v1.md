The ABI-aware linked compiler now exposes original-source correctness and its peak-depth variant. Both theorem headers match the retained variants exactly. No source, heap, trace, helper, signature, expansion, slot, memory, depth or trap premise changes.

Validation: 22 support kernels plus focused witnesses; two standard-only generic roots and two marked fixed witness roots. Witnesses instantiate every source premise for arbitrary arguments in both cleanup modes. All actual import sources match the checked context.

Stacked on #888. Delivery requires its landed receipt, one QUICK, DIRTY, CHEAP direct peer review, exact-head CI and tested/merged tree equality.
