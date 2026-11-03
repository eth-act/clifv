Source memory-fault proofs need to follow callee frames across program views. Add four generic transport lemmas for reachability and access-trap events. The proofs preserve the original frame, memory, and trapping flags.

Validation: the real repository auditor passes all four roots with `propext` and `Quot.sound`. The focused normal kernel passes with a 156-source context.

The full-program reachability simulation and production fault transfer remain open. These helpers add no compiler admission condition.
