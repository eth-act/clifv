Unwind handlers can reach memory faults outside ordinary source reachability. Add internal contracts over actual unwind states and preserve handler tables, post-unwind memory, and all five existing trap clauses. The old admission embeds unchanged. Actual `MemTrapAt` events cover ordinary and atomic accesses.

Validation: 177 proper normal modules, focused kernels, eight standard-axiom roots through the repository auditor, and complete default-flag load/store witnesses. All 175 imported source files match current main. The old `UnwindStatement` remains byte-exact.

Production must still derive these internal instances. Actual caught-handler fault execution and executable first-fault transfer remain open under #140.
