# Preserve a live pointer across a direct call and store its result

The new class keeps the original pointer across a direct call.
It stores the returned word at offset 8 with the default trapping flags.
It then returns that word.
The real allocator saves the pointer in x19.

The generic proofs preserve arbitrary callee memory effects.
They cover returned source executions, paired machine executions, and the actual first store fault.
The machine fault theorem keeps a callee trap as a separate alternative.
The fixed caller and callee preserve their original source bytes.
Their source runs cover both the returned outcome and the first store fault.
Both preparation modes derive their required access shapes internally.

The parameterized provider preserves complete retry and every earlier Stock output.
Its witness uses the complete landed predecessor.
That predecessor succeeds on the original caller.
The new provider selects a distinct Stock artifact.
The patch adds no route index or shared-file change.

Validation:

- All 27 new modules pass their focused kernel checks.
- The audit passes 46 roots: 39 standard roots and seven marked fixed witnesses.
- All earlier 31-root and 45-root axiom sets remain exact.
- The current-main bridge checks 1,124 sources against a685df2b.
- The complete normal-key check and the unchanged audit pass in that exact source projection.
- The only build configuration difference adds the weak -j1 scheduling option.
- The measured peak stays below 1 GiB within the 2 GiB allocation.
- Two missing baseline artifacts use verified copies from the fence prefix.
- Those copies preserve their full source closures, native keys, output keys, and .olean hashes.
- No broad provider was rebuilt.

Delivery uses standalone-class-canonical-v1 and its manifest.
The final receipt is standalone-class-state-v1.json.
The existing three constructor files remain untouched.

The following work remains part of the original goal:

- Generic callee-trap propagation through valueSemU, xrT, and the linked induction.
- Actual linked ARM execution of this class.
- The three CLI paths and generated proofs in both cleanup modes.
- The separate float-file variant and complete production activation.
- Every remaining original #140 obligation.
