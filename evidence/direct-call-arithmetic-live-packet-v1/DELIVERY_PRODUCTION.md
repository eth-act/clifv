# Live parameters across direct calls

The staged production compiler now selects the proved arithmetic class.
The original caller calls its callee, adds the live parameter to the result, and returns the sum.
The callee changes x0 and returns its argument plus 13.
The actual allocator saves the live parameter in x19 in both cleanup modes.
The source and ARM theorems prove the result `(word + 13) + word` for every word.
The generic class keeps arbitrary callee memory effects and the original source premises.

The packet adds one admission profile and thin instances of the existing consumer kernels.
It keeps the complete previous file action and the original allocation callback.
It prepends one linker action and keeps the complete previous linker action unchanged.
It preserves the old checker definitions, rejection interfaces, route indices, and shared proof emitter.
It keeps typed, optimizer, cleanup, unverified, tail-call, and unwind branches.

The staged context uses main d4ba42c101ab318b7e49b7a048fe749d121a52bc.
It also includes the canonical PR892 providers and the immutable result-call predecessor packet.
The constructor boundary remains unresolved.
This result is not current-main publication validation.
The three frozen constructor hashes remain unchanged.

Validation passed:

- All 119 affected modules passed native Lake checks with one job and a 2 GiB cap.
- Three additional provider/facade modules passed focused native checks.
- Both cleanup modes passed all three actual CLIs on the original pair and its distinct float variant.
- All four generated proof files compiled, with 36 audited roots.
- The linked ARM proof establishes ArmRet and the symbolic sum in x0.
- All 381 old headers and 182 old axiom sets remain exact.
- The consumer audit passed 252 standard roots and 15 marked fixed roots.
- The five additional checker/constructor roots use only standard axioms.
- Peak memory was 828,391,424 bytes. All OOM counters stayed zero.

The immutable sources are in `reviewed-live-production-v1/manifest.json`.
The complete source/config/dependency context is in `reviewed-live-production-v1/full-context.json`.
The receipt is `live-production-complete-state-v1.json`.
The input, allocation, generated source, object, and ELF hashes are in `live-production-original-inputs-v1.json`.
All failed diagnostics remain available.
The output manifest records 19,359 files before cleanup.

Publication still needs the constructor boundary and the required current-main delivery gates.
Memory consumption, multiple calls, stack arguments, and the full original #140 goal remain incomplete.
