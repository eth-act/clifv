# Conditional entry with ranked scalar tails

Implementation checkpoint on merged #635 (91c809f7). Extends wide entry-parameter conditional control to arbitrary ranked scalar jump/return tails, inherited values, nonempty single-successor copies and joins, preserving first and later traps. The unchanged Scalar.Domain is derived from original source checks. Compiler/checker/linker/generated consumers append route10 and retain routes0–9 plus the complete previous conditional pipeline on failure. Old forward-return/trap variants and headers remain.

Preflight (dirty implementation based on91c809f7, not final frozen-source gates): maintained core/consumer build2478/2478; native tools4976jobs; focused21roots,20standard-only and one fixed checked-driver witness carrying one permitted generated original-input-check fact. General roots use only standard axioms. Runtime100graphs across six ABIs, both allocators and cleanup modes, retry/disabled/mixed fallback and missing-allocator control pass. Actual machine-byte execution:24000 against3000Cranelift references,0failures/0disagreements. Complete source/domain/ABI-entry-return witnesses cover both branch choices.

Evidence: /tmp/stock-conditional-forward-cfg-core-gates-v3, focused-inventory-v1.json, runtime-preflight-v1/receipt.json and native-preflight-v1.log (common /tmp/stock-conditional-forward-cfg- prefix). Historical failed proper-module builds remain retained.

Next: freeze/push this source checkpoint, run current normal/trust/header/old-axiom parity, full linked/generated integration and retained classes, runtime/encoder/identity-stage/examples/actual-crate and paired actual-output binding. Publish terminal evidence, squash only after current author gates. No final validation or agreement improvement claimed. Full original #140 remains open: broader conditions/per-edge/loops/effects/calls and whole-driver/completeness.

## Terminal author validation

All current author gates pass on7170a146. PR #636 publishes default route10 with complete prior fallback; [terminal evidence](stock-conditional-forward-cfg-production.md) records the full validation, exact old axioms/headers, actual native execution and same-input900→900comparison. No full140 completion or agreement gain. Continue the separately preserved general parameter-conditional graph source/domain work, then broader conditions/per-edge/loops/effects/calls/full-domain obligations.
