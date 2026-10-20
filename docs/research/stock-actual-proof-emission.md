# Actual Stock image, stack and emitted-proof integration

Base: fd857be3 (#331). Additive packet for #140; original entrypoints and theorem variants remain unchanged.

`Link.ActualImageProof` derives static image and `BinOkWithResults` facts from successful actual-callback linking, retaining every existing writer guard. `ActualStackBound` reuses the original graph/budget algorithm with a data-only callback input, and proves both legacy-mode compatibility equations. `ActualChunkCheck` and the new emitter connect actual artifacts to sliced checks, whole-program correctness, binary checks and global/per-entry stack bounds.

The actual Stock two-block prologue witness retains different diagnostic history from legacy. The linked fixture exercises strict/fallback modes, both cleanup modes, nonzero source/oracle indices, two-function programs and 33-function slicing. It is a fixed integration witness, not a universal production selector or a new enabled class.

Targeted verification: final fixture module build passed 688 jobs; public audit passed 39 roots (33 standard-only compiler roots, six explicitly marked fixed native witnesses); all 116 owned compiler/emitter constants use only standard axioms. Six linked fixture cases and all twelve emitted Lean files passed after fixing generated import ordering. Evidence: `/tmp/stock-actual-linked-proper-check`, `/tmp/stock-proof-emission-owned-constants.log`, and `/tmp/stock-proof-emission-qualified-axioms.log`.

Per-PR full module/E2E/link/trust gates follow on this committed source. Next: actual binary execution adapters, actual CLI consumers and universal prologue production activation with transactional legacy fallback. All remaining original #140 obligations stay open.
