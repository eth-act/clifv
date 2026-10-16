# Actual source execution reachability

The original full #140 goal remains active; production uses the legacy driver.

Actual Stock source destinations resolve to the same first matching block as Clif.enterBlock. Actual Clif.initState/enterFunc, every successful Clif.step and every finite prefix of that unchanged step relation derive reachable original frame locations for active and suspended frames. This covers arbitrary ordinary effects, direct/indirect program and extern calls, returns, tail calls, jump/brif/brTable, and both normal TryCall forms. Actual executing source calls now derive source position, node, scan, record and emitted Step internally; executed direct/GOT calls derive SigStackOk at actual returned area, without global CallsStack or caller reachability/emission certificates. Pending original TryCall tables and actual catchIn handlers have location proofs; full suspended-table/runX composition remains open.

Ten modules compile with 38 new public roots and four ghost definitions using only standard axioms. The 344-root/model/definition normal audit preserves all 302 earlier exact sets. All previous scratch source/object and recorded log hashes and the canonical 2,246-source/script freeze are verified.

Complete original-condition ordinary/sret direct, indirect and GOT compiler pipelines now exercise the NEW executing-call bridge from real source entry. Their real `Clif.runWith` runs finish successfully. Original-condition control witnesses execute all three branch forms and both normal TryCall forms. Tagged/default direct/indirect TryCall witnesses execute actual `stepX` and complete `Clif.runWithX` runs; local caught-frame proofs derive the handler internally. Separate real nested-program call/return witnesses and a raw tail-call helper witness exercise stored callers and actual callee entry. The raw tail witness does not expand the original compiler's accepted scope.

The generic `runX` invariant for stored TryCall tables and unwinding remains open. These reachability proofs do not prove Stock's full value/world simulation or completeness. Production cutover, exact current-PR/full validation, one bundled MCP and the fresh complete comparison remain mandatory.

[Hashed source, kernel, witness, audit and remaining-obligation evidence](stock-source-execution-scratch.json).

1. Preserve same live canonical1930build/source+script freeze; inspect terminal2182audit receipt and review every changed upstream dependency set. No timeout-based restart.
2. Prove generic XState stored-table correspondence and actual raiseIn/unwindFrom/liftStep/stepX prefix invariant; then connect actual normal AND exceptional source executions to Stock call/handler/control coverage.
3. Integrate76validated modules beyond existing110coherent modules, add only actual affected builds; ONE expanded337root MCP, complete public/kernel/transitive audits, full exact-current-PR/build/crates/runtime/encoder/BOTH E2E identity-stage gates before ready/squash#246 then#247.
4. Finish every original family/effect/Try/world/DFG/source/block/whole-driver value simulation AND completeness, original-input availability/visitor/static/checker/fallback/physical readiness/totality, and complete remaining witnesses.
5. Switch actual compiler/checker/linker/generated-proof consumers only when all original proof and acceptance parity obligations hold; final fresh complete stock comparison must retain at least#179.
