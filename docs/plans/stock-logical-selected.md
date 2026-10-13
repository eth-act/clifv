# Actual selected logical-root receipts

Part of #140; follows #172 on fresh main4519c36.

1. Reuse pure matching and existing mapped-context invariants for AND/OR/XOR
   roots1412/1449/1516, preserving complete Stock state.
2. Derive the typed environment and actual RHS execution from a retained emitted
   record, source instruction and final selected rule ID. Reuse selected-record
   receipts and rule-ID uniqueness; derive width from existing source scope.
3. Inhabit all three cases using complete sparse-ID Stock runs and kernel-checked
   observations. Run Lean MCP, cumulative trust audits and repository gates.

No compiler behavior change. Actual helper case inversion and source/machine value
composition follow; other semantic families/effects, whole simulation/completeness
and production cutover remain under #140.
