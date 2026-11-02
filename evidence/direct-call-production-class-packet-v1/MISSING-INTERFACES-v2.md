# Direct result-call interfaces

Reviewed base: main `3b586e45bb65855c9e6c0640f3e9f5f75abd4446`.
Reviewed production proposal: #892 at `36dd36a6c1746acb1741dd5c984b0ead1b8a2d18`.
These identifiers describe inspection. They reserve no shared file or route index.

## Complete class unit

1. `StockResultCallCheck` checks the original one-call source, retained records, final aliases, argument pins, and x0 result pins.
2. `StockResultCallLayout` derives its internal facts from those checks.
3. `StockResultCallSource` derives the callback result and exact returned memory from the original source run.
4. The accepted `StockDirectCallResult` adapter binds that source result to the final virtual definition and physical fixed register.
5. A new return-function proof must compose the actual entry prelude, call, virtual definition, and return.
6. A new NI proof must retain the original `XCallsOk`, `XCallsIndOk`, `XNI`, `ActEntry`, source-trap, and stack conditions.
7. A provider must retain complete retry and preserve exact previous Stock artifacts. An execution witness must cover actual caller/callee code and arbitrary arguments.

The eleven class modules now contain a draft complete function Domain and machine variants.
Every class module remains unverified. No complete class result is claimed yet.
The callback memory remains arbitrary. No no-heap, no-calls, source certificate, or execution certificate enters the interface.

## Exact missing semantic interface

The proposed additive path uses O’s existing ABI contract.
It needs no edit to `SemanticNI.check` or `CompiledSemantic`.
A retains ownership of CodeDomain, arguments, control flow, and loops.

After the complete function proof passes, O must coordinate these shared edits:

- Add `Stock.ResultCall.check` as the last alternative in `Backend.SemanticABI.checkCalls`.
- Add its matching branch in `returnPinCallsExtra` and retain the exact old alternatives.
- Add a result-call constructor to `CompiledSemanticABI` and `CompiledSemanticReturnPins`.
- Give those constructors the complete raw/cleanup machine contract from the new function Domain.
- Extend their check constructors and eliminators without changing existing constructor statements.
- Reuse the existing binary, executable, linker, and generated-proof contracts through that extended artifact contract.

The new branch uses `ReturnABI`. A normal explicit i64 result selects x0.
`ReturnPinMode.checked` keeps the existing SemanticNI priority.
A previously accepted artifact still takes its old compatible constructor.
The new class must not require `lowerCheck = false`.
That priority preserves compatible stageF artifacts and their original guarantees.

## Provider and consumer boundary

The current main includes `Stock.ParameterArgsCfg.NI` as raw route22.
The published892 CLI proposal still uses the VoidCall provider as its chain head.
A owns the later argument/control chain-head update.

`Stock.ResultCall.lowerWithPrevious` therefore accepts the complete previous provider as a parameter.
It changes no shared chain head or raw index.
O and A must agree on the exact predecessor before wiring the new class.
The new route must append after the actual retained list without renumbering any old route.

The whole-file mode adapter must keep its actual-artifact preflight and complete previous-file retry.
Typed programs outside the ABI admission rule must retain their matching previous objects and theorem emitter.
This follows the existing892 mode boundary. It is not a source-only float filter.

## Remaining proof join

The return-function proof must use the actual retained block chunk.
Its raw result mapping can differ from its final alias-resolved destination.
The checker records both forms and their exact resolution equality.
The call definition and final return must use the same destination and x0.

The existing `void_call_pair` discards callback outputs through `X.voidCalls`.
The new class must use the original `X` and preserve its explicit scalar result.
Its paired execution must derive equal result values through the original `XNI` contract.
No extra determinism premise or heap guard may replace that derivation.

## Actual provider reachability

The runtime probe confirmed that VoidCall.NI succeeds through the legacy fallback for the unchanged caller.
A previous-success-first wrapper cannot activate this class.
The corrected draft tries the checked new class first and retains complete previous-provider retry.
Its preservation theorem applies to exact previous Stock results.
Its acceptance theorem retains every accepted function, including legacy successes.
The same witness module includes an actual-predecessor selection theorem for published892’s VoidCall.NI head.
All revised proofs remain unverified. No shared interface changed.
