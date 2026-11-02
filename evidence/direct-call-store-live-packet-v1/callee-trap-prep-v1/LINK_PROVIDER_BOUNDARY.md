# Additive linked trap provider

The source, virtual, stage, and world-machine callee proofs now pass.
The world theorem preserves the existing TrapsExplicitC and XTrapsOk contracts.
It needs no lowerCheckU or legacy-output guard.
The fault-aware world variant remains separate and preserves MapFaults.

The linked proof still has two legacy restrictions:

- LinkSys.Ok.compiled requires CompiledEither.
- LinkSys.TrapsOk.cleanup and lowerU require CompiledCleanup and lowerCheckU.

Neither restriction follows from the actual new Stock artifact.
An additional source guard cannot solve this mismatch.

The existing OkReturnPins contract already preserves all original static conditions.
Its compilation field admits the semantic artifact families.
The new kernel should retain that static contract and accept a proved trap provider.
The provider must expose the existing world stopping guarantee.
It must preserve the source run, XCallsOk, XCallsIndOk, XTrapsOk, entry, memory, and symbol premises.
Its result must include the real trace, stopping SP, program, and callee-trap state.
The provider is an internal theorem contract.
The artifact constructor and checker must derive it.
It must not become a caller execution certificate.

The kernel should reuse the existing return-pin callbacks and good-trace proofs.
The trap induction should accept the proved per-function provider.
The old trap theorems should remain exact wrappers around their old providers.
Their public headers, axiom sets, and accepted inputs must stay exact.
The kernel must retain depth and peak variants.
It must retain every indirect and GOT branch in the existing linked proof.

The following shared interfaces need coordination before edits:

- FV/E2E/LinkTrapCall.lean: static hook facts and the trapping-callee contract.
- FV/E2E/LinkTrapCallInd.lean: the call handoff and the provider-driven induction.
- FV/E2E/LinkReturnPinContract.lean: a shared static projection only if the existing record needs one.

The existing WorldTrapStop adapter provides the required SP and program facts.
No copied world-machine proof is needed.
The remaining provider inventory is remaining-link-trap-providers-inventory-v1.json.
No build or shared edit is authorized by this note.

The three #843 constructor files remain unchanged.
Their separate additive callStore case remains required for production admission.
The fixed original caller/callee, actual float variant, all three CLIs, generated proofs,
and linked ARM executions remain mandatory.
