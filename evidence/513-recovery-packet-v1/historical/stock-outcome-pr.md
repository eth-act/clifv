Proof-only additions to `LowerSim` currently invalidate generated interpreter/totality proofs and large fixed Stock witnesses. This extracts the unchanged VCode outcome interface and two frame-value lemmas into stable providers. Preparation/E2E statements and199 Stock witness files import what they use; E2E composition retains its explicit simulation import, and ABI read-only realization explicitly imports its load-value lemma.

All366 existing public theorem headers and every import-only consumer body are unchanged. Moved lemma bodies, elaborated types and required axiom sets are exact. `LowerSim` re-exports every old name. The original ABI/sret/atomic simulation proof bodies are unchanged.

Static future `LowerSim` reverse closure shrinks from1202 to804modules (398removed; this is not a measured wall-clock speedup). `IselShpTotal`, `DefGenWrap` and `IselPrgTryLast` no longer depend on it. The boundary and the additional missing ABI import were coordinated on #140.

Validation: full affected normal/trust/tool/E2E/actual generated-consumer gates are still running/pending; no merge until author gates pass. An overbroad library replay also started an uncached, unchanged optimizer proof; its healthy worker is preserved and its partial observation stays separate from this packet’s affected gates. Exact completed gate lines will replace this paragraph before merge.

Part of #140; does not close its remaining production/completeness obligations. The complete mixed-prefix/final-division implementation is independently backed up and under normal pipeline validation.
