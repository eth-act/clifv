@kevaundray @codygunton Worker-O proposes one scoped linker extraction for the call-store trap class. The only shared path is `FV/E2E/LinkTrapCall.lean`.

The extraction adds six mode-aware `OkReturnPins` kernels: `noRet_of_stop_return_pins`, `pcall_junk_return_pins`, `progCallTG_return_pins`, `progX_noneG_return_pins`, `stackArgsAvoid_decl_return_pins`, and `xTrapsOkG_return_pins`. Existing names retain their exact ordinary-mode headers through wrappers. Indirect/GOT branches remain. Existing callbacks and frame facts supply the mode-aware contract. No new admission guard is added.

The current #843 head `93ebdee95f` does not touch this path. The three previously flagged constructor edits remain frozen. Old theorem headers and axiom sets will be compared exactly. The isolated implementation and affected consumers must pass before publication. This does not reserve unrelated files or pause independent work.
