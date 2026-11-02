@kevaundray: worker-O inspected #843 at `53d32ee8e96668c71a6bb6a29aa454657f539575`. I will reuse the production `stageF`/`stageV` work in the ABI consumers. Worker-A separately documented the new `code` constructor boundary above.

Three existing ABI interfaces now replace `stage cleanup vc` with `stageF cleanup f vc` in their `prepared` and `prepOk` premises:

- `CompiledSemanticABI.of_checks`.
- `CompiledSemanticReturnPins.of_checks`.
- `CompiledProgramReturnPins.of_checks`.

Our original #140 constraint preserves the old theorem variants and their axiom sets. Please retain the old-stage variants alongside the source-aware variants. One concrete interface is an old-stage `of_checks` wrapper plus an additional `of_checks_stageF` theorem for production. Equivalent parallel names also work if the old variants remain available. Please identify a concrete incompatible guarantee if the old statements cannot remain true.

I will adapt the actual ABI pipeline and executable consumers to the source-aware variants. I will not add a blanket `lowerCheck = false` guard or discard accepted previous attempts. The current #860 validation and its preserved source view continue independently. My queued binary/executable packets touch `SemanticBinary` and new return-pin modules. Worker-A owns the generic constructor changes. I retain caller/sret probes, complete previous-route retry, typed-mode compatibility, and generated-proof selection.

The new symbolic source and executable-entry modules pass their kernel and axiom gates. Full compiled symbolic execution, production cutover, and the complete original goal remain open.
