# Universal root810 boundary

The fixed-function checkpoint does not prove arbitrary root810 contexts.
The root is rule_lower_1272, with actual rule ID810.
Its matcher selects uextend of a sinkable atomic load with little/native flags.
Its output type satisfies fits_in_64.
Its RHS calls sink_atomic_load564 and then load_acquire422.

The universal proof must derive these facts from the actual matcher and evaluator:

1. The bound producer is the original mapped atomic load.
2. The producer has exactly one demanded use and a positive source color.
3. The actual sink update retains the producer identity and changes only its sunk bit and ordering color.
4. The emitted acquire binds the consumer result through actual aliases.
5. The scan's deferred-effect relation preserves every source memory effect and fault.
6. The original color interval contains no intervening ordering effect.
7. The single-use fact excludes an earlier source use of the deferred result.
8. The actual source read or first fault corresponds to the deferred acquire at the consumer.

Existing reusable facts include stock_sink_resultful,stock_sink_iflet,stock_loadSink_call,
stock_loadSink_binding,stock_ctor_noSink and the sourceMetadata_projection theorem.
The new source-only body_color_count lemma states the exact number of colored steps.
Its companion derives a quiet interval from an unchanged actual metadata color.
These equalities must come from the real scan and metadata.
They are not new source acceptance conditions.

The source semantics permits ordinary memory faults.
The proof cannot assume a valid heap or a caller execution certificate.
The legacy uextend_atomic_load_ok nonmatch theorem does not apply to Stock.
Acquire ordering uses the existing single-thread memory model.
The proof must preserve all accepted source widths and flags.
The current fixed byte fixture remains unchanged.
