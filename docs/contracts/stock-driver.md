# Incremental Stock lowering

`Backend.lowerChecked` and the four strict/total, ordinary/cleanup E2E pipelines
use `Backend.Stock.D0.defaultLower`. Its input predicate currently selects six
structural forms: a single block numbered zero, one ordinary entry parameter
numbered zero, an empty body, and a return of that parameter, with matching i32 or
i64 signature and default, System V or fast calling convention. Symbol names and
run-command metadata are arbitrary. Other functions retain legacy lowering.

On a selected input the dispatcher runs the actual Stock driver. It compacts
Stock's reserved virtual-register prefix and restores the source symbol name.
It accepts only empty successor-edge rows; a Stock error or nonempty row selects
legacy on the same input. Future classes with successor arguments must carry the
full edge-aware payload into preparation, rather than erase it.

`Backend.Stock.D0.normalized_eq_legacy` proves the
entire compacted result equals legacy code, including rules and metadata, for
every selected input. `defaultLower_eq_legacy` lifts this to every input without
adding caller premises. The equality is a fixed kernel-checked proof, not a
runtime output comparison or a per-program certificate. The runtime predicate
does not inspect fixture names or the legacy output.

For this first class the common allocation/checking/physical-lowering/emission
computation receives exactly the legacy code. Thus downstream errors, effects,
spill fallbacks and successes are the same computation; there is no distinct
downstream Stock attempt requiring a second allocator invocation. The
`Compiler.compileFileWith_eq_legacy` theorem covers arbitrary allocator monads,
answers, errors, settings, cleanup choices and mixed files. Classes producing
different prepared code will require transactional legacy retry for downstream
failures before activation.

Existing E2E and linker theorem statements remain intact. The source witness
covers arbitrary values, including dirty upper bits, memory and oracle streams.
`complete_pipeline_witness` binds both actual total pipeline artifacts to the
successful Stock result for arbitrary allocator answers. Fallback witnesses cover
forced Stock errors and nonempty edge payloads on inhabited inputs. Run the
production parser/routing/mixed-file regression with:

```
FV_MEMCAP=8G scripts/memcap.sh lake env lean --run FVTest/Backend/Lowering/StockD0Runtime.lean
```

This class does not complete #140. Pure operations, CFGs/loops, effects, calls,
exceptions, original-domain Stock simulation and Stock-only completeness remain
required before fallback retirement. The source class and its proof consumers
must grow together under `docs/plans/stock-driver-incremental-delivery.md`.
