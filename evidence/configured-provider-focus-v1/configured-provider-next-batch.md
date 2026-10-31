The official delivery result uses lean-backend with --stock-config, as recorded by delivery-official-vectors-v1/results.json and each compile command.
FVTest/Backend/Main.lean routes stock = none through compileFileMemoryCfgNIWhen, but stock = some c still uses compileFileWith. The official comparison therefore measures the legacy configured path, not the newly proved production providers.

Next implementation batch, after the captured class lands:
- Route the configured compiler through the same proved provider with the existing StockConfig.allocate callback.
- Preserve settings acceptance/rejection policy, configuration receipts, experimental annotations, original inputs and all successful stages.
- Preserve whole-file transactional fallback with the same allocator/settings.
- Add maintained configured-mode tests for actual provider selection and bytes, both cleanup modes, and retained classes.
- Rerun the complete official comparison and audit each previously exact identity. Investigate losses; do not redefine the denominator or mask them with input changes.
- Check whether configured allocation needs the default compiler's CraneliftInput.shape adapter, based on actual allocator requests. Do not change settings policy without evidence.

This remains part of the original compiler/consumer integration goal. The load/store helper drafts remain preserved for the following memory batch.

The maintained pre-fix test also shows a missing allocation adapter. The default caller uses allocRecordingNamed with CraneliftInput.shape. StockConfig.allocate calls Allocator.run directly. Consequently even the typed provider gets different allocator inputs between default and configured modes.

The implementation draft now adds StockConfig.allocateWith with an allocation callback. The old allocate signature remains as a wrapper using Allocator.run. The configured compiler passes its existing allocNone callback, which applies the checked shape adapter. StockConfig.configure, allocateAt, and settings policy remain unchanged. The typed path still selects its existing lowering provider through the disabled new-route guard.

The maintained test draft now also binds the actual allocator request to the lowering diagnostic. In plain mode, the diagnostic must select the exact raw Stock output. Equality between default and configured outputs alone cannot pass this check through a shared provider regression. This draft passed Python syntax checking; execution after integration remains pending.

The compiler draft resets per-function rejection records before each whole-file allocation attempt. A successful fallback therefore cannot retain an abandoned attempt's setting rejection. The legacy StockConfig.allocate wrapper keeps its original accumulated-effect behavior. The four-path integration patch applies cleanly to the frozen captured candidate without modifying it. Lean build and runtime verification remain pending after the current packets land.

Focused validation now passes: both changed modules type-check, and all eight configured cases pass through Lean's interpreter against the existing native baseline. The memory classes bind to exact raw Stock output in plain mode. The retained class preserves its existing provider output; the initial draft incorrectly imposed raw Stock equality on that older provider. The failed test attempt remains preserved. The v2 integration patch applies cleanly. Native compilation and the complete official comparison remain required after integration. Receipt: configured-provider-focus-receipt-v1.json.
