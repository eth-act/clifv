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
