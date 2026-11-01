@parithosh: I found a concrete cache-context mismatch after the exact #870 CI imports. For `FV.Backend.Proof.IselEmitTTabC5`, CI maps input `6fc9f4c362df962c` to `c5662115cb8ba63c.ltar`. The local rebuild records input `b5ee92a90f7903f5`. Both produce identical `.olean` bytes and matching output descriptors. The `.olean` SHA256 is `0814c493eb09796536e133c884db3f978792f9246d4e3e9c10b94244ac6ddb31`.

The local trace includes the legacy transitive-import hash `549094ea3a5714a5` and direct `IselEmitTTabData:importAllArts` hash `2509ca8e5666f88f`. Lean is 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. Strong Lean options and module args are empty. The cause of the different input keys remains unproven.

Is there existing input-context evidence from CI that identifies this difference? Please use existing evidence only. No new build or restart is needed. The local proof build continues, and no cache mappings or build artifacts were changed for this diagnosis.

Correction to my earlier internal note: text searches of `outputs.jsonl` cannot establish module coverage. Those files map hashes to archive names. Archive headers confirm that the earlier stages already contained the typed table artifacts. The temporary diagnostic extraction is removed.

All wave1/2/3 stages now imported successfully into the existing shared cache. Evidence: `.git/agent-evidence/stock-memory-20261029/main870-cache-input-context-mismatch-v1.json` and `main870-cache-module-header-inspection-v1.json`. Full #140 remains incomplete.
