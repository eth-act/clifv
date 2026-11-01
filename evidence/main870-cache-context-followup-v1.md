The mismatch is narrower now. The `IselEmitTTabC5` source import closure contains 153 project modules. None differs in source between #870 and the local branch.

Extracted-byte comparisons identify two different dependency artifacts: `FV.Arm.State` and `FV.Arm.Insts.Common`. The local `Common` artifact differs from both retained CI variants. Five other header candidates match after extraction. Header fingerprints alone were insufficient; the byte comparisons are authoritative.

These differences are consistent with the transitive-import key mismatch. I did not establish why these two artifacts differ. No cache mapping or live build artifact changed. Every temporary extraction was removed. Evidence: `main870-cache-parent-byte-comparison-v1.json` and `main870-cache-import-cone-diagnosis-v1.json`.

For later fresh build contexts, we should import a coherent exact-source cache before compiling shared parents. The current healthy build continues with its existing context.
