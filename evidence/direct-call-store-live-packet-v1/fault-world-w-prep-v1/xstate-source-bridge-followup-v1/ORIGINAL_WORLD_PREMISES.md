The old unwind theorem does not admit the new handler fault case.

`backend_correct_world_ni_cleanupU` in `FV/E2E/WorldUnwindNI.lean:72` requires `TrapsExplicitX` at line99. Its statement clause permits explicit trap instructions only. An ordinary load/store fault contradicts that clause. The old theorem remains valid and unchanged.

`XRaiseOk` in `FV/Backend/Proof/LowerSimURaise.lean:57` relates the returned source memory to the world after an unwind. It does not mention an ARM permission map. `RelW` in `FV/E2E/LinkWorld.lean:67` adds stack-pointer and error facts to the memory relation. It does not require invalid CLIF addresses to be unmapped.

`MapRelRW` in `FV/E2E/DeadCleanupExecMemFault.lean:650` requires writable entry allocations and readable code. It permits an all-read-write map. It cannot establish an unmapped byte for an invalid source access.

Ordinary `MapFaults` follows ordinary source reachability. `XEnv.toEnv` converts an unwinding extern result to a stuck outcome. An unwind handler can therefore contain a later memory fault outside ordinary reachability. This is a semantic counterexample pattern. It is not yet a complete Lean counterexample.

The new source module prepares an internal instance for the old explicit-only branch. That proof excludes memory events by the existing premise. It does not establish handler memory coverage. The broader handler case needs a separate production derivation. No public input or acceptance rule changed.
