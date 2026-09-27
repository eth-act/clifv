# M2: correctness of the DSL → CLIF emitter (`FV/Compile/Proof`)

## Status (kept current for resumption)

Work in progress (agent `M2Proof`). Nothing below is claimed until it is listed as proven.

### Changes made to the emitter / semantics (all regression scripts re-run after each)

1. `Clif.enterFunc` (FV/Clif/Run.lean): a frame with stack slots whose allocation does not fit
   below `2^64` (`Mem.fits`) traps `stk_ovf` (resource exhaustion). Frames without slots are
   unchanged (the check is `f.slots.isEmpty || mem'.fits`; this also keeps the symbolic `rfl`
   proofs of `FVTest/Clif/StepExamples.lean` within the recursion limit).
   New helpers: `Clif.Res.trapUnless`, `Clif.Mem.fits` (FV/Clif/Mem.lean).
2. `Compile.writeEntries`/`newMapObj`/`setupCall` (FV/Compile/Model.lean): a map longer than
   `maxEntries` or an allocation that does not fit below `2^64` traps `Compile.oomTrap`
   (`user1`, the CLIF runtime's arena-exhaustion trap). Before, such runs silently wrapped
   addresses or got `stuck` on a later read, which made the unconditional M2 statement false
   (counterexample: a loop inserting `2^20 + 1` distinct keys).
3. `Compile.declare` (FV/Compile/Emit.lean): reuses a declaration only if name *and*
   signature match. Output unchanged on the corpus (every name has one signature).

### Plan / proof map

See the sections below (filled in as lemmas land).

### Proof files so far (all build, no `sorry`)

| File | Contents |
| --- | --- |
| `FV/Compile/Proof/Exec.lean` | `Reach` (eventual reachability, CPS-composable), `Reach.runLoop` (fuel monotonicity), `RegsHas`, `Agree`, `setMany` lemmas, single-step lemmas |
| `FV/Compile/Proof/Gen.lean` | `*_run` unfolding of generator primitives, `Lk`/`Good` (final function contains the generated code), `Bk` backward transfer algebra, `At` (machine at a generator position) |
| `FV/Compile/Proof/Rel.lean` | `Heap`, `Enc`, `hdl`, `vecOk`, `EnvRel`, `selHdl`, checker-state `alive`/`mutd` |
| `FV/Compile/Proof/Check.lean` | `ExprStep`/`StmtStep`: liveness effects of a successful check (`Expr/Exprs/Op/Stmt.chk_step`) |
| `FV/Compile/Proof/Bytes.lean` | little-endian byte round trips, `MemWF` (bump allocator), `Keeps`, load/store lemmas |
| `FV/Compile/Proof/Heap.lean` | `ObjAt`, `MemModels`, `readEntries`/`writeEntries_spec`/`newMapObj_spec` |
