# M2: correctness of the DSL → CLIF emitter (`FV/Compile/Proof`)

## Status (kept current for resumption)

**In progress. `Compile.compile_correct` is NOT yet proven.** Everything listed as proven
below builds (`lake build FV.Compile.Proof`), contains no `sorry` and no `axiom`.
Branch `agent/m2proof`, worktree `/home/kev/work/clifv-wt/m2proof`.

| Layer | Status |
| --- | --- |
| Execution framework (`Reach`, fuel monotonicity) | proven |
| Generator structure (`Good`/`Lk`, `Bk` for every emitter function, `At`) | proven |
| Checker liveness effects (`Expr/Exprs/Op/Stmt.chk_step`) | proven |
| Byte-level memory, bump allocator (`MemWF`, `Keeps`) | proven |
| Map objects in memory (`MemModels`, `readEntries`, `writeEntries_spec`, `newMapObj_spec`) | proven |
| `mapEnv` extern specs (new, clone, contains, insert, get), `toWord` injectivity, `lookupL`/`upsertL` on encodings | proven |
| Control-flow primitives (`reach_selectVals`, `reach_errIf`, extern calls) | proven |
| **`expr_sim`: every `Expr` constructor (incl. `cond`, `clone`, `mapEmpty`, `mapContains`)** | **proven** |
| `exprs_sim` (call arguments) | not started (same pattern as `pair`) |
| `op_sim` (`iop` checks, `vget`/`selectElem`, `mapGet`) | not started; overflow lemmas prototyped (below) |
| `stmt_sim` (all statements, loop invariant, calls) | not started |
| function level (`compileBody`: entry, error block, block-id uniqueness) | not started |
| top level (`setupCall`, `decodeResult`), `compile_correct`, `FVTest/Compile/ProofExample.lean` | not started |

`#print axioms` (checked 2026-09-27):

```
Compile.Proof.expr_sim            [propext, Classical.choice, Quot.sound]
Compile.Proof.Stmt.chk_step       [propext, Classical.choice, Quot.sound]
Compile.Proof.Reach.runLoop       [propext, Quot.sound]
Compile.Proof.writeEntries_spec   [propext, Classical.choice, Quot.sound]
Corpus.sumChecked.denote_eq       [propext, Quot.sound]
```

The last line confirms PLAN.md M2 deliverable 2: `denote_eq` is generated automatically by the
M1 frontend (kernel `rfl`), with a clean axiom footprint.

Regression (after all changes below, 2026-09-27): `lake exe compile-diff` 107/107 vectors,
`onlySubsetE` 41/41; `scripts/clif-filetests.sh` pass 5706, fail 7 (the known i128 ones);
`scripts/diff-corpus.sh` ALL ENGINES AGREE (114/114, Rust runtime 22/22).

## Intended final statement (and why it differs from compile.md §6)

```lean
theorem Compile.compile_correct {σ τ} (f : DSL.FlatFn σ τ) (hf : f.checked)
    (hlink : Compile.linkOk f) (args : DSL.Args σ) :
    ∃ fuel₀, ∀ fuel ≥ fuel₀,
      Compile.runCompiled f args fuel = some (DSL.denote f args) ∨
      Compile.Exhausted (Compile.runOutcome f args fuel)
```

* **Resource exhaustion disjunct (CakeML style).** The unconditional compile.md statement is
  false: `readEntries` rejects maps longer than `maxEntries = 2^20` (a checked loop inserting
  `2^20 + 1` keys gets `stuck`), and the bump allocator never reuses addresses, so a checked
  program with `2^64`-iteration nested loops calling a buffer-mode function exhausts the
  64-bit address space (addresses then wrap). Semantic change 1 and 2 below turn every such run
  into a trap `stk_ovf` / `oomTrap` (= `user1`, the CLIF runtime's arena-exhaustion trap).
  `Exhausted o := ∃ c, o = .trapped c ∧ (c = .stkOvf ∨ c = oomTrap)` (`Compile.Proof.Exh`).
  The emitter emits no `trap` and no trapping access that can fail, so this disjunct only
  covers genuine resource exhaustion.
* **`linkOk` (mechanically checkable per program, `decide`).** Calls are resolved by name.
  Nothing in `FlatFn.checked` prevents two different callee bodies with the same name, or a
  callee named like a runtime extern; then the emitted program calls the wrong function. The
  frontend guarantees unique names, so every corpus program satisfies
  `linkOk f := (∀ c ∈ Stmt.callees f.body, (compile f).func? (mangle c.name) =
  some (compileBody c.name c.body)) ∧ ∀ n ∈ rtNames, (compile f).func? n = none`.
* No vector-size bound is needed: the exhaustion trap covers huge buffers.

## Proof architecture (implemented part)

* `Reach E P Q X s`: from `s` the machine reaches a state in `Q`, or ends with an outcome in
  `X` (here `Exh`). Lemmas are CPS-composable (`Reach.bind`); `Reach.runLoop` gives the
  `∃ fuel₀, ∀ fuel ≥ fuel₀` form.
* Generator positions: a simulation lemma for a generator action `m` from state `cg` assumes
  `Good F (m.run cg).2` (the final function `F` contains everything generated) and derives
  `Good`/`Lk` for earlier states with `Bk` (`terminate` turns `Lk` after into `Good` before,
  `switchTo` the converse). `At F cg fr`: the frame executes `F` at position `cg`.
* Values: `Enc H t x vs` (flat encoding; a map is an `i64` handle `h` with
  `H h = some (d, encEntries …)`), `hdl` (handles, not inside vectors), `EnvRel` over the
  variables alive in the checker state, `selHdl` (handles of selected variables).
* Memory: `MemModels m H` (well-formed bump memory, every object's header and entry array
  are distinct live allocations with the right words). Frame allocations (slots, result
  buffer) are `ObjFree`; `Grows H H' n` keeps them object-free as the heap grows.
* `expr_sim` (`SimE e`): from `XPre` (invariant, `EnvRel`, env ids below `nextVal`, `Γ` well
  formed, alive handles distinct) the code of `e` reaches the next position with the result
  values encoding `e.denote ρ` (`XPost`): heap only extended (`Ext`), result handles
  distinct, each fresh or owned by a variable `e` moved (the affine rule, `moved st st'`).

## Remaining work, precisely

1. `Prog` needs one more field `sub : s.mem.allocs ⊆ s'.mem.allocs` (the caller's
   allocations survive callee frames: callee slot bases are `≥` the caller's `next`), and
   `ErrAt` must carry `Grows`/`next`/`allocs` progress relative to the start state (needed by
   the caller after a callee error). Both are small edits of `Expr.lean`/`Prims.lean`.
2. `op_sim`: overflow checks. Proven in a scratch file, to be added to `Arith.lean`:
   `(a + b).ult a = uaddOverflow a b`, `a.ult b = usubOverflow a b`,
   `umulhi-extract a b != 0 = umulOverflow a b` (generic in the width, `omega` only).
   `vget`: induction over `selectElem`'s fold (invariant: accumulator holds element
   `if i < K then i else 0`); `mapGet`: `spec_get` + `readBits_writeBits` for the
   `notrap aligned` load (slot base `≡ 0 mod 16`); needs `SlotIdx F` (slot keys = indices,
   like `ExtIdx`) in `FnOK`.
3. `stmt_sim` by induction on `Stmt`, postcondition for a normal result: result handles
   distinct and each fresh or a handle of a variable alive at the start; objects of variables
   that are alive at the end and not updated (`mutd = false`) or frozen (`Check.frozen lim`)
   untouched and disjoint from the result; objects not reachable from alive variables
   untouched (needed for callees); heap domain only grows. Uses `StmtStep` (proven). Loop: induction on iterations with the
   header invariant. Calls: `fn_sim` of the callee body from the induction hypothesis.
4. Function level: `compileBody` block-id uniqueness (`F.block?` finds the generated block),
   entry block first, error block returns `(tag, zeros)`/zero stores; `enterFunc` slot
   allocation (`stk_ovf` or `SlotsOK`).
5. Top level: `setupCall`/`encodeArgs` give `Enc`/`MemModels` (or `oomTrap`), `decodeVal`
   inverts `Enc` for well-formed types, `readBuf` after the result stores; then
   `compile_correct` and `FVTest/Compile/ProofExample.lean`.
6. `notrap`/`aligned`: the emitter's only such flags are `slotFlags` loads (mapGet cell,
   buffer-mode results) and none elsewhere; their justification is part of 2–4 (a failing
   flag is `stuck`, which the simulation excludes). The CLIF runtime (`Runtime.text`) is
   trusted relative to `mapEnv` and differentially tested; its proof is not attempted.

## Changes made to the emitter / semantics

1. `Clif.enterFunc` (FV/Clif/Run.lean): a frame with stack slots whose allocation does not fit
   below `2^64` (`Mem.fits`) traps `stk_ovf`. Frames without slots are unchanged (the check is
   `f.slots.isEmpty || mem'.fits`; this also keeps the symbolic `rfl` proofs of
   `FVTest/Clif/StepExamples.lean` within the recursion limit). New helpers
   `Clif.Res.trapUnless`, `Clif.Mem.fits` (FV/Clif/Mem.lean). docs/contracts/clif.md should
   mention this (owner: integrator).
2. `Compile.writeEntries`/`newMapObj`/`setupCall` (FV/Compile/Model.lean): a map longer than
   `maxEntries` or an allocation that does not fit below `2^64` traps `Compile.oomTrap`
   (`user1`).
3. `Compile.declare` (FV/Compile/Emit.lean): reuses a declaration only if name *and* signature
   match. Output unchanged on the corpus.

## Proof files

| File | Contents |
| --- | --- |
| `Exec.lean` | `Reach`, `Reach.runLoop`, `RegsHas`, `Agree`, `setMany` lemmas, step lemmas |
| `Gen.lean` | generator `*_run` lemmas, `Lk`/`Good`, `Bk` algebra, `At` |
| `GenBk.lean` | `Bk` for every emitter function (`compileExpr`…`compileStmt`) |
| `RunEq.lean` | `compileExpr` run equations (all `rfl`) |
| `Rel.lean` | `Heap`, `Enc`, `hdl`, `vecOk`, `EnvRel`, `selHdl`, `alive`/`mutd` |
| `Check.lean` | `ExprStep`/`StmtStep`, `*.chk_step` |
| `Bytes.lean` | byte round trips, `MemWF`, `Keeps`, load/store |
| `Heap.lean` | `ObjAt`, `MemModels`, `readEntries`, `writeEntries_spec`, `newMapObj_spec` |
| `Sim.lean` | `Ctx`, `Ctx.Inv`, `Exh`, `Grows`, `reach_inst1`, `enterBlock_of` |
| `Step.lean` | `freshFor_run`, `ExtIdx`, `declare_lookup`, `reach_callExt(_trap)`, `RtOK` |
| `Env.lean` | `EnvRel`/`selHdl` lemmas |
| `Prims.lean` | `ErrAt`, `reach_selectVals`, `reach_errIf` |
| `Arith.lean` | instruction semantics on encoded scalars |
| `RtSpec.lean` | `mapEnv` specs, `toWord` lemmas, `reach_toWordV`/`reach_ofWordV`, `Inv.mem_step` |
| `Expr.lean` | `XPre`, `XPost`, `Prog`, `clone_sim`, **`expr_sim`** |
