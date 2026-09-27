# Contract: DSL → CLIF emitter (`FV/Compile`, milestone M1; proof M2)

Producer: M1 emitter. Consumers: M2 (`compile_correct` against this code), M3 (validates the
Cranelift output of these functions), the differential tests. Inputs: `docs/contracts/dsl.md`
(AST, `denote`, checker), `docs/contracts/clif.md` (`Clif.Program`, `Clif.run`),
`docs/contracts/clif-subset.md` (subset E).

## Status (kept current for resumption)

M1 emitter deliverables complete (2026-09-27):

- [x] `FV/Compile/{Abi,Emit,Model,Subset,Runtime,Harness}.lean`, umbrella `FV/Compile.lean`:
      `lake build FV.Compile` clean (no warnings), no `sorry`, no `axiom`;
      `#print axioms Compile.compile` → `[propext, Classical.choice, Quot.sound]`
- [x] `corpus/dsl/Corpus/Emit.lean` (10 extra programs), `FVTest/Compile/Cases.lean`
- [x] `lake exe emit corpus/clif`: 41 files (+8 in `extrt/`), 114 run lines
- [x] `lake exe compile-diff`: 107/107 vectors, `onlySubsetE` 41/41 programs
- [x] `FVTest/Compile/Kernel.lean`: `runCompiled` computes in the kernel (`decide +kernel`)
- [x] `rust/crates/flat-runtime` (host tests 2/2, aarch64 staticlib)
- [x] `scripts/diff-corpus.sh`: four engines agree on 114/114 run lines, Rust runtime 22/22 (§8)

## 1. Data layout

Every DSL value is **flattened into a list of scalar CLIF values**
(`Compile.flat : DSL.Ty → List Clif.Ty`):

| DSL type | CLIF values |
| --- | --- |
| `int w` (u8…u64) | one `i8`/`i16`/`i32`/`i64` |
| `bool` | one `i8`, 0 or 1 |
| `unit` | none |
| `vec n t` | `n` copies of `flat t`, element 0 first |
| `prod a b` | `flat a ++ flat b` |
| `map k v` | one `i64` handle to a runtime object |

One uniform rule, no memory for vectors or products. Vectors are small fixed-size values
(PLAN.md §3.1), so flattening keeps the M2 simulation relation register-based. `vset` is a
functional update of the list of SSA values (old values are no longer referenced), so in-place
soundness is trivial for vectors. The affine rule matters only for maps, which are runtime
objects that `flat_map_insert` mutates in place. Cost: every vector access with an index
expression costs `n` compare-and-branch steps (§3), with code linear in `n · |flat t|`.
There is no special case for constant indices.

## 2. Function ABI

A compiled `f : FlatFn σ τ` is the CLIF function `%(mangle f.name)`, default call conv:

- **Parameters**: `[ctx : i64]` iff `Compile.Stmt.usesCtx f.body` (the body or a transitive
  callee calls the map runtime: `mapEmpty`, `mapContains`, `mapGet`, `mapInsert`, `clone`
  of a map-containing type). Then `[ret : i64]` iff buffer mode (below). Then `flat σ` in order.
- **Returns**:
  - *Register mode*, when `1 + |flat τ| ≤ 8`: `i8 tag` then `flat τ`.
  - *Buffer mode* (`FnAbi.sret`), otherwise: only `i8 tag`. The payload goes into the caller's
    buffer `ret` of `8·|flat τ|` bytes. Flat value `j` sits at offset `8·j`, stored at its own
    width, little-endian.

  The limit 8 is the AArch64 integer return registers x0–x7. Cranelift 0.136.1 rejects more
  return values unless `enable_multi_ret_implicit_sret` is set, and the fixed driver settings
  (PLAN.md M1) do not set it. A buffer-mode caller allocates the buffer as its own stack slot.
- **Error-tag ABI** (docs/ARCHITECTURE.md): `tag = 0` is ok; `tag = Err.tag e` means `throw e`.
  On error, register-mode payloads are `iconst 0` and buffer-mode buffers are zero-filled.
  Every failure site (`throw`, a failed check, a callee error) jumps to the single error exit
  `block1(tag : i8)`. `block0` is the entry block. There are no traps.
- `ctx` is the runtime context, a pointer to the map arena (§4). It is passed unchanged to
  every map extern and to every callee that takes it.
- Mangling (`Compile.mangle`, injective, reader-safe `[A-Za-z0-9_]`): ASCII letters and digits
  are kept, `.` → `__`, `_` → `_1`, any other character `c` → `_x<hex c>_`. Example:
  `Corpus.sumChecked` → `%Corpus__sumChecked`. A mangled name never equals a runtime name
  (`flat_map_*`, `flat_rt_*` contain `_m`, `_r`, which are not escapes) or a wrapper name
  (`…_w<j>`).
- `Compile.compile f` is `compileFn f` followed by one function per distinct callee name
  reachable through `Stmt.call` (first occurrence, call order). The dsl.md frontend guarantees
  that a name identifies one body.

## 3. Lowering, per construct

`compileExpr`/`compileOp` emit into the current block and return the SSA values of the
result. They may end the current block and continue in fresh ones. `compileStmt s kont`
always ends the current block. Its value goes to `kont`: `.ret` returns `(0, value)` (buffer
mode: store, then `return 0`), and `.jump J` is `jump J(value)`. Names come from
`CG.nextVal`, `CG.nextBlock` and the slot count, threaded through `StateM CG`.

| Construct | CLIF |
| --- | --- |
| `var v` | the values of `v` (a move of a map transfers the handle) |
| `clone v` | same values; each map component → `call flat_map_clone(ctx, h)` |
| `ilit`, `blit`, `unit` | `iconst.iN`, `iconst.i8 0/1`, nothing |
| `ibin add…ashr` | `iadd isub imul band bor bxor ishl ushr sshr` (shift mod width = `Ops.shl…`) |
| `inot` / `bnot` | `bnot.iN` / `bxor.i8 b, 1` |
| `icmp eq ne ult ule slt sle` | `icmp` with the same condition code (`i8` 0/1) |
| `band`, `bor` (bool) | `band.i8`, `bor.i8` |
| `cast op w'` | narrower: `ireduce` (all three ops); wider: `sextend` for `sext`, else `uextend`; same width: no code |
| `cond c a b`, `ite` | `brif c` into a join block with parameters (no `select`); `ite`: `brif c, T, E`, both compiled with the same `kont` |
| `pair`, `fst`, `snd`, `vrepl` | list concatenation / prefix / suffix / replication, no code |
| `mapEmpty`, `mapContains m k` | `call flat_map_new(ctx)`, `call flat_map_contains(ctx, h, zext64 k)` |
| `iop addC` | `s = iadd a, b`; overflow iff `icmp ult s, a` |
| `iop subC` | `d = isub a, b`; overflow iff `icmp ult a, b` |
| `iop mulC` | `p = imul a, b`; overflow iff `icmp ne (umulhi a, b), 0` |
| `iop udiv/urem` | `icmp eq b, 0` → error 2, then `udiv`/`urem`, which cannot trap |
| `vget v i` | `icmp uge i, n` → error 3 (omitted when `n ≥ 2^w`). Then for `k = 1…n-1`: `r := brif (icmp eq i, k), J(elem k), J(r)`, starting from `r = elem 0` |
| `vset v i e` | the same bounds check, then per `k`: `elem k := brif (icmp eq i, k), J(e), J(elem k)` |
| `mapGet m k` | 8-byte slot `p`; `found = call flat_map_get(ctx, h, zext64 k, p)`; `brif found, ok, block1(4)`; `load.i64 notrap aligned p`, then `ireduce` to the value type |
| `mapInsert m k x` | `call flat_map_insert(ctx, h, zext64 k, zext64 x)`, handle unchanged |
| `throw e` | `jump block1(iconst.i8 e.tag)` |
| `call g body args` | `res = call %g([ctx], [buf], args)`; `brif res.tag, block1(res.tag), ok`. Buffer-mode callee: `buf` is an own slot and the payload is `load … notrap aligned` from it |
| `let_`, `letPair`, `set` | compile-time environment only (`env.set v.idx`) |
| `bind s k` | fresh join `J(flat α)`; `s` with `.jump J`, then `k` in `J` with `#0 = J`'s parameters |
| `forRange n init body` | `jump H(0, init)`; `H(i, acc)`: `brif (icmp ult i, n), B, X`; `B`: body with `.jump L`; `L(acc')`: `jump H(i + 1, acc')`; `X`: `kont acc` |

Map keys and values are `int`/`bool` values zero-extended to `i64` (`uextend`, or nothing for
`u64`). The runtime's words are converted back with `ireduce` (`u64`: nothing).

Memory flags: `notrap aligned` only on accesses to the function's own explicit slots
(`explicit_slot 8·k, align = 8`), at offsets `8·j` inside the slot. These are `mapGet` out
cells, buffer-mode result buffers, and the wrappers' arena header and entry cells. Stores
into a caller-provided buffer keep the default flags (trap `heap_oob`). The emitter never
emits `trap`, `select` or `*_overflow`.

## 4. Runtime: map externs

This is the extern table of dsl.md §5 with one change: **every extern takes the runtime
context `ctx : i64` as its first parameter.** The Cranelift interpreter can only call
functions of the same file, and CLIF subset S has no global state (`global_value` and
`symbol_value` are not in S). A CLIF implementation of the runtime therefore needs its arena
passed in. The test wrappers put the arena in a stack slot. dsl.md carries a pointer to this
section.

| Extern (all `i64` params) | Returns | Meaning (`Compile.mapEnv`, over `DSL.Map` entry lists) |
| --- | --- | --- |
| `flat_map_new(ctx)` | `i64` handle | empty map |
| `flat_map_insert(ctx, h, k, v)` | — | `entries := upsertL k v entries` (in place) |
| `flat_map_contains(ctx, h, k)` | `i8` 0/1 | `(lookupL k entries).isSome` |
| `flat_map_get(ctx, h, k, out)` | `i8` 0/1 | `lookupL`; if found, writes the value word to `*out` |
| `flat_map_clone(ctx, h)` | `i64` | an independent map with the same entries |
| `flat_map_len(ctx, h)` | `i64` | number of entries (test harness) |
| `flat_map_entry(ctx, h, i, kp, vp)` | — | entry `i` in insertion order, `0, 0` if `i ≥ len` (test harness) |

`flat_map_free` is not emitted. Leaks are unobservable in M1 and the arena is freed with its
stack slot.

Three implementations are kept consistent:

1. **`Compile.mapEnv`** (Lean `Clif.Env`, the specification, used by `runCompiled` and M2).
   Map objects live in `Clif.Mem`: a 16-byte header (`len`, `data`) and `len` entries of 16
   bytes (key word, value word). Every insert writes a fresh entry array with `Mem.alloc`.
   The model ignores `ctx`.
2. **CLIF runtime** (`Compile.Runtime.text`, written as `corpus/clif/runtime.clif` and
   appended to every emitted file that calls it). Arena at `ctx`: `used` at `+0`, `cap` at
   `+8`, bump allocation, exhaustion traps `user1`. Map object: `len`, `cap`, `data`. The
   entry array doubles from 4. Uses only E opcodes.
3. **`rust/crates/flat-runtime`**: the same algorithm and layout as 2, `#![no_std]`, no global
   state, `extern "C"` symbols. Linked natively into the `extrt/` variants.

All three are run on the whole corpus by `diff-corpus.sh`. 1 runs in (a); 2 runs in (b), (c)
and (d); 3 runs in (d) on the Rust runtime. `flat-runtime` also has a randomized unit test
against an association-list model (4000 operations, 8 maps, clones, growth).

## 5. API

| Module | Contents |
| --- | --- |
| `FV/Compile/Abi.lean` | `intTy`, `flat`, `flatList`, `maxRegReturns = 8`, `Expr/Exprs/Op/Stmt.usesCtx`, `FnAbi` (`ctx`, `params`, `result`; `sret`, `bufSize`, `paramTys`, `retTys`, `signature`), `bodyAbi`, `fnAbi`, `mangle`, `toWord`, `ofWord?` |
| `FV/Compile/Emit.lean` | `Cont`, `FnCtx`, `CG`, `CGM := StateM CG`, generator primitives (`fresh`, `freshFor`, `emitStmt`, `inst1`, `iconstN`, `newBlock`, `terminate`, `switchTo`, `newSlot`, `declare`, `callFn`, `errIf`), `slotFlags`, `rt*` extern signatures, `selectVals`, `selectElem`, `updateElem`, `boundsCheck`, `cloneVals`, `compileExpr`, `compileExprs`, `compileOp`, `finish`, `compileStmt`, `compileBody`, `Callee`, `Stmt.callees`, `dedupCallees`, **`compileFn : FlatFn σ τ → Clif.Function`**, **`compile : FlatFn σ τ → Clif.Program`** |
| `FV/Compile/Model.lean` | `mapExtern`, **`mapEnv : Clif.Env`**, `readEntries`, `writeEntries`, `newMapObj`, `encodeVal`, `encodeArgs`, `decodeVal`, `CallSetup`, **`setupCall`**, `readBuf`, **`decodeResult : FnAbi → Option Nat → Clif.Outcome → Option (DSL.M τ.denote)`**, **`runCompiled f args fuel`**, `defaultFuel` |
| `FV/Compile/Subset.lean` | **`onlySubsetE : Clif.Program → Bool`** (opcodes, `i8…i64`, flags limited to `notrap`/`aligned`) |
| `FV/Compile/Runtime.lean` | `Runtime.text` (CLIF map runtime), `Runtime.functions`, `Runtime.names` |
| `FV/Compile/Harness.lean` | wire encoding (`wireTys`, `wireVal`, `wireArgs`), `needsWrapper`, `wrapper`, `testProgram tc (withRuntime := true)` |

`compileStmt`, `compileExpr`, `compileOp`, `cloneVals`, `Stmt.callees` and `usesCtx` are
structurally recursive. The whole pipeline `runCompiled` reduces in the kernel
(`FVTest/Compile/Kernel.lean`).

**Test wrappers** (`Compile.Harness`). A run line can only pass and compare scalars. A
function is called directly iff it has no `ctx`, no buffer mode, and no map in `σ` or `τ`.
Otherwise the emitter generates CLIF wrappers `%<mangled>_w<j>`:

- *Parameters* are the wire encoding of the arguments. It is `flat`, except that a map is
  `len, k₀, v₀, …, k_{C-1}, v_{C-1}`, where `C` is the largest map in the case's vectors.
- *Body*: a 64 KiB arena slot, map arguments built by `flat_map_new` and conditional
  `flat_map_insert`, the call, and on success the result serialised to wire form (maps through
  `flat_map_len` and `flat_map_entry`).
- *Result*: `i8 tag` then chunk `j` (7 values) of the wire result. Chunk `j` exists for every
  `j < ⌈wire length / 7⌉`.

Every corpus function is covered by run lines (directly or through wrappers) and by
`compile-diff`.

Commands:

```
lake build FV.Compile FVTest.Compile.Kernel
lake exe emit corpus/clif          # regenerates the corpus files
lake exe compile-diff [-v]         # (a) denote vs Clif.run (compile f), onlySubsetE
scripts/diff-corpus.sh [-v]        # everything, four engines (§8)
cargo test --manifest-path rust/Cargo.toml -p flat-runtime
cargo rustc --release --manifest-path rust/Cargo.toml -p flat-runtime \
  --target aarch64-unknown-linux-musl --crate-type staticlib -- -C panic=abort
```

`flat-runtime` declares `crate-type = ["rlib"]`. A `staticlib` crate type in `Cargo.toml` would
make every host workspace build link a `no_std` staticlib with unwinding panics, which rustc
rejects. The aarch64 archive is therefore built with `cargo rustc --crate-type staticlib`.

## 6. The M2 theorem and the simulation invariants

**Statement** (to be proven in `FV/Compile/Correct.lean`):

```lean
theorem Compile.compile_correct {σ : List DSL.Ty} {τ : DSL.Ty} (f : DSL.FlatFn σ τ)
    (hf : f.checked) (args : DSL.Args σ) :
    ∃ fuel₀, ∀ fuel ≥ fuel₀, Compile.runCompiled f args fuel = some (DSL.denote f args)
```

Unfolded, this runs `Clif.runWith Compile.mapEnv (compile f) (mangle f.name) s.args s.mem fuel`.
Here `s = setupCall (fnAbi f) args` (always `.ok`). Its arguments are `ctx = 0` (ignored by the
model), then a fresh buffer in buffer mode, then `encodeArgs`; map arguments are fresh
`Mem` objects. The result is decoded with `decodeResult`: tag `0` plus the canonical encoding
of the value, or `Err.tag e` plus an all-zero payload. `compile f` computes in the kernel,
so small instances hold by `decide +kernel`. Supporting lemmas M2 needs: fuel monotonicity of
`Clif.runLoop`, `ofWord? t (toWord t x) = some x`, and `setupCall = .ok _`.

**Relations.**

- `Enc t x vs mem`: the values `vs` (types `flat t`) encode `x : t.denote`. Scalars are equal
  bits (`bool` is 0/1). Vectors and products hold per component. A map is a handle `h` with
  `readEntries mem h = .ok (x.entries.map (toWord k × toWord v))`.
- `EnvRel Γ env ρ regs mem`: for every variable `i` that is *alive* (checker state), the
  values `env[i]` are defined in `regs` and `Enc (Γ[i]) (ρ.get i) (regs env[i]) mem`. The map
  handles of distinct alive variables are distinct, and the objects they reach do not overlap.
  This is the dsl.md §4 invariant; a move leaves the moved variable dead.
- `Fresh cg regs`: every value id `≥ cg.nextVal` and block id `≥ cg.nextBlock` is unused, so
  each generated name is defined exactly once (SSA) and generation only extends `regs`.

**Per construct** (all from a state whose current block is `cg.cur`, satisfying `EnvRel` and
`Fresh`):

- `compileExpr e` executes straight to the open block it returns, without failing. It
  returns `vs` with `Enc t (e.denote ρ) (regs' vs) mem'`, where `regs'` extends `regs`. `mem'`
  differs from `mem` only by fresh allocations (`mapEmpty`, `clone`) and leaves every
  existing object intact. `cond` goes through one `brif` into a join block.
- `compileOp o`: if `o.denote ρ = .error e`, execution reaches `block1` with argument
  `e.tag8`. If it is `.ok x`, execution reaches the returned open block with `Enc t x`. The
  checks are exact: `icmp ult (a + b) a ↔ BitVec.uaddOverflow`, `icmp ult a b ↔ usubOverflow`,
  `umulhi ≠ 0 ↔ umulOverflow`. `udiv`/`urem` run only on a non-zero divisor, so they are
  never `int_divz`. The select chains produce element `i.toNat`.
- `compileStmt s kont`: if `s.denote ρ = .error e`, execution reaches `block1(e.tag8)`. If
  it is `.ok x`, then for `kont = .jump J` it reaches `J` with `Enc τ x` of the arguments, and
  for `kont = .ret` it returns `(0, enc x)` (buffer mode: the stores, then `return 0`).
  `bind` composes the two cases at the join block. `ite` splits on the branch. `set`,
  `let_`, `letPair`, `vset` re-establish `EnvRel` for the updated environment. `mapInsert`
  changes only the object of the (alive, unshared) map variable, which by `upsertL` equals
  `(ρ.get v).insert k x`.
- `forRange n init body`: invariant at `H(i, acc)` with `i ≤ n` (`n < 2^64` by the checker):
  `acc` encodes the accumulator after iterations `0…i-1` of `Ops.forRange`, and `EnvRel`
  holds for the outer environment (the body updates no outer linear variable). Per iteration,
  the body with `.jump L` either reaches `block1` or `L`, and `L` re-enters `H(i+1, …)`.
- `block1(tag)` returns `tag` with a zero payload (buffer mode: zero stores).
- `call g body args`: `compile f` contains `compileBody g body` (`Stmt.callees` closure,
  deduplicated by name). By induction on the nesting of embedded callee bodies (structural:
  `body` is a subterm), the callee simulates `body.denote`. The caller then continues or
  propagates the tag.
- `notrap aligned` obligations: `mapGet` cells and result buffers are own slots of size
  `≥ 8(j+1)` whose base `Mem.alloc` aligns to 16. They are read only after being written:
  by `flat_map_get` when found, or by the callee's stores on success.

## 7. Opcode audit (subset E)

`Compile.onlySubsetE` checks every emitted program. `compile-diff` checks it on all 41
compiled programs, and `emit` refuses to write a file whose non-runtime functions leave E.
Opcode census of the emitted corpus (compiled functions plus wrappers, runtime excluded):

| Opcode | Count | Opcode | Count |
| --- | ---: | --- | ---: |
| `iconst` | 1626 | `bxor` / `bor` / `band` / `bnot` | 36 / 34 / 4 / 1 |
| `brif` | 1088 | `ushr` / `ishl` / `sshr` | 34 / 33 / 2 |
| `icmp` (`eq` 905, `uge` 83, `ult` 52, `ne` 11, `slt` 2, `sle` 2, `ule` 1) | 1056 | `uextend` / `sextend` / `ireduce` | 28 / 2 / 4 |
| `jump` | 192 | `imul` / `umulhi` / `isub` | 12 / 10 / 11 |
| `return` | 137 | `udiv` / `urem` | 4 / 2 |
| `load` (all `notrap aligned`) | 133 | `call` | 65 |
| `store` (buffer: default flags; arena: `notrap aligned`) | 114 | `stack_addr` | 41 |
| `iadd` | 88 | | |

The CLIF runtime uses only E opcodes too (`load`, `store`, `iadd`, `ishl`, `icmp`, `brif`,
`jump`, `call`, `return`, `iconst`, and `trap user1` for arena exhaustion).

## 8. Differential results (`scripts/diff-corpus.sh`, 2026-09-27)

Corpus: `Corpus.all` (31 functions, 79 vectors) plus `Corpus.emitTests` (10 functions, 28
vectors), for 41 functions and 107 vectors (41 end in `throw`). The emitted files hold 114
run lines; buffer-mode results are split into chunks (ChaCha20: 3 wrappers).

It covers loops (nested; loop-carried tuples; map inserts in loops), checked arithmetic that
overflows (u8/u16/u32/u64 add/sub/mul), `divByZero`, `indexOutOfBounds`, `notFound`, user
errors, errors from callees and from buffer-mode callees, and runtime calls (new, insert,
contains, get, clone, growth past 4 entries, maps as parameters and results, `ctx` passed to
callees).

| Engine | Result |
| --- | --- |
| (a) `denote` = expected = `Clif.run (compile f)` + `mapEnv` (`compile-diff`) | **107/107** vectors; `onlySubsetE` 41/41 |
| `clif-oracle check` (reader + verifier) | 50 files (42 + 8 `extrt/`), **0 rejected** |
| (b) `Clif.run` on the emitted files, CLIF runtime (`clif-filetest`) | **114/114** pass, round-trip 0 failures, agree with (c) 114/114 |
| (c) Cranelift interpreter (`clif-oracle interp`) | **114/114** pass |
| (d) native aarch64 under qemu, CLIF runtime (`clif-native`) | **114/114** pass; vs (c) 114 agree, 0 disagree |
| (d) native aarch64, Rust `flat-runtime` (`extrt/`, `--link`) | **22/22** pass; vs (c) 22 agree |

Every run line's expectation is `denote`'s result encoded per the ABI, so "pass" means
agreement with `denote`.

## 9. Decisions made without the owner, and known gaps

- The extern ABI gains `ctx` (§4). Vectors and products are flattened (§1). Buffer mode is
  used beyond 8 return values (§2).
- Extra corpus programs live in `corpus/dsl/Corpus/Emit.lean` as `Corpus.emitTests`.
  `Corpus.all` is unchanged because dsl.md does not define how to extend it; the emitter uses
  `FVTest.Compile.cases = Corpus.all ++ Corpus.emitTests`.
- Aggregate-signature functions are covered through generated CLIF wrappers, not through a
  Lean-only check. Every corpus function is covered by all four engines.
- Code size: a vector access with a non-constant index costs `n` branches, and so does a
  constant index (no special case, to keep the proof uniform). `vset` on a large vector of
  large elements is `O(n · |flat t|)` block arguments.
- Wrappers recompute the function once per result chunk. The wrapper arena is 64 KiB; the
  corpus uses far less.
- Arena exhaustion traps `user1` in the CLIF runtime and hits `udf` in the Rust runtime. It
  is a resource precondition and never happens in the corpus.
- The Lean model and the two runtimes use different in-memory layouts. Handles are opaque
  and only compared through the externs, which (b)–(d) exercise.
- M2 still has to prove `compile_correct` (§6). Nothing in M1 is proven about the emitter.
