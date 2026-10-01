# Contract: CLIF in Lean (`FV/Clif`, milestone M0)

Producer: M0. Consumers: M1 (emitter produces `Clif.Program`), M2 (`Clif.run (compile f) =
denote f`), M3 (validator relates Arm states to CLIF), M4 (ISLE rules vs per-op semantics).
Subset: `clif-subset-v2` (`docs/contracts/clif-subset.md`). Pinned against Cranelift 0.136.1.

## Status

All M0 deliverables are in place:

- [x] `FV/Clif/Syntax.lean`, `Sem.lean`, `Mem.lean`, `Run.lean`, `Print.lean`, `Parse.lean`,
      umbrella `FV/Clif.lean`
- [x] `rust/crates/clif-oracle` (`interp`, `check`)
- [x] `FVTest/Clif/Filetest.lean` (`lean_exe clif-filetest`), `scripts/clif-filetests.sh`
- [x] `FVTest/Clif/SpecCrossread.lean`, `docs/contracts/clif-spec-crossread.md`
- [x] `FVTest/Clif/StepExamples.lean` (symbolic execution through `Clif.run`)

Commands:

```
lake build FV.Clif FVTest.Clif.SpecCrossread FVTest.Clif.StepExamples
scripts/clif-filetests.sh            # all runtests, both engines, printer check; -v for details
lake build clif-filetest && .lake/build/bin/clif-filetest [-v] [--oracle-dir D | --oracle F.json] [--print-dir D] FILE.clif...
cargo build --release --manifest-path rust/Cargo.toml -p clif-oracle
rust/target/release/clif-oracle interp FILE.clif    # JSON lines, schema below
rust/target/release/clif-oracle check FILE.clif     # reader + verifier, exit status
```

## Modules and public API

All names are in namespace `Clif` (per-op semantics in `Clif.Sem`).

### `FV/Clif/Syntax.lean`

- `inductive Ty | i8 | i16 | i32 | i64 | i128`; `Ty.width : Ty → Nat` (8…128), `Ty.bytes`,
  `Ty.name`, `Ty.ofName?`, `Ty.ofWidth?`, `Ty.double?`, `Ty.half?`, `Ty.width_pos`.
- `structure Val where ty : Ty; bits : BitVec ty.width` (`DecidableEq`);
  `Val.ofInt`, `Val.ofNat`, `Val.ofBool` (`i8` 0/1), `Val.toNat`, `Val.toInt`,
  `Val.as? : Val → (ty : Ty) → Option (BitVec ty.width)` (`@[simp] Val.as?_mk`).
- `inductive TrapCode | stkOvf | heapOob | intOvf | intDivz | badToint | user (n : Nat)`
  (`1 ≤ n ≤ 250`), `TrapCode.name`, `TrapCode.ofName?`.
- `structure MemFlags` (`trapCode : Option TrapCode := some .heapOob` — `none` is `notrap`;
  `aligned`, `readonly`, `canMove : Bool`; `endianness : Option Endianness`), `MemFlags.notrap`.
- `IntCC` (10 codes), `UnaryOp`, `BinaryOp`, `DivOp`, `OverflowOp`, `CarryOp`, `ExtendOp`,
  `LoadOp`, `StoreOp`, `AtomicRmwOp`.
- `abbrev ValueId BlockId SlotId FnRef := Nat` (`vN`, `blockN`, `ssN`, `fnN` by number).
- `structure BlockCall where block : BlockId; args : List ValueId`.
- `inductive Inst`: `iconst ty imm` · `unary op ty x` · `binary op ty x y` · `div op ty x y` ·
  `overflow op ty x y` (results `ty`, `i8`) · `carry op ty x y c` · `uaddOverflowTrap ty x y code` ·
  `icmp cc ty x y` (`ty` = operand type, result `i8`) · `select ty c x y` ·
  `selectSpectreGuard ty c x y` · `bitselect ty c x y` · `bmask ty x` · `extend op ty x` ·
  `ireduce ty x` · `iconcat ty lo hi` (`ty` = operand type) · `isplit ty x` (`ty` = operand type) ·
  `load op ty flags p offset` · `store op ty flags x p offset` (`ty` = type of `x`) ·
  `stackAddr ty slot offset` · `call fn args` · `atomicRmw op ty flags p x` ·
  `atomicCas ty flags p e x` · `atomicLoad ty flags p` · `atomicStore ty flags x p` · `fence` ·
  `bitcast ty flags x` · `trapz c code` · `trapnz c code` · `nop` ·
  `symbolValue ty gv` (`symbol_value.ty gvN`; v2).
  Every value-producing instruction carries its controlling type explicitly.
- `inductive Terminator | jump dest | brif c thenDest elseDest | brTable x default table |
  ret vals | returnCall fn args | trap code`.
- `structure Stmt where results : List ValueId; inst : Inst`.
- `structure Block where id; params : List (ValueId × Ty); cold : Bool; body : List Stmt; term`.
- `AbiParam` (`ty`, `ext : ArgExt`, `purpose : ArgPurpose`), `CallConv`, `Signature`
  (`params`, `returns`, `callConv : Option CallConv`; `none` = reader default). Extension,
  purpose and calling convention have no effect on `Clif.run`.
- `StackSlot` (`size`, `align : Option Nat` in bytes), `GlobalValue` (declarations only; the
  `global_value` instruction is not in S), `ExtFunc` (`name`, `sig`, `colocated`).
- `Expect | eq vals | ne vals | nonzero | print`, `RunCommand` (`func`, `args`, `expect`).
- `structure Function where name; sig; slots; globals; externs : List (FnRef × ExtFunc);
  blocks : List Block; runs : List RunCommand`. The first block is the entry block. `runs` is
  empty for emitted code.
- `structure Program where header : List String; funcs : List Function`.
- `Function.block?`, `Function.slot?`, `Function.extern?`, `Function.entry?`,
  `Program.func?`, `Inst.resultTypes`.

### `FV/Clif/Sem.lean` — per-opcode semantics (`Clif.Sem`)

Separately unfoldable definitions on `BitVec w`:
`iadd isub ineg imul umulhi smulhi iabs` · `udiv sdiv urem srem : … → Except TrapCode (BitVec w)` ·
`band bor bxor bnot bitselect` · `shiftAmt w y := y.toNat % w`, `ishl ushr sshr rotl rotr`
(amount of any width `v`) · `clz ctz popcnt cls bitrev bswap` · `smin smax umin umax` ·
`uaddSat saddSat usubSat ssubSat` · `uaddOverflow … smulOverflow : … → BitVec w × Bool` ·
`uaddOverflowCin saddOverflowCin usubOverflowBin ssubOverflowBin` · `uaddOverflowTrap` ·
`intcc cc x y : Bool`, `bool8`, `icmp cc x y : BitVec 8` · `truthy x := x ≠ 0`, `select`,
`bmask` · `uextend v`, `sextend v`, `ireduce v`, `iconcat lo hi : BitVec (w + w)`,
`isplit v` · `atomicRmw op old x` · dispatchers `unary`, `binary`, `shift`, `div`,
`overflow`, `carry`; `BinaryOp.isShift`.

Semantics notes (all checked against the runtests and the interpreter):
- shift and rotate amounts are taken mod `w`; `clz 0 = ctz 0 = w`; `cls` counts leading
  sign bits excluding the sign bit; `iabs MIN = MIN`;
- `udiv/urem/sdiv/srem x 0` trap `int_divz`; `sdiv MIN, -1` traps `int_ovf`;
  **`srem MIN, -1 = 0`** (CLIF docs, VeriISLE, native backends);
- flags of `*_overflow`, `*_sat` and `*_cin`/`*_bin` are mathematical: the flag is set iff
  the exact result is not representable. **`sadd_overflow_cin`/`ssub_overflow_bin`** use the
  exact sum `x + y + c` (like AArch64 `adcs`/`sbcs`);
- `icmp` produces `i8` 1/0; conditions (`brif`, `select`, `trapz`, `trapnz`, `bmask`) test
  non-zero at any width.

### `FV/Clif/Mem.lean`

- `inductive Res (α) | ok a | trap code | stuck msg` with `Monad` and `LawfulMonad`
  instances; simp lemmas `Res.ok_bind`, `trap_bind`, `stuck_bind`, `ofOption_some/none`,
  `ofExcept_ok/error`, `check_true/false`. `Res.ofOption`, `Res.ofExcept`, `Res.check`.
- `structure Alloc where base size : Nat; readonly : Bool := false`; `Alloc.contains`.
- `structure Mem where allocs : List Alloc; bytes : Nat → Option (BitVec 8); next : Nat;
  symbols : String → Option Nat` (`Mem.empty`: no allocations, `next = 0x10000`, no symbols).
  `symbols` is the link-time symbol table read by `symbol_value`; execution never changes it.
- `Mem.readonlyAt m addr n`; `Mem.store` is `stuck` if the bytes overlap a `readonly`
  allocation ("store to read-only data").
- Link-time image (v2): `Image.itemSize`, `Image.size`, `Image.place`, `Image.writeItems`,
  `Image.mem (ds : List DataObject) : Res Mem` (objects allocated in order with the bump
  allocator, alignment `max align 16`, read-only unless `writable`; `.addr n k` items written as
  the 8-byte little-endian address of object `n` plus `k`; `symbols n` = address of object `n`;
  duplicate names or relocations to unknown objects are `stuck`).
  `Program.initMem p : Res Mem` = `.ok Mem.empty` if `p.data = []`, else `Image.mem p.data`.
- `Mem.valid m addr n`, `Mem.alloc m size align : Nat × Mem`, `Mem.free m bases`,
  `Mem.readBits m big addr n w : Option (BitVec w)`, `Mem.writeBits m big addr n x`,
  `Mem.checkAccess`, `Mem.load m flags addr n w : Res (BitVec w)`,
  `Mem.store m flags addr n x : Res Mem`.

Memory invariants:
- byte-addressed, little-endian (big-endian only with the `big` flag);
- an access is valid iff all its bytes lie inside one live allocation; otherwise it traps
  with the flags' trap code (default `heap_oob`), or is `stuck` if the access is `notrap`;
- a valid access with `aligned` at a misaligned address is `stuck`; atomics must be
  naturally aligned (`stuck` otherwise);
- bytes start uninitialised (`none`); reading one is `stuck`;
- `alloc` is a bump allocator (alignment `max align 16`, 16-byte gap after every
  allocation); addresses are never reused, freed allocations make later accesses through
  stale pointers invalid;
- the `readonly`/`can_move` *flags* are not checked; stores into read-only data objects are
  `stuck`.

### `FV/Clif/Run.lean`

```lean
inductive Outcome | returned (vals : List Val) (mem : Mem) | trapped (code : TrapCode)
                  | stuck (msg : String) | outOfFuel
def Outcome.returnedVals? : Outcome → Option (List Val)
structure Env where extern : String → Option (List Val → Mem → Outcome) := fun _ => none
def Env.empty : Env
abbrev Regs := ValueId → Option Val        -- Regs.empty, Regs.set, Regs.setMany (+ simp lemmas)
structure Frame where func : Function; regs : Regs; slots : List (SlotId × Nat);
                      body : List Stmt; term : Terminator
structure State where frame : Frame; callers : List (Frame × List ValueId); mem : Mem
inductive StepResult | next (s : State) | done (vals : List Val) (mem : Mem)
                     | trapped (code : TrapCode) | stuck (msg : String)
def evalInst (fr : Frame) (mem : Mem) : Inst → Res (List Val × Mem)   -- every non-call inst
def enterBlock (fr : Frame) (bc : BlockCall) : Res Frame
def enterFunc (f : Function) (args : List Val) (mem : Mem) : Res (Frame × Mem)
def stepCall (env) (p) (s) (rest) (results) (fn) (args) : StepResult
def returnValues (s : State) (vals : List Val) (mem : Mem) : StepResult
def stepReturnCall (env) (p) (s) (fn) (args) : StepResult
def stepTerm (env : Env) (p : Program) (s : State) : Terminator → StepResult
def step (env : Env) (p : Program) (s : State) : StepResult
def runLoop (env : Env) (p : Program) : Nat → State → Outcome
def initState (p : Program) (f : String) (args : List Val) (mem : Mem) : Res State
def runWith (env : Env) (p : Program) (f : String) (args : List Val) (mem : Mem) (fuel : Nat) : Outcome
def run (env : Env) (p : Program) (f : String) (args : List Val) (fuel : Nat) : Outcome
  -- = runWith env p f args m fuel where p.initMem = .ok m (stuck/trapped otherwise)
theorem run_of_data_nil : p.data = [] → run env p f args fuel = runWith env p f args Mem.empty fuel
```

Lemmas for stepping: `runLoop_zero` (simp), `runLoop_succ`, `step_term`, `step_call`,
`step_inst`, `StepResult.ofRes_ok/trap/stuck` (simp). `FVTest/Clif/StepExamples.lean` shows
proofs about symbolic inputs: straight-line code and calls close by `rfl`, branches by
`cases` on the condition plus `simp` with the definitions above.

Machine structure and invariants:
- `step` executes one statement of the current block or its terminator; `fuel` counts
  steps (`runLoop` returns `outOfFuel` when it runs out). Recursion is bounded by fuel.
- `call fnN(args)`: `fnN`'s declaration name is looked up first among the program's
  functions (a new frame is pushed, its stack slots are freshly allocated), then in
  `env.extern` (an atomic step on `(args, mem)`; an extern's `outOfFuel` is `stuck`). The
  callee's signature (types) must equal the declaration's. `return_call` replaces the
  current frame (its slots are freed first).
- `return`: the values must have the function's return types; the frame's slots are freed;
  the caller's pending call results are bound, or `run` finishes with
  `returned vals mem` (the final memory, with every stack slot freed).
- Branches evaluate all block arguments first, then bind the target's parameters (parallel
  assignment); `br_table` uses the index as an unsigned number, out of range → default.
- Addresses: `effAddr p offset = (p.toNat + offset) mod 2^64` (pointer zero-extended);
  `stack_addr.ty ssN+off` is `Val.ofInt ty (base + off)`.
- `stuck msg` exactly when a precondition fails: unknown function/value/block/slot/fn
  reference, operand of the wrong type, arity mismatch, an `extend` that does not widen or
  `ireduce` that does not narrow, `iconcat.i128`/`isplit.i8`, a `notrap` access out of
  bounds, a misaligned `aligned` or atomic access, a read of uninitialised memory.
  `trapped c` only for CLIF traps (`trap`, `trapz/nz`, division, `uadd_overflow_trap`,
  out-of-bounds accesses that may trap).

### `FV/Clif/Print.lean`, `FV/Clif/Parse.lean`

- `Clif.print : Program → String`; `Function.print`; `Function.valueTypes`.
  Header lines, then each function followed by its run commands. Polymorphic instructions
  always get an explicit `.ty` suffix (`brif`/`trapz`/`trapnz`: the condition's type), so the
  reader never has to infer a type from a value defined later in the layout. Integers are
  signed decimal; offsets `+N`/`-N`; memflags in the writer's order.
- `Clif.parse : String → Except String Program` (every function must be in S).
- `inductive ParseError | unsupported msg | malformed msg`; `structure ParsedFunction`
  (`name`, `func : Except ParseError Function`, `runLines`), `structure ParsedFile`
  (`header`, `funcs`); `Clif.parseFile : String → ParsedFile` (per function; functions
  outside S are `unsupported` with the reason: non-integer type, opcode, declaration).
- Accepted: `test`/`target`/`set` headers (kept verbatim), `function %name(sig) [-> …] [cc]`,
  `ssN = explicit_slot N[, align = K]`, `gvN = vmctx | load… | iadd_imm… | symbol
  [colocated] [tls] %name[+off]` (the reader's order; a `tls` symbol is a thread-local
  variable, the operand of `tls_value`), `fnN = [colocated] %name(sig)`, blocks with parameters and `cold`, value aliases
  `vA -> vB` (collected for the whole function before the body is read, so a use may precede
  its alias line, as in cranelift-reader; chains followed, duplicates and cycles `malformed`), optional `.ty` suffixes (inferred from the typevar operand as
  the reader does), memflags, trap codes, `; run: %f(args) == v` / `!= v` / `== [v, …]`,
  bare `; run`, `; print: …`. Literals: decimal, negative, `0x` hex with `_`, reduced mod
  `2^w`. Run arguments/expectations are typed by the signature of the function the comment
  follows (as in the reader); run commands attach to the preceding function.
- Round trip: `parse (print p) = p` for the program of every file's supported functions
  (checked by `clif-filetest` on all 395 runtests: 0 failures), and every printed file is
  accepted by `cranelift-reader` + the Cranelift verifier (`clif-oracle check`: 146 files,
  0 rejected).

## Rust externs: `Clif.Rust.env` and `clif-filetest --rust-env` (rust-route)

`FV/Clif/Rust.lean` defines `Clif.Rust.env : Clif.Env`: the trusted contracts for the
externs `rustc_codegen_cranelift` output calls (see `docs/contracts/e2e.md`, "Rust route").
`clif-filetest --rust-env` runs with that env instead of `Env.empty` (the default is
unchanged, so the runtests gate is unaffected):

* `memcpy(dst, src, n)` / `memmove(dst, src, n) -> i64` and `memset(dst, c, n) -> i64`:
  byte-level `Mem` semantics (each destination byte becomes initialised; both ranges in
  one allocation, no read-only destination; otherwise `stuck`), returning `dst`;
* `memcmp(a, b, n) -> i32`: bytewise unsigned (`0`/`-1`/`1`), `stuck` on uninitialised
  bytes;
* every diverging entry point (`Clif.Rust.isPanic`: mangled names containing
  `panic`/`fail`/`handle_`, `Formatter`, `…3fmt`) ends the run with
  `trapped (user 1)` — no value is returned. Natively they are `udf #251` (SIGILL).

A `; print:` run command passes for any outcome (a `print` has no expectation, so an
aborting call is recorded, not failed).

## `clif-oracle` and its JSON schema (shared with `clif-native`)

`clif-oracle interp FILE.clif` prints JSON lines, one record per `; run`/`; print` comment,
in file order (functions in order, comments in order):

```json
{"attached": "f",            // function the comment follows (name without %)
 "func": "g",                // invoked function (bare `; run` = the attached function)
 "args": [{"ty": "i32", "bits": "0x0000002a"}],
 "expected": {"cmp": "==", "values": [{"ty": "i8", "bits": "0x01"}]},   // "!="; null for print
 "actual": {"returned": [{"ty": "i8", "bits": "0x01"}]}}                 // or:
             // {"trapped": "int_ovf"}  (trap code name; also "bad_signature", "unreachable",
             //                          "heap_misaligned", "debug" for interpreter-only traps)
             // {"error": "..."}        (interpreter error or panic, e.g. unimplemented opcode)
```

Values: `ty` is Cranelift's type name; `bits` is `0x` + the value's bytes as a
little-endian unsigned number, zero-padded to the type's width (`2·bytes` hex digits).
A file the reader rejects yields one line `{"file_error": "..."}` and exit status 1.
The interpreter runs as in `cranelift/filetests/src/test_interpret.rs` (one `FunctionStore`
for the file, fresh state per command, same libcall handler), with fuel `10^8` and a
1 GiB stack. `clif-oracle check FILE.clif` exits 0 iff the file parses and every function
passes the verifier (default flags).

## Link-time data and `symbol_value` (clif-subset-v2)

- Syntax: `Program.data : List DataObject := []`; `DataObject` = `name`, `align := 1`,
  `writable := false`, `items : List DataItem`; `DataItem | byte (b : BitVec 8) |
  addr (name : String) (addend : Int)` (an `Abs8` relocation).
- Text: before the first function, `; data: %name [align=N] [writable] = item…`, where an
  item is an even-length hex string (bytes in memory order) or `%sym[+N|-N]` (8-byte absolute
  address). A comment, so cranelift-reader ignores it. `Clif.parseFile` returns them in
  `ParsedFile.data` (`Except String`), `Clif.parse` puts them in `Program.data`, `Clif.print`
  prints them back (round trip), `clif-filetest` runs with them, and `clif-native` assembles
  them into a linked object (`docs/contracts/drivers.md`).
- `symbol_value.ty gvN`: `gvN` must be `symbol [colocated] %s[+k]` (other kinds are `stuck`);
  the result is `Val.ofInt ty (addr + k)` with `addr = mem.symbols s` (`stuck` if undefined).
  `colocated` has no effect on the value. Loads from the address follow the normal `load`
  rules (bounds = the object's allocation).
- Checked: `FVTest/Clif/fixtures/e-v2-symbol-value.clif` (28 runs: tables, offsets, relocated
  pointers, a writable object) pass in `Clif.run` and agree with native Cranelift code
  (`clif-native`, 28/28). The Cranelift interpreter does not implement data symbols
  (`GlobalValueData::Symbol => unimplemented!()`), so those 28 runs are `oracle-error`.
- `tls_value.ty gvN` (a `symbol tls` gv): `Clif.run` has one thread, whose instance of the
  variable is the image's symbol (`mem.symbols name + offset`, as `symbol_value`). In subset E
  as `tls_value.i64` with offset 0 (agent/stack-tls-proof; `docs/contracts/e2e.md`, "`tls_value`").
- Not modelled: function symbols in data (vtables of `fn` pointers), threads, data symbols of
  other functions' `gv` offsets beyond the object (out-of-bounds reads trap/stuck as usual).

## S-list additions (M0)

| Added | Unlocks (runs passing through `Clif.run`) |
| --- | --- |
| `atomic_rmw`, `atomic_cas`, `atomic_load`, `atomic_store`, `fence` | atomic-128 (93), atomic-128-cas-lse (8), atomic-cas (8), atomic-cas-little (8), atomic-cas-subword-big (12), atomic-cas-subword-little (12), atomic-load-store (34), atomic-rmw-little (232), atomic-rmw-subword-big (264), atomic-rmw-subword-little (266), fence (1), issue5884 (1), issue5901 (1) |
| `bitcast` (integer, same type) | bitcast-same-type (15), i128-bitcast (1) |
| `return_call` | return-call (7) |
| `select_spectre_guard`, `bitselect`, `uadd_overflow_cin`, `sadd_overflow_cin`, `usub_overflow_bin`, `ssub_overflow_bin` | selectif-spectre-guard, bitselect, i128-bitselect, iaddcarry, isubborrow (all runs) |

Atomics are single-threaded: a checked load followed by a checked store at the same
naturally aligned address; `atomic_rmw`/`atomic_cas` return the old value.

## Filetest results (`scripts/clif-filetests.sh`, 395 files in `runtests/`)

| | runs |
| --- | --- |
| passed through `Clif.run` | **5706** |
| failed | **7** (1 function, see below) |
| unsupported (with reason) | 8020 |
| agree with the Cranelift interpreter | 5700 |
| disagree with the interpreter | 13 (0 in files with a `test interpret` header) |
| printed files rejected by cranelift-reader/verifier | 0 of 146 |
| round-trip failures | 0 |

Files: 128 fully supported (every run passes or, for the one function below, fails),
12 partially (functions with floats/vectors), 255 fully unsupported.

Failures (7 runs): `i128-load-store.clif` `%i128_stack_store_load_inst_offset` stores and
loads through `stack_addr ss1+16` with `notrap`, i.e. 16 bytes past the end of the 16-byte
slot `ss1`. The test relies on the stack layout (`ss2` follows `ss1`); in our model each
slot is its own allocation, so the access violates `notrap` and is `stuck`. This is a
deliberate choice: slot-granular bounds are what the emitter must respect. The interpreter
(contiguous frame) returns the expected value, so these 7 runs are also disagreements.

Disagreements besides those (6 runs, `div-checks.clif`, no `test interpret` header):
`srem MIN, -1` for i8/i16/i32 (register and constant divisor): we return 0 as the test
expects; the interpreter traps `int_ovf` (an interpreter bug; the file is not run under
`test interpret` upstream).

Unsupported runs by reason: float types 5904 (328 functions), vector types 2096
(1030 functions), `func_addr`/`call_indirect` 7, `sigN` declarations 3, `set_pinned_reg` 3,
callers of unsupported functions 3, `get_stack_pointer` 2, `get_frame_pointer` 1,
`f32const` 1.

Fully supported files: alias-analysis-endianness, alias, amode-shared-base,
arithmetic-extends, arithmetic, atomic-*, bitops, bitrev, bitselect, bmask, bnot, br,
br_table, brif, cls, clz, const, ctz, div-checks, extend, fence, fibonacci, fold-bitops,
global_value, i128-* (all integer ones), iabs, iaddcarry, icmp-*, ineg, inline-probestack,
integer-minmax, ireduce, issue-*/issue*.clif (integer ones), isubborrow, long-jump,
mul_overflow_flag_consumers, or-and-y-with-not-y, popcnt, rotl, rotr, sadd_overflow, sdiv,
selectif-spectre-guard, shift-right-left, shifts, smul_overflow, smulhi, spill-reload, srem,
stack, stack-addr-32/64, uadd_overflow*, udiv, umul_overflow, umulhi, urem, usub_overflow,
x64-bmi1/2 and others (full list: `scripts/clif-filetests.sh -v`).

## Known gaps

- No `func_addr`/`call_indirect`/`return_call_indirect`/`try_call` (function pointers),
  `global_value`/`symbol_value`, pinned register, stack/frame pointer intrinsics, floats,
  vectors.
- The interpreter comparison covers only the runtests' inputs. Runtests cannot express
  trap expectations and none of the supported runs traps, so trap outcomes are compared
  with the interpreter only when run by hand (`clif-filetest` compares trap codes when both
  engines trap). A manual check at M0 time (`sdiv MIN/-1`, `sdiv x/0`, an out-of-slot load
  without `notrap`, `uadd_overflow_trap … user7`, `sshr.i8` by 9 and by `-1`): 8 of 8 outcomes
  agree, including trap codes.
