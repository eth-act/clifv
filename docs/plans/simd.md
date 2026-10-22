# SIMD (S12, #36): vector CLIF types under the theorems

Goal: the functions of real crates that cg_clif compiles with vector-typed CLIF (`i64x2`,
`i32x4`, …) compile through the Lean backend and are covered by the end-to-end theorems
(`E2E.backend_correct_final*`, `Link.DeadCleanup.compileExe_correct*`) instead of falling back
to cg_clif. As for floats (`docs/plans/floats.md`), the theorem statements stay the same; their
scope grows, through new scope predicates under new names. S12 builds on S11 (floats): the FP
register class, the typed ABI, the class-aware value map and the typed scope `functionET` of
S11e.

## 1. What real code needs (measured)

**Fallbacks.** `examples/deps`, debug build, report of 2026-10-18 (`cargo fv test`, agent/linker-l2b;
21021 functions, 20821 verified, 200 fallbacks): 9 SIMD fallbacks, all
`decode: unsupported: type i64x2` (4) or `type i32x4` (5). Release: 6 (`docs/USAGE.md`).

| package | functions (cg_clif instance) |
|---|---|
| sha2 (8) | `core::arch::aarch64::vsha512{h,h2,su0,su1}q_u64`, `core::arch::arm_shared::vsha256{h,h2,su0,su1}q_u32` |
| zmij (1) | `zmij::to_bcd_4x4` |

`examples/fv-demo` (1370 functions), `survey` (3179) and `vendor` have no SIMD fallback.

**Constructs.** `scripts/simd-scan.py DIR…` scans cg_clif's per-function dumps
(`<unit>.clif/<symbol>.unopt.clif`) for vector-typed CLIF and counts the constructs:

| dumps | distinct functions | with a vector type | constructs (functions) |
|---|---|---|---|
| `examples/deps` debug (agent/alias-total target) | 17039 | 9 | `load.i32x4` 5, `load.i64x2` 4, `store` of a vector 9; nothing else |
| `examples/survey` | 2993 | 0 | — |
| `examples/fv-demo` | 1351 | 0 | — |
| `examples/vendor` | 7525 | 0 | — |
| `core` + `alloc` (`scripts/rust-clif/core.sh`, x86_64, release) | 1561 | 0 | — |

std on aarch64 could not be measured: cg_clif rejects core's 128-bit atomics on aarch64
(`scripts/rust-clif/core.sh` header; T3 #39). The 9 functions all have the same shape: each
vector operand is loaded from its by-reference argument (`load.i64x2 notrap v1`), stored into
an explicit stack slot (`store notrap v4, v7`), the slot's address is passed to cg_clif's
global-asm shim (`call fn0(v10)`, the `__inline_asm_*` symbol that holds the `sha512h`/… or
`/*{0:v}*/` asm), and the result is loaded back and stored to the return place. No lane
operation, no vector arithmetic, no vector parameter, return, block parameter, call argument,
`bitcast` or `vconst` appears. Calls to the inline-asm shims are already verified in other
functions (4 such zmij functions are verified in the same report).

**Why no other construct appears (cg_clif source, nightly-2026-09-26).** cg_clif implements every
SIMD intrinsic (`src/intrinsics/simd.rs`, `llvm_aarch64.rs`) lane by lane through memory
(`simd_for_each_lane`, `CValue::value_lane` on `ByRef` places, scalar CLIF per lane);
`clif_type_from_ty` has no SIMD case, so a SIMD local is never an SSA variable; a copy of a SIMD
place is a memcpy-style sequence of `i64` loads/stores. A vector-typed CLIF value arises only
from `CValue::load_scalar` on a `SimdVector` layout (inline-asm operands, `src/inline_asm.rs`),
from `PassMode::Direct` SIMD arguments and returns (`abi/pass_mode.rs`; only non-Rust ABIs
pass SIMD by value), and from `transmute` into a scalar SSA variable (`codegen_bitcast`, a
`bitcast` with explicit little-endian flags). This is why memchr (829 functions, 170 mention
NEON) and hashbrown's NEON group compile without a single vector-typed CLIF value.

**Cranelift's runtests.** 177 of the 396 files in
`cranelift/filetests/filetests/runtests` use vector types (154 of them target aarch64, 1809
`; run` lines). They are the oracle for a full vector semantics (phase B below), not something
the measured crates need.

Consequences for the order of work:

1. **Phase A, vector data movement**, covers all 9 measured fallbacks: vector types,
   `load`/`store` of 128-bit vectors, and, because cg_clif can emit them, vector parameters,
   returns, call arguments/results and `bitcast`. No lane semantics is needed by any measured
   function.
2. **Phase B, lane operations and vector arithmetic** (`splat`, `extractlane`, `insertlane`,
   `iadd`… on vectors, `shuffle`, widen/narrow, vector compares and float lanes) is needed only by
   Cranelift's runtests and hand-written CLIF. It is deferred (DEFERRED.md, "SIMD lane
   operations") until a measured crate needs it.

## 2. Semantics decisions

**Types.** `Clif.Ty` gets one constructor, `vec (s : VShape)`, over an enumeration of the
legal 64- and 128-bit shapes: `i8x8 i16x4 i32x2 f32x2` (64 bits) and `i8x16 i16x8 i32x4 i64x2
f32x4 f64x2` (128 bits). One constructor keeps the `cases ty` proofs at one new arm; an enum
(not `vec (lane : Ty) (n : Nat)`) excludes ill-formed shapes by construction. `Ty.width (vec s)
= s.lanes * s.laneBits`. `isInt (vec _) = false`; `Ty.isFloat` (today `!isInt`) becomes the
explicit `f32 | f64` test and `Ty.isVec` is new, so no float statement silently admits vectors
(hazard 1 in section 9).

**Representation.** `Clif.Val` stays a type tag plus raw bits (`BitVec ty.width`). Lane `i` of
a vector is bits `[i·laneBits, (i+1)·laneBits)` (`extractLsb'`), lane 0 least significant: the
order of Cranelift's interpreter (`interpreter/src/step.rs` `extractlanes`: lane `i` is bytes
`[i·n, (i+1)·n)` of the `V128` byte array, little-endian within the lane) and of the Arm model
(`elem_get`), so a lowering proof compares the same bit vector on both sides. Float lanes carry
raw bits (NaN payloads exact), as `f32`/`f64` do.

**Memory.** A vector `load`/`store` moves `width/8` bytes exactly like the equal-width integer
access with little-endian byte order (`Mem.load flags addr 16 128`): lane `i` occupies bytes
`[i·laneBytes, (i+1)·laneBytes)`. Big-endian vector accesses (`big` flag) are rejected (`stuck`)
rather than modelled: Cranelift reverses bytes per lane, not over the whole vector, cg_clif never
sets `big`, and the aarch64 rules match `little_or_native_endian` only.

**`bitcast`.** With `little` (or no flag, same lane count) it is the identity on the bits between
types of equal width (vector ↔ vector, vector ↔ `i128`/`f64`/`i64` of the same width). With
`big` and different lane counts it is rejected (`stuck`), as above.

**Phase B semantics (recorded now, implemented later).** Integer lanes wrap (two's complement);
lane-wise float operations use the S11c core per lane with the AArch64 `FPCR = 0` NaN choice
(`floats.md` §2, which is inside Cranelift's admissible set lane by lane); `extractlane`/
`insertlane` with an out-of-range immediate are rejected by the verifier, so `Clif.run` is
`stuck` there; `swizzle` yields 0 for out-of-range indices; `shuffle` indexes the 32-byte
concatenation.

**Lean model (S12b, done).** The lane/byte functions live in `FV/Clif/Vector.lean` (independent of
`Clif.Ty`, so it does not touch the files of the running float slices): `VShape` with
`laneBits`/`lanes`/`width`/CLIF names, `Vec.lane`, `Vec.setLane`, `Vec.byte` (byte `j`,
little-endian, the layout `Mem.readBits`/`writeBits` give with `big = false`), `Vec.bitcastLE`,
and their algebra (`lane_setLane_same`, `lane_setLane_ne`, `ext_lane`, `byte_lane`: byte `j` of
lane `i` is byte `i·laneBits/8 + j`, `byte_bitcastLE`). S12d plugs them into
`Clif.Ty`/`Clif.run`.

## 3. Arm model: Advanced SIMD coverage

The state has 32 × 128-bit SIMD&FP registers (`ArmState.sfp`, `read_sfp`/`write_sfp`, the write
zero-extends). Instruction classes, by need:

| need | instructions | model | co-simulation |
|---|---|---|---|
| A: vector load/store | `ldr`/`str q` (unsigned offset, unscaled `ldur`/`stur`, pre/post-index, register offset), `ldp`/`stp q`, `ldr q` (literal) | yes (`LDST/Reg_imm`, `Reg_unscaled_imm`, `Reg_pair`, `Reg_literal`) | yes (`Specs.lean` `ldstSimdVariants`, `ldstPair`, `ldrLiteral`; 0 failures) |
| A: register moves | `mov vd.16b, vn.16b` (`orr` vector; Cranelift `FpuMove128`) | yes | yes (`orr (vector)`) |
| A: `bitcast` `i128` → vector | `fmov d, x` + `ins vd.d[1], x` (`mov_to_fpu`, `mov_to_vec`) | `fmov` yes; `ins` (general) yes | yes (`ins (general)`: S12c) |
| A: `bitcast` vector → `i128`/`i64` | `umov x, v.d[0..1]` (`mov_from_vec`) | yes | yes (`umov`) |
| model, not checked yet | `ins` (element), `dup` (element, general), `smov`, `rev16/rev32/rev64` (vector), `add`/`sub` (vector), `and`/`bic`/`orn`/`eor`/`bsl`/`bit`/`bif` (vector) | yes (LNSym ports with FV fixes) | yes (S12c) |
| B: lane arithmetic and permutes | `cmeq`/`cmgt`/… (vector), `mul`, `smin`/`umax`…, `sqadd`…, shifts by immediate (`ushr`, `sshll`/`ushll`), `xtn`/`sqxtn`, `zip`/`uzp`/`trn`, `ext`, `tbl`, `fadd`/`fmul`/… (vector), `fcvt*` (vector) | no (LNSym's `Advanced_simd_{extract,permute,shift_by_immediate,table_lookup,three_different,…}` were dropped, `docs/contracts/arm.md`) | phase B |

Phase A therefore needs no new Arm semantics. S12c (done, 2026-10-22) co-simulated the Advanced
SIMD forms that were in the model but unchecked: 17 new forms in `FVTest/Arm/Cosim/Specs.lean`,
0 failures (`scripts/arm-cosim.sh`: 350 forms, 70 000 vectors), no model change.

## 4. Register class

The machine side already holds vectors: the FP class (`RegClass.float`, `Reg.v`) is 128 bits
wide end to end. `Backend.Proof.CV` is `BitVec 128` and `regVal (.v n)` is the full `q`
register; spills and register-to-register FP moves go through 16-byte slots with `str q`/`ldr q`
(`StackAlloc.slotStore`, `RAFrame.moveInsts`); calls clobber all of `v0`–`v31`
(`RegallocOps.defaultAapcsClobbers`, as Cranelift's `DEFAULT_AAPCS_CLOBBERS`), so no vector
value lives across a call in `v8`–`v15`, whose upper halves AAPCS64 does not preserve; the
callee-saved contract keeps the low 64 bits (`ckeep`). What is float-shaped is the value map
and the typed scope: `valClass` maps `f32`/`f64` to `.float`; vectors join them there, and the
S11e typed predicates (`CtxInvT`, `functionET`, `LowerScopeT`) get the vector types through
`Ty.isVec`.

## 5. Lowering rules (Cranelift 0.136.1, `lower.isle`)

Phase A roots (generated names, `FV/Isle/Generated`):

| rule | CLIF | lowering | closure today |
|---|---|---|---|
| `rule_lower_2633` (`load_ty_vec128`, prio −4) | `load` of a 128-bit vector | `aarch64_fpuload128` → `ldr q` | excluded (`ty_128`, `ty_float_or_vec`) |
| `rule_lower_2754` (prio −4) | `store` of a 128-bit vector | `aarch64_fpustore128` → `str q` | excluded |
| `rule_lower_2628` / `rule_lower_2750` (prio −3) | `load`/`store` of a 64-bit vector | `ldr d`/`str d` | included, proven for `f64` (S11e4); extend to 64-bit vectors |
| `rule_lower_2779` (prio 7) | `bitcast` SIMD&FP ↔ SIMD&FP | identity | included (S11e4) |
| `rule_lower_2784` / `rule_lower_2789` | `bitcast` `i128` ↔ vector | `fmov d, x` + `ins v.d[1], x` / 2 × `umov` | excluded (`i128`); needs `MInst.movToVec` |

The 128-bit memory rules lower to `MInst.load .fpuLoad128`/`store .fpuStore128`, the forms that
today only spill code uses: the integer memory contracts carry `op ≠ .fpuLoad128` premises
(`E2E/ExecReads`, `Lockstep`, `Guarded`, `RegLevelOpReads`, `Concurrency/VCodeFrame`), and the
float memory bridge (`MemRefinesFP`, S11e5 slice 4) is stated for 4- and 8-byte accesses.
Phase A adds 16-byte variants beside them under new names.

ABI: Cranelift's aarch64 `compute_arg_locs` places 64/128-bit vectors like floats (`v0`–`v7`,
then 16-byte aligned stack slots); `argLocsC`/`retRegsC` (S11e2) are class-based, so a vector
is a `.float`-class argument of 16 bytes.

**Route taken for the measured functions (S12e, 2026-10-22): retyping + `i128` legalisation.**
The 9 measured functions only move 128-bit vectors from memory to memory (§1), so they need
neither `q` registers nor the 16-byte FP contracts above. `Opt.Retype` (`FV/Opt/Retype.lean`)
rewrites each plain `load`/`store` at a type of a `TyMap σ` (for S12: the 128-bit vector shapes,
`vec128`) to the access at a type of the same width (`i128`), on the domain `okB σ f`: each
retyped load defines one value, read only as the stored value of retyped stores (not by any
other statement, terminator or block parameter). The retyped function is then the input of the
existing, proven `i128` legalisation (two `i64` accesses per 16-byte access) and backend.
Theorems: `Opt.Retype.retype_simX` (`FunSimX f (retype σ f)` on `okB`, `call_indirect` and
`try_call` included; the registers agree outside the retyped values and hold the same bits at
the other type there), and `E2E.backend_correct_retype_legal_wide{,_cleanup}` /
`…_retype_legal_opt_wide{,_cleanup}` (`FV/E2E/RetypeLegal.lean`: the Arm code of the
legalisation `g` of `retype σ f` refines the run of `f`, by `retype_simX` lifted to the program
run, composed with `backend_correct_legal_wide`/`_opt_wide`). Witnesses:
`Opt.Retype.Witness.copyF_sim` (a function the retyping changes), `E2E.LinkWitness.a2_retype_legal_wide`.
The `q`-register lowering of this section stays the route for vectors in registers (parameters,
returns, `bitcast`), when a measured function needs it.

## 6. Proof plan

The statements of `E2E.backend_correct_final*`, `Link.compileExe_correct*`,
`Link.DeadCleanup.compileExe_correct*` and `Front.bundle_correct_raw*` stay as they are: their
scope predicates (`Compile.functionET`, `LowerScopeT`, `InScopeIn`) admit vector data movement
through new, wider predicates under new names, with the old ones as corollaries (every existing
theorem kept). The steps:

1. `Clif.run` on vectors (S12d) is a specification: checked against the Cranelift interpreter
   on the data-movement runtests (`scripts/clif-filetests.sh`, pass count up, no new
   disagreement) and against native code under qemu (`lean-backend-filetests.sh`).
2. Rule correctness (S12e): `rule_lower_2633`/`2754` proven over `CtxInvT` with a 16-byte FP
   memory refinement, following `IselFloatMem.lean` (`load.f64`/`store.f64`); 64-bit vectors
   reuse the `f64` proofs through the width.
3. Lockstep/link (S12e): the program-level 16-byte FP accesses through the guarded simulation
   and the ABI contracts (`ArgsIn` with 16-byte `.float` locations).
4. Scope and totality (S12f): `functionET`/`InScopeIn` widened by vector data movement
   (`driverInB`/`iselInB` totality kept), `examples/deps` SIMD fallbacks 9 → 0.

Every new top-level theorem gets a concrete non-vacuity witness (a sha2-shaped function: two
vector loads, a slot store, a shim call, a reload, a store); compiler theorems print only
`propext`, `Classical.choice`, `Quot.sound`.

## 7. Slices (one PR each, merged on per-PR gates, TO-PROVE §7)

| slice | content | depends on | size (estimate) |
|---|---|---|---|
| S12a | **done** (#369): this plan; `scripts/simd-scan.py` | — | docs |
| S12b | **done**: `FV/Clif/Vector.lean`: `VShape`, `Vec.lane`/`setLane`/`byte`/`bitcastLE`; `lane_setLane_same`, `lane_setLane_ne`, `ext_lane`, `byte_lane`, `byte_bitcastLE`, `bitcastLE_bitcastLE` + witnesses | — | 216 lines, 1 new module (no importers yet) |
| S12c | **done**: Arm co-simulation of the unchecked Advanced SIMD forms (section 3), 17 forms, 0 failures, no FV/Arm change | — | 60 lines in `FVTest/Arm/Cosim` |
| S12d | `Clif.Ty.vec`, explicit `isFloat`, `isVec`; parser/printer (`i64x2`, `vconst` literals for runtests); `Clif.run` data movement (`load`, `store`, params, returns, calls, block params, `select`, `bitcast`); integer/float premises where vectors make statements false | floats Stage C slice 8 (scope widening) merged | like S11b (#264: 155 files, +2045/−742) |
| S12e | **done (theorems)**: `Opt.Retype` + `retype_simX`, `E2E.backend_correct_retype_legal_wide*` (§5, "Route taken"); then `lean-backend` retypes the `vec128` accesses before the `i128` legalisation (needs S12d) | S12d for the wiring | ~900 lines |
| S12f | `lean-link`: the input's functions retyped before legalisation under new theorem names (`FnInput.func` keeps its meaning), totality, end to end: `lean-e2e-check`, `cargo fv test --lean-link --verified` on fv-demo/survey/deps with fallback counts before → after (deps SIMD 9 → 0), docs | S12e | ~1500 lines |
| S12e′ (if measured) | vectors in registers: closure gets `rule_lower_2633`/`2754` (+ 64-bit vectors through `2628`/`2750`), 16-byte memory refinement, typed value map with vector types, ABI with vector arguments/returns | S12d, a measured need | like S11e4 + S11e5 slice 4 (~5000 lines) |
| S12g (if measured) | `bitcast` `i128` ↔ vector: `MInst.movToVec` (`ins`), encoder, `rule_lower_2784`/`2789` | S12e | ~800 lines |
| phase B | lane semantics and arithmetic (section 1, item 2) | a measured need | DEFERRED |

## 8. Testing (oracles)

- `Clif.run`: Cranelift interpreter on the runtests (`scripts/clif-filetests.sh`), vector
  results compared bit for bit (data movement involves no NaN choice).
- Arm model: `scripts/arm-cosim.sh` (qemu), the forms of section 3.
- Backend: `scripts/lean-backend-filetests.sh` (native code under qemu, the runtests whose
  functions are in scope) and `lean-backend-encode-check.sh` (0 differ).
- End to end: `cargo fv test --lean-link --verified` on `examples/deps` (the 9 functions),
  `scripts/simd-scan.py` on the run's dumps, `scripts/float-fallbacks.py` (its `simd` bucket).

## 9. Known hazards

1. `Ty.isFloat` is `!isInt` today (142 uses in `FV`). With a vector constructor it would call
   vectors floats, so S12d defines it explicitly and audits every use; float statements stay
   about `f32`/`f64`.
2. `fpuLoad128`/`fpuStore128` mean "spill" in many proofs (`op ≠ .fpuLoad128` premises). A
   program-level 16-byte access must not be confused with spill code; S12e states the program
   access as its own case beside the spill-slot one.
3. Cranelift's verifier rejects `bitcast` between vectors of different lane counts without an
   explicit endianness; `Clif.run` must not accept what Cranelift rejects for `big`.
4. `Clif.Syntax` changes rebuild everything downstream, including the heavy `FV.Opt.Proof.*`
   modules; S12d is one PR, after floats Stage C slice 8, with a main-gate run right after it.
5. `clif-native`'s random differential generator has no vector values; vector diffs need it
   extended (or the runtests suffice for data movement).
6. The mid-end (`Isle.Opt`) has no vector nodes; vector instructions must pass through it
   unchanged (`optimizeExe`'s shape guard), checked by `scripts/opt-difftest.sh`.
