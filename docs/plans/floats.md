# Floats (S11, #35): f32/f64 under the theorems

Goal: real crates' float functions compile through the Lean backend and are covered by the
end-to-end theorems (`E2E.backend_correct_final*`, `Link.DeadCleanup.compileExe_correct*`)
instead of falling back to cg_clif. The theorem statements stay the same; their scope
(`Compile.functionE`, clif-subset E, `InScopeIn`) grows. SIMD vectors (S12) are out of scope.

## 1. What real code needs (measured)

Source: `examples/deps` debug build (`cargo fv test`, report of agent/alias-total,
2026-10-09): 17249 functions, 158 fallbacks, of which 145 are floats
(`unsupported: type f64` 117, `type f32` 28, `opcode f64const` 1 counted with f64); the rest
are 9 NEON SIMD (S12) and 3 validation-budget functions. `examples/fv-demo`, `survey` and
`vendor` have no float fallbacks (fv-demo's 6 fallbacks are `metadata.fv.skip`). By package:
serde_json 50, num-integer 27, num-bigint 26, num-traits 14, zmij 11, deps-demo 8, serde_core 8,
serde 2.

Classification of the 145 float functions by the float constructs in their `.unopt.clif`
(scan of cg_clif's dumps, one count per function):

| construct | functions |
|---|---|
| **data movement only** (no float arithmetic): float parameters/returns, float call arguments/results, float `load`/`store`, block parameters, `select`, `f64const` | **100** |
| of these: float parameters or returns of the function or of a callee | 82 |
| of these: only float `load`/`store` (no float in any signature) | 8 |
| of these: only `f64const` | 1 |
| **with float arithmetic** | **45** |

Per operation (functions using it, among all 157 fallbacks):

| op | fns | | op | fns |
|---|---|---|---|---|
| `load.f64` | 35 | | `fabs` | 4 |
| `fcmp` (mostly `lt`) | 31 | | `fneg` | 4 |
| `fcvt_from_uint` | 25 | | `fcvt_from_sint` | 4 |
| `fcvt_to_uint_sat` (`.i32` 9, `.i64` 7) | 16 | | `f32const`, `fpromote`, `sqrt`, `fadd`, `fsub` | 2 each |
| `fdiv` | 12 | | `bitcast` int↔float | 3 |
| `f64const` | 10 | | `fdemote`, `trunc`, `ceil` | 1 each |
| `load.f32` | 9 | | `store.f32` | 1 |
| `store.f64` | 7 | | `fmul` | 5 |

**Reproduction (S11g).** `scripts/float-fallbacks.py target/fv-report.json` recomputes these
numbers from a run's report and cg_clif's dumps (`<unit>.clif/<symbol>.unopt.clif` beside the
unit's artifact; keep the target directory), and `--before OLD/fv-report.json` follows every
function by identity (package, crate, symbol; else instance) into a newer run. A fallback is a
float fallback when its dump has an `f32`/`f64` value, parameter, signature or constant (the
reasons changed since S11b, e.g. `call with f32/f64 parameters or returns`, `ctlCheck failed`;
without a dump, when its reason names `f32`/`f64`). On the 2026-10-09 report above it gives
158 fallbacks = **146 float** (117 `type f64` + 28 `type f32` + 1 `opcode f64const`: the 145
above are the first two) + 9 SIMD + 3 budget; **100 data movement only, 46 with float
arithmetic** (the hand count had 45); by package serde_json 50, num-bigint 27, num-integer 27,
num-traits 14, zmij 10, deps-demo 8, serde_core 8, serde 2. Its sub-rows differ from the
table's: 91 movement-only functions have an `f32`/`f64` in their own or a declared callee
signature (the table's 82 counted parameters/returns), 8 only float loads/stores. The per-op
counts are by function, among the float fallbacks.

Consequences for the order of work:

1. Float *types* with data movement (ABI in `v0`–`v7`, FP loads/stores, FP moves/spills,
   `fcsel`, `fmov`, constants, int↔float `bitcast`) cover 100 of 145 (69%) without any IEEE
   arithmetic. The FP ABI is the critical part (82 of the 100).
2. `fcmp`, `fcvt_from_{u,s}int`, `fcvt_to_{u,s}int_sat`, `fdiv`, `fmul` then cover almost all
   of the remaining 45; `fabs`/`fneg`/`fpromote`/`fdemote`/`sqrt`/`fadd`/`fsub`/`trunc`/`ceil`
   finish the list. `fma`, `fmin`/`fmax`, `fcopysign`, `floor`/`nearest`, trapping
   `fcvt_to_{u,s}int` are not used by the measured crates but are cheap once the core exists.

## 2. Semantics decisions

**Representation.** `Clif.Ty` gets `f32 | f64` (widths 32/64); `Clif.Val` stays a type tag
plus raw bits (`BitVec ty.width`), so NaN payloads and signed zeros are carried exactly. A
new `Ty.isInt`/`Ty.isFloat` separates the two; every place that means "integer type" says so
(scope predicates `tyE`/`eTy`, integer lemmas proved from `ty ≠ i128` or from the width
alone get an `isInt` premise). Memory stays byte-level: a float load/store moves the same
bytes as the equal-width integer access.

**IEEE 754.** binary32/binary64 as in IEEE 754-2019, rounding to nearest, ties to even for
every rounding arithmetic operation (Cranelift has no rounding-mode operand; cg_clif never
changes FPCR). Subnormals are kept (no flush-to-zero: Linux starts processes with
`FPCR = 0`, `FZ = 0`). Exceptions/flags (FPSR) are not observable in CLIF and are not modelled.

**NaNs.** Cranelift (`docs/ir.md`, "Floating point types") makes arithmetic NaN results
nondeterministic: a quiet NaN with nondeterministic sign, and a canonical payload if every
NaN input is canonical. `Clif.run` is a function, so it fixes one admissible choice: the
AArch64 one with `FPCR.DN = 0` (`FPProcessNaNs`: the first signalling NaN operand quietened,
else the first quiet NaN operand, else for an invalid operation the default NaN
`0x7FC00000`/`0x7FF8000000000000`). This is a refinement of Cranelift's specification (every
result it picks is allowed by `ir.md`), and it is exactly what the target computes, so the
backend proofs need no NaN reasoning. Fidelity checks compare NaN results *modulo the
`ir.md` admissible set* (both NaN, and canonical-in ⇒ canonical-out), not bit-for-bit, when
the oracle is the Cranelift interpreter (whose NaNs come from the host CPU); against qemu
(Arm co-simulation, `clif-native`) results are compared bit-for-bit. `fneg`, `fabs`,
`fcopysign`, `bitcast`, loads/stores, `select` and moves are bitwise and never touch NaNs.
`fmin`/`fmax` follow the WebAssembly rules Cranelift specifies (NaN-propagating, `-0 < +0`),
which is AArch64 `FMIN`/`FMAX`.

**Conversions.** `fcvt_to_{u,s}int` trap `bad_toint` on NaN and `int_ovf` when the truncated
value does not fit (Cranelift's `fpu_to_int_cvt` checks); `fcvt_to_{u,s}int_sat` saturate and
map NaN to 0 (AArch64 `FCVTZ{U,S}`, plus clamping for `i8`/`i16` results);
`fcvt_from_{u,s}int`, `fdemote` round to nearest even; `fpromote` is exact (signalling NaNs
quietened as `FPConvert` does). `ceil`/`floor`/`trunc`/`nearest` are `FRINTP/M/Z/N` (no
inexact flag).

**Lean model.** A bit-precise IEEE model of our own, `FV/Float/` (core only, no Mathlib),
used by *both* `Clif.run` and the Arm model: unpack `BitVec (1+e+m)` into a class
(zero/subnormal/normal/infinity/NaN) and an exact value `(sign, significand : Nat,
exponent : Int)`; operate exactly on integers (add/sub by alignment, mul exactly, div and sqrt
with guard bits plus a sticky bit); one `round` function (to nearest even, toward ±∞, toward
zero) back to the format, with overflow to ∞ and gradual underflow. Lean's native `Float` is
not used: it is opaque to the kernel (no proofs about it) and only exists for `f64`. The Arm
instructions are transcribed from the ASL (`FPAdd`, `FPProcessNaNs`, `FPRound`, `FPCompare`,
`FPToFixed`, `FixedToFP`, `FPRoundInt`, `FPConvert`) on top of the same core; the CLIF
operations are defined as the ASL results with `FPCR = 0`. The shared core makes lowering
correctness for a float rule a statement about the same function on both sides; the core
itself is checked by three oracles: qemu (Arm co-simulation, bit-exact including NaNs), the
Cranelift interpreter (`clif-filetests.sh`, modulo NaN admissibility), and native Cranelift
code under qemu (`clif-native`, `lean-backend-filetests.sh`).

## 3. Slices (one PR each, merged on per-PR gates, TO-PROVE §7)

| slice | issue | content | gates beyond the standard ones |
|---|---|---|---|
| S11a | [#234](https://github.com/eth-act/clifv/issues/234) | this plan | — |
| S11b | [#235](https://github.com/eth-act/clifv/issues/235) | CLIF float types and data movement: `Ty.f32/f64`, `isInt`/`isFloat`; parser (types, `f32const`/`f64const` hex/decimal literals, float run-line values), printer, `Clif.run` for float `load`/`store`/`select`/`bitcast`/constants/calls/block params; integer premises in the Opt/Backend proofs that only held because every type was an integer; scope predicates keep floats out of E | `clif-filetests.sh` pass count rises, 0 new disagreements; `opt-difftest.sh` 0 failures |
| S11c | [#236](https://github.com/eth-act/clifv/issues/236) | `FV/Float` IEEE core and the CLIF float arithmetic semantics (`fadd fsub fmul fdiv sqrt fma fneg fabs fcopysign fmin fmax fcmp ceil floor trunc nearest fpromote fdemote fcvt_*`), NaN-admissible agreement in `FVTest/Clif/Filetest.lean` | as S11b; a direct differential test of the core against the host's IEEE operations |
| S11d | [#237](https://github.com/eth-act/clifv/issues/237) | Arm FP/SIMD scalar instructions: `FADD FSUB FMUL FDIV FSQRT FMADD/FMSUB/FNMADD/FNMSUB FNEG FABS FMIN FMAX FCMP FCSEL FCVT (s↔d) FCVTZS/FCVTZU SCVTF/UCVTF FMOV (reg, imm) FRINTP/M/Z/N`, scalar SIMD&FP loads/stores if missing; decode, exec, co-simulation with IEEE edge-case generators (zeros, subnormals, ∞, NaN payloads, rounding ties); backend encoder classes with kernel-checked `decode_armBits_*` proofs; `lean-backend-encode-check.sh` forms | `arm-cosim` 0 mismatches; encode-check 0 differ |
| S11e | [#238](https://github.com/eth-act/clifv/issues/238) | Backend data movement: typed AAPCS64 ABI (`v0`–`v7` arguments/results, separate counters, `d8`–`d15` callee-saved low halves), FP loads/stores/moves/`fcsel`/constants (incl. the literal-pool `constant_f64` case), class-aware `buildCtx`/stock allocation, `ClassesHyp` (V4) with float values, `ArgsIn`/linking contracts for FP registers, ISLE float data-movement root rules in the closure with `LowerRulesCorrect` proofs; `functionE`/E/`InScopeIn` widened to float data movement with `driverInB`/`iselInB` totality kept | lean-backend filetests/runtests up; `cargo fv` deps fallbacks 145 → ≈45 |
| S11f | [#239](https://github.com/eth-act/clifv/issues/239) | Backend float arithmetic: the arithmetic/compare/convert root rules (`rule_lower_485` `fadd`, `rule_lower_2176` `fcmp`, `fpu_to_int_cvt{,_sat}`, `int_to_fpu`, …) proven against the shared core; scope widened to them | deps fallbacks ≈45 → 0 float |
| S11g | [#240](https://github.com/eth-act/clifv/issues/240) | End to end: `lean-e2e-check`, `cargo fv test --lean-link --verified` on fv-demo/survey/deps with fallback counts before → after, docs (TO-PROVE §2/§4/§8, PLAN, DEFERRED, USAGE) | — |

Status: S11a (#242), S11c (#244) and S11d (#248, phase 2 in the S11d (#237) arithmetic PR) are merged.

**S11b (#235): differential results.** `scripts/clif-filetests.sh` reports pass 11714 / fail 8 /
agree 11679 / disagree 13 / oracle-error 30, with 214 printed files and 0 rejected. Before S11b
the counts were pass 6072 / fail 7 / disagree 13, so the float runtests now run and pass, and
there are no new disagreements. The one additional fail is
`fcvt-sat-small.clif`'s line `; run: %fcvt_to_sint_sat_i8_f64(-0x1.fffffffffffffp1023) == 0`.
That line sits under `%fcvt_to_uint_sat_i8_f64`, so upstream `test run` calls the unsigned
function, but our tools call the named function (`docs/contracts/drivers.md`). Our tools and the
Cranelift interpreter therefore both return -128, which is correct for the signed conversion.
The line ran for the first time once f64 parsed. The 30 oracle errors are 28 `symbol_value`
runs and 2 in `try_call.clif`, which the interpreter cannot execute.
`scripts/opt-difftest.sh` exits 0: 395 runtests are not worse, and 207 + 50 optimised files are
checked with 0 rejected.

S11c and S11d are independent (exclusive files: `FV/Clif/*` vs `FV/Arm/*`,
`FVTest/Arm/Cosim/*`, `FV/Backend/Encode.lean`, `FV/Backend/Proof/Encode*.lean`) once the
`FV/Float` interface is fixed. S11e depends on S11b and the data-movement part of S11d; S11f
on all of them.

**S11e sub-slices.** The machine side already has both register classes (`RegClass.float`,
`Reg.v`), the `v0..v31` allocation pools, 16-byte FP spill slots and the `d8`–`d15` low-half
callee-saved contract (`RegallocOps.calleeSaved`, `ArmRet.savedV`), and `ArgsIn` is
location-generic; what is integer-only is the MInst/ISLE bridge, the ABI placement, the
value-to-register map and the proofs built on `typedReg`'s `.vreg x .int`. In dependency order:

| sub-slice | content | main files |
|---|---|---|
| S11e1 | scalar FP MInst forms used by data movement: `fpuLoad`/`fpuStore` (`FpuLoad32/64`, `FpuStore32/64`; their own `MInst` constructors with the size, so the `op ≠ .fpuLoad128` premises of the integer memory contracts stay as they are), `fpuCSel` (`FpuCSel32/64`), `fpuMoveFPImm` (`ASIMDFPModImm`), `vecDupImm` (`ASIMDMovModImm`; only the plain `movi #imm8` expands, which includes the zero of `constant_f32/64`); ISLE decoding, uses/defs/`mapRegs`, `emitOk`, `MInst.lines` into the S11d `Insn`s, the instruction semantics (`ispec`: `fcsel`, `VFPExpandImm`, `moviVal`) and its refinement/regalloc proofs (`FormOk` covers `fpuCSel`, `fpuMoveFPImm`, `vecDupImm`, and `fpuLoad`/`fpuStore` of size 32/64 with a float data vreg and a `memOk` mode: Arm-model memory proofs, `OperandsSound`/`LinesOk`, encodability, reads). Not yet: `fpuLoad64` of `AMode.Const` (literal pool), and the coverage/emission-check domains of the `asimd_*` immediates (S11e4) | `Backend/MInst.lean`, `Asm.lean`, `EmitOk.lean`, `RegallocOps.lean`, `Proof/{IselContract,RegallocInstsFP,RegallocMemFP,RegallocCSem,RegallocOS,RegallocCover,RefinesInsts2,RefinesCSem,CSemRename,SpillLocalForms,IselEmitChk,IselCovForm}.lean`, `E2E/{EmitEnc,RegLevelOpReads}.lean` |
| S11e2 | typed ABI placement: `sigArgs` with classes, `argLocs` with separate `x`/`v` counters, typed `retRegs`; `argLocs` of integer-only signatures unchanged (a lemma), so integer proofs transport | `Backend/Isel.lean` ABI section, `E2E/Final.lean` (`argsIn_iff_of_regs`), `LinkOwn*` (`retRegs_eq`) |
| S11e3 | class-aware value map: `buildCtx`/Stock allocation give a float value `.vreg x .float`; `CtxInv`/`CtxSpec`/`MappedCtxInv.typedReg` state the class of the type; driver entry loads, result copies and block/edge arguments per class; `ClassesHyp` (V4) with float values | `Isel.lean` `buildCtx`, `Lowering/Stock*.lean`, `Proof/{LowerLoopCtx,LowerSpec,DriverCheck,DriverCheckSound,SpillClasses,StockContext,StockDFG}.lean` (Stock files: @codygunton) |
| S11e4 | ISLE float data-movement root rules (`f32const`/`f64const`, float `load`/`store`/`select`, `bitcast`) in the closure with `LowerRulesCorrect`/`MemRulesCorrect` proofs | `Proof/Isel*` families, `IselExclBase`, `IselLowerAll`, coverage tables |
| S11e5 | E/`functionE`/`InScopeIn` widened to float data movement, `driverInB`/`iselInB` totality kept, call/return/link contracts for FP registers | `Compile/Subset.lean`, `E2E/LinkScopeInputDefs.lean`, `Proof/LowerTotal*.lean`, `E2E/LinkOwn*.lean` |

**S11e2 (typed ABI placement): done.** `FV/Backend/Isel.lean` places values per class as
Cranelift's aarch64 `compute_arg_locs` does: `argLocsC` (x0..x7 / v0..v7, separate counters,
then 8-byte-minimum aligned stack slots), `paramLocs` (`sret` in x8), `abiArgLocs` over
`abiArgs` (which admits `f32`/`f64`), `retRegsC`/`abiRetRegs` (8 per class). `argLocs`/`retRegs`
stay as the integer specialisations (`Proof.argLocsC_int`, `Proof.retRegsC_int`), and
`abiArgLocs_int`/`abiRetRegs_int` show the typed placement of an integer signature is the
lowering's. Interim: the lowering stays integer, `sigArgs` (hence `sigParamBytes`, `sigArgLocs`)
rejects a float parameter until S11e3 lowers FP argument moves, so `sigArgLocs` is unchanged
(`Proof.sigArgLocs_eq`) and the integer proofs needed only `unfold sigArgLocs` →
`rw [sigArgLocs_eq]` and `sigArgs_bytes` → `sigParamBytes_bytes`; no statement changed.
Witness `(f64, i64, f32)` ↦ `[v0, x0, v1]` (`FV/Backend/Proof/AbiClass.lean`). S11e3 switches
the function's own entry/return lowering to the typed placement, S11e5 the calls (see S11e3
below), with the FP-register `ArgsIn`/callee/link contracts; floats are not left excluded from
calls.

**S11e3 (class-aware value map, typed entry/return).** `buildCtx` admits `f32`/`f64` values
(`valTyOk`) and maps each to `.vreg x t.valClass`; `sigArgs` admits `f32`/`f64` parameters, so
the entry places them per class (`paramLocs`/`argLocsC`: v0..v7, stack-passed ones loaded by
`stackArgLoad`, `ldr s`/`ldr d` into a float vreg) and `gen_return` returns them per class
(`retRegsC (regsClasses rss)`, at most 8 values in all, so the size tables are unchanged).
Witnesses: `FVTest/Backend/AbiTyped.lean` (`(f64, i64, f32) -> f64` lowers to args
`v0, x0, v1` and return `v0`) and `E2E.argsIn_sigFIF` (`ArgsIn` of that signature through
`E2E.argsIn_iff_of_locs`). **Interim, to be lifted by S11e5: calls stay integer-only.**
`instData` rejects a `call`/`call_indirect` whose signature has an `f32`/`f64` parameter or
return, and `exnTableOpnd` a `try_call`/`try_call_indirect` with one (`sigIntB`); the
totality scope says so (`stmtInB`'s `call`/`call_indirect` cases and `tryInB` gain `sigIntB`).
S11e5 types `gen_call_args`/`gen_call_output`/`gen_call_rets`/`gen_try_call_rets`
(`tryRegsOf`) and the FP call contracts, then drops `sigIntB`. Also interim: the loop
simulation's driver model (`DriverCheck`) is integer-shaped, so `loop_run`/`lowerFunction_run`
take `Compile.functionE f` (still integer-only, so no theorem's scope admits a float value
yet), and Stock's `buildCtx` rejects float values (`f32/f64 value`) until it gets a float path.

**S11e4 (ISLE float data-movement roots).** The float roots of `lower` are proven over the
float-capable context `CtxInvT` (class-aware vregs, `f32`/`f64` types, `IntPos` for the
operands in integer positions, `intArgs`), as variant targets beside the unchanged integer ones
(`docs/contracts/backend-proof.md`, "Float data movement"): `lowerRulesCorrectT_program :
LowerRulesCorrectT program` covers `f32const`/`f64const` (584/585: `fmov s/d, #imm`, `movi` for
zero), `bitcast` (1080/1083/1084/1085: `fmov` between the register files, or no code) and the
float arm of `select` (971: the condition's flag instruction, then `fcsel`, through the
`CtxInvT` variants of the integer condition chain, `IselCmp*`); `memRulesCorrectRT_program :
MemRulesCorrectRT program` covers `load.f32`/`load.f64` (1047/1048: `ldr s/d`) and `store` of an
`f32`/`f64` (1073/1074: `str s/d`) under the new obligation `MemRefinesFP`. The integer
`lowerRulesCorrect_program` takes the float-move roots from the `T` theorems (`.toOk`);
`memRulesCorrectR_program` keeps the float memory roots vacuous on `CtxInv` contexts.
Non-vacuity: `Driver.ctxOkT`/`ctxOkT_sound` decide `CtxInvT`, checked on `buildCtx`'s contexts of
a `select.f32` and a `load.f32`/`store.f64` function (`FVTest/Backend/FloatCtxT.lean`, where
`lower` fires 971/1047/1074); `E2E.csemGF` (`FV/E2E/GuardedFP.lean`), `csemG` with the guarded
float accesses as their Arm runs (`RegallocMemFP.execMInst_fpuLoad`/`execMInst_fpuStore`),
satisfies `Refines`, `MemRefinesR` and `MemRefinesFP`. Instruction selection matches Cranelift's
for the same CLIF (`FVTest/Backend/FloatMove.lean`, Cranelift filetests `select.clif`,
`constants.clif`, `bitcast.clif`), and the Lean backend's code runs as Cranelift-native's does
under qemu: `scripts/lean-backend-filetests.sh FVTest/Backend/float_move.clif` gives 17 runs,
17 pass, 17 agree with Cranelift-native, and the
object's `.text` is byte-identical to `llvm-mc`'s. Its functions have integer signatures, since
`ctlCheck` keeps `args`/`rets` integer until S11e5. **Interim, S11e5:** no consumer takes the `T`
targets yet (driver and end-to-end theorems keep `CtxInv`/`Compile.functionE`); the
literal-pool `f64const` (`emit_u64_le_const`) is not modelled, so such a function is reported
unsupported.

**S11e5 Stage C slice 4 (FP memory bridge, GF lockstep).** `csem`'s specification fallback
`mspec` has the scalar float load/store arms (as `fspec` states them), so `csem` itself refines
the float accesses on every world (`csem_fpuLoad`/`csem_fpuStore`, `memRefinesFP_csem`);
`csemGF` is a sub-semantics of `csem` (`csemGF_sub`) extending `csemG` (`csemG_csemGF`), with
`csemG`'s pinned call contracts, and its runs go in lockstep (`csemGF_lockstep2`;
`FV/E2E/GuardedFP.lean`). On pairs of worlds: `guardedStepF`/`guardedStep0F` and the guarded
simulation composition of a statement / `try_call` from per-step `csemGF` contracts
(`lowerInstOk_pair_of`/`lowerInstOk_pairF`, `lowerTryOk_pair_of`/`lowerTryOk_pairF`;
`FV/E2E/GuardedFPPair.lean`), with `instCalls_pair`, `tryCalls_pair`, `tryIndCalls_pair` as
instances (`…_viaF`, the integer contracts lifted by `LowerInstOkP.sem_ext`/`LowerTryOkP.sem_ext`);
the same for the shipped value semantics (`valueSemGF`, `valueSemGF_lockstep2`,
`lowerInstOk_pairF_value`, `instCalls_pair_value_viaF`; `FV/E2E/DeadCleanupGuardedFP.lean`).
Witnesses: `FV/E2E/GuardedFPWitness.lean`. The typed per-step contracts (`T` dispatch at
`CtxInvT`) and the typed driver that consumes the composition are slices 2/3/7.

**S11e5 Stage C, slices 1-2 (typed scope, typed context, typed driver model).** Variants beside
the integer ones; no public scope changes. `Compile.functionET` (`FV/Compile/SubsetT.lean`) is
subset E with `f32`/`f64` (`tyM`) only for data movement: `f32const`, `f64const` without the
literal pool (`f64PoolFree`), float `load`/`store` (plain ops), float `select`, `bitcast`, block
parameters, the signature; integer operations keep `tyE`, externs keep integer signatures, and
the operands in integer positions (`intOperands`/`termIntOperands`, `intArgs_eq_intOperands`) are
never float-defined values (`floatDefs`, `opsTypedT`); `functionET_of_functionE`. On it
(`LowerScopeT`, `LowerScope.toT`) `buildCtx` gives `ctxOkT`, `CtxInvT` and the separate
supported-instruction fact `InstScopeT` (`buildCtx_typed`, `Proof/LowerLoopCtxT.lean`; `intOps`
comes from the typing check), and `ctxOkT` decides `CtxInvT` (`ctxOkT_complete`, `ctxOkT_iff`).
`Proof/DriverCheckTy.lean` models `lowerFunction`'s class-aware driver: result copies
(`extraOfT`), entry `Args` pairs and `stackArgLoad`s (`preT`), block parameters, branch and
`try_call` normal-return arguments (`vregOf ctx x = .vreg x (valClassOf ctx x)`,
`normArgRegT`), the validator `lowerCheckT` (`shapeOkT` with `ctxOkT`/`instScopeOk`,
`entryOkBT` with v0..v7) and `LowerShapeT`, with `loweringT_of_check`; on integer contexts the
typed model is the integer one (`*_int`, `lowerShapeT_of_lowerShape`, `lowerShape_of_lowerShapeT`,
`lowerCheckT_of_lowerCheck`). Witnesses: `FVTest/Backend/FloatDriverT.lean` (float parameters,
loads/stores, constants, `select`, `bitcast`, float block parameters and edge arguments,
stack-passed `f64`/`f32`: in `functionET`/`LowerScopeT`, accepted by `lowerCheckT`, rejected by
`lowerCheck`).

**S11e5 Stage C, slice 3 (typed loop simulation, typed `Low`, edge classes).** `buildCtx` gives
every value `vregOf ctx x` (`CtxSpec.regEqT`), so the loop simulation over the typed model needs
no premise: `loop_runT`, `lowerFunction_runT` (`Proof/LowerLoop{Run,Sim,}T.lean`: the VCode is
`vcBlocksOfT f ctx bl`, typed raw blocks `rawBlockT` and edge blocks `edgeBlocksT`, with
`LoopFactsT`), and the integer `lowerFunction_run` follows on integer contexts
(`lowerFunction_run_of_runT`, `vcBlocksOfT_int`, `LoopFactsT.toInt`). `shapeOkT_complete` /
`lowerShapeT_of_lower` (`Proof/LowerShapeOkT.lean`) give `LowerShapeT` on SSA `LowerScopeT` input
with well-founded aliases, given that the terminator rules emit code (`TermEmitsT`; on integer
contexts `termEmitsT_of_ctxInv` from `term_emits`, so `shapeOkT_complete_int` has the integer
premises only). `Spill.LowT`/`lowT_of` (`Proof/SpillEdgesLowT.lean`, no premise) carry the label,
position, target and edge facts (`LowT.edge_facts`: arguments are vregs of any class);
`Low.toT`/`LowT.toLow` on integer contexts. `Compile.functionET` now also checks edge classes
(`edgeClassOk`: branch arguments, a `try_call`'s value arguments and returned values have the
class of their target parameter/return, `defFloats`, `argClassOk`), with `CtxSpec.edgeClass`,
`tryEdgeClass`, `retClass` in `buildCtx`'s context. Witnesses: `FVTest/Backend/FloatLoopT.lean`.
The open terminator and completeness items are closed by the next entry.

**S11e5 Stage C, slice 3 completion (typed terminator shapes, typed `lowerCheckT_complete`).**
The terminator rules run over float-capable contexts (`Proof/IselTermFactsTy.lean`: a `return`
pins values of either class, `lower_return_okTy`; a `brif` condition and a `br_table` index are in
integer positions, `TermIntPos`, from `Compile.termIntOperands` via `opsTypedT`;
`term_emitsTy`, `termShape_runTermTy`, `branchShape_runTermTy`, `jumpShape_runTermTy`), so
`shapeOkT_completeT`/`lowerShapeT_of_lowerT` need no terminator premise and `LowT.raw_back`
holds on the typed scope. The root rules outside the closure cannot match an instruction of a
float-capable context (`Proof/IselExclT.lean`, `lower_nonroot_nomatchT`): the checker `failsT`
widens value and result types to `mCTys` and keeps the opcode/result-type correlation (a float
result has a float-movement opcode, `floatOps`, `inst_split`), which excludes the float
`bnot`/`band`/`bor`/`bxor` rules, and it reads a `bitcast`'s operand (`bitcast_i128_simdfp`).
On that, the flow and TLS analyses (`Proof/IselFlowT.lean`: `flowModelT`, `stmt_flowT`,
`stmt_noTlsT`, `termCall_noTlsT`, `tryCall_noTlsT`), the certificate (`Proof/LowerCertT.lean`:
`alias_factsT`, `certOk_completeT`), the outgoing area (`Proof/IselTermFactsCallT.lean`:
`callOut_runTermT`, `tryOut_runTermT`, arguments in integer positions) and the entry locations
(`entryOkBT_of`, any classes) give `lowerCheckT_complete` (`Proof/LowerCompleteT.lean`:
`Dominated f → LowerScopeT f → lowerFunction f = .ok vc → lowerCheckT f vc = true`).
Witnesses: `FVTest/Backend/FloatTermT.lean` (`fMv`, a float `br_table` function and a float
function with an integer `call`; `lowerCheck` rejects all three). Open (slice 6): typed
`ClassesHyp` and the spill chain (`stmt_cls`/`stmt_cov`/`termCall_cls`/`tryCall_cls` over
`CtxInvT`, `SpillEdges*`, `SpillDefined`, `SpillAvail`, `SpillLocalPipe` over `LowerScopeT`).

**S11e5 Stage C, slice 6 (typed spill chain; FP spill slots unchanged).** Over `LowerScopeT`:
CFG facts `Spill.edgesHyp_ofT`/`lowOk_ofT`/`prepDomain_ofT` (`Proof/SpillEdgesT.lean`; branch and
`try_call` value arguments have their parameter's class by `edgeClassOk`; a `try_call`'s
`ret`/`exn` arguments go to integer parameters by the new input check `Compile.tryArgClassOk`,
`FV/Compile/TryArgClass.lean`, true on subset E), classes `Spill.classesHypT`
(`Proof/SpillClassesT.lean`: `stmt_clsT`, `termCall_clsT`, `resolve_clsT`; premise `ResClassOk f`,
decided by `resClassOkB`: the lowering returns each result in a vreg of the result's class),
local facts and acceptance `spillLocalOk_of_pipelineT`, `spillAcceptedT`,
`allocChecked_allocResultT` (`Proof/SpillLocalPipeT.lean`) with explicit per-function premises
`hctl` (slice 5; decided by `ctlSpillB`, `Proof/SpillInstCheck.lean`), `hform : FormsCovered
default vcp` (decided by `formsCoveredB`) and `killFreeB vcp`. Integer corollaries:
`classesHyp_of_T`, `edgesHyp_of_toT`, `spillLocalOk_of_pipelineT_int`. Witnesses:
`FVTest/Backend/FloatSpillT.lean`. Open: a typed coverage analysis (`formsCovered_completeT`:
`IselCov*`'s `aext`/`actor`/`ext_sound`/`ctor_sound` and `covTab` are integer by construction;
shared with slice 5 as `IselCovT`), `ResClassOk` from it, and the typed kill-free chain
(`KillRunsHyp`/`TryDefsExact`/`killFreeB_lower` over `LowT`, which needs slice 5's typed
`try_call` exclusion).

**S11e5 Stage C, slice 7, composition (FloatsC7D: typed contracts, driver, Main/Final).** The
typed obligations (`Proof/LowerContractT.lean`): `CtxT f ctx` (`CtxInvT`, `InstScopeT`, integer
externs; `CtxInv.toCtxT`); statements on subset-E instructions of a typed context
(`LowerRulesCorrectTI`, `MemRulesCorrectRTI`, `CallRulesCorrectT`, `IndRulesCorrectT`) and
`NonEUnmatchableT` (on the other typed-scope instructions only the float roots match);
terminators `LowerTermOkT` (a `return` puts value `x` in the next return register of its class
`valClassOf ctx x`: `retRegsT`, `retRegsC_eq`), `LowerTermRulesCorrectT`, `BranchRulesCorrectT`,
`TryRulesCorrectT`, `TryIndRulesCorrectT` and the four unmatchability Props; dispatchers
`lowerInstOk_runTermT` (with the proven `LowerRulesCorrectT`/`MemRulesCorrectRT`/
`LowerRulesCorrectFT` and `lower_nonroot_nomatchT`), `lowerTermOk_runTermT`, `branchOk_runTermT`,
`tryOk_runTermT`, `tryIndOk_runTermT`; the driver's calls of one context `InstCallsT`/
`TermCallsT`/`TryCallsT`/`TryIndCallsT` with `*_of_rules` and integer `.toT`. The typed driver
(`Proof/LowerSimT.lean`): `MatchT` (at `posT`, tracked values typed: `TypedA`), `DriverHypT`,
`stmt_stepT`, `term_stepT` (returns: `RetRegsOk`, the values' type classes, and the return
types), `term_step_tryT`, `entryLoads_runT` (an `ldr s`/`ldr d` under `MemRefinesFP`),
`entry_stepT` (class-aware `Args`, `argPairsT`), `sim_runT`, `driver_correctT`;
`DriverHyp.toT`. Composition (`E2E/ComposeT.lean`): `IselSimT`, `ArmRefinesT` (returned value
`j` held by the `j`-th return register of the values' classes: x0.. integers, v0.. floats),
`backend_correct_of_layers_exT`/`T`; for integer returns `backend_correct_of_layers_ex_ofT`
and `ArmRefinesT.toArmRefines`. Main/Final (`E2E/MainT.lean`, `E2E/FinalT.lean`,
`E2E/FinalDirectT.lean`): `InSubsetT`, `CompiledT`/`CompiledAT` (`lowerCheckT`),
`loweringObligationsT_of_check`, `iselSim_of_driverT`, `argsAtEntry_bodyT` (x0–x8/v0–v7),
`iselSimT_of_rules`, `backend_correct_of_rules_exT`/`T`, and at `csem` (`memRefinesFP_csem`)
`backend_correct_m4_exT`, `backend_correct_final_exT`, `backend_correct_finalT` under
`TypedRules` (the 13 open typed families); integer specialization `backend_correct_final_ofT`
(`backend_correct_final`'s premises and conclusion through the typed chain);
`CompiledAT.of_lowerT`, `backend_correct_finalT_alloc` (slice 6's `allocChecked_allocResultT`,
decided premises `arityOkB`, `tryArgClassOk`, `resClassOkB`, `ctlSpillB`, `formsCoveredB`,
`killFreeB`). Witness `FVTest/E2E/FloatFinalT.lean`: `fW` (float `load`/`f64const`/`select`/
`store`/`bitcast` between integer parameters and return) has `InSubsetT`, `CompiledT`,
`CompiledAT` (also via `CompiledAT.of_lowerT` with the spill allocation) and `FormsCovered`;
`fMv` (float parameters/return) has `InSubsetT`, but `lowerRFunc`'s `ctlCheck` rejects it until
slice 5 widens `ctlInstOk`. The dead-cleanup route (`E2E/DeadCleanupT.lean`):
`CompiledCleanupT`/`AT`, `backend_correct_of_rules_cleanup_exT` (`prune_correct`), at `valueSem`
(`memRefinesFP_valueSem`) `backend_correct_m4_cleanup_exT`, `backend_correct_final_cleanup_exT`/
`T`, integer specialization `backend_correct_final_cleanup_ofT`; witness `compiledCleanupT_w`.
Two-world entry: `entry_step2T`. The open items of this paragraph are closed or narrowed by the
next one.

**S11e5 Stage C, slice 7, store typing, integer roots, world and input scope (FloatsC7I,
`agent/floats-c7`).** *Store typing* (the false premise of the earlier typed final theorems):
the integer `store` roots 1064–1067 dispatch on the stored value's type, so `NonEUnmatchableT`
now takes `StoreTyped ctx inst` (a float `store` stores a float-typed value; one definition, in
`Proof/LowerContractT.lean`, with `StoresTyped`, `storeTyped_of_instE`, `CtxInv.storesTyped`),
decided per function by `Compile.storeTypedB` (`FV/Compile/StoreTyped.lean`: `storeTypedB_sound`,
`storeTypedB_of_functionE`) and linked to `buildCtx` by `storesTyped_of_buildCtx`; the check is
the new field `InSubsetT.storeTyped` (`InSubset.toT` derives it from `functionE`, so the integer
specializations keep the integer premises), threaded through `lowerInstOk_runTermT` →
`instCallsT_of_rules` → `iselSimT_of_rules`. FloatsC7F's integer roots over typed contexts are
proven and plugged in: `lowerRulesCorrectTI_program` (`Proof/IselLowerAllTI.lean`),
`memRulesCorrectRTI_program` (`Proof/IselMemAllTI.lean`), `nonEUnmatchableT_program`
(`Proof/IselNonETI.lean`). At FloatsC5's request the branch/`try_call` families take
`TermIntPos ctx t` (a `brif` condition, a `try_call`'s callee and arguments are in integer
positions; `termIntPos_of_functionET`, `DriverHypT.termIntPos`). `TypedRules` is now the ten
control families, its call families in the pinned form of the two-world driver
(`Proof/LowerContractTP.lean`: `CallRulesCorrectTP`, `IndRulesCorrectTP`, `TryRulesCorrectTP`,
`TryIndRulesCorrectTP` with `*_of_P`, dispatchers `lowerInstOkP_runTermT`, `tryOkP_runTermT`,
`tryIndOkP_runTermT`). *World and non-interference*: `E2E/LinkWorldT.lean`
(`driverHypT_relW_of`, `iselSim_relWT`, `backend_correct_worldT`: returns in their classes'
registers, `RetRegsOk`, with the return types; `armRefinesT_of_actRet`), `E2E/PairDriverT.lean`
(`instCalls_pairT`/`tryCalls_pairT`/`tryIndCalls_pairT` from the pinned typed contracts at
`csemGF`, `termCalls_pairT`, `vcode_niT` on `entry_step2T`, `backend_correct_world_niT`),
`E2E/DeadCleanupPairT.lean` (the `valueSem` forms through `valueSemGF`), `E2E/CompiledEitherT.lean`
(the per-state `X` forms, `CompiledEitherT`, `CompiledEither.toT`, the four pipeline dispatches).
*Typed input scope*: `E2E/LinkScopeDefsT.lean` (`lowerScopeTB`, `lowersTB` with `ctlSpillB`/
`formsCoveredB default`/`killFreeB`, `fnScopeTB` with `storeTypedB`/`tryArgClassOk`/
`resClassOkB`, `InScopePT`), `E2E/LinkScopeT.lean` (`lowerScopeT_of`,
`lowerScopeTB_of_lowerScopeB`, `inSubsetT_of_fnScopeT`, `allocChecked_of_fnScopeT`,
`compiledAT_of_fnScopeT`, `compiledT_of_fnScopeT`, `backend_correct_finalT_scope`).
`InScopeIn`/`fnScopeInB`/`compileExe` are unchanged. Witnesses: `FVTest/E2E/FloatFinalT.lean`
(`storeTypedB` of `fW`/`fMv`; `fBadStore`, a float store of an integer value, is rejected),
`FVTest/E2E/FloatLinkT.lean` (`StoresTyped`, `TermIntPos`, `CompiledEitherT`, `fnScopeTB fW` and
its consequences, `lowerScopeTB_of_lowerScopeB`). Open: the ten control families (FloatsC5; now
proven, slice 5c: `typedRules_program`);
`Link.compileExe_correctT` needs a typed port of the link induction (`LinkSys.Ok` has
`subset : InSubset`, `compiled : CompiledEither`, and `LinkSys.Thm` fixes `us.map (·.2)` to
x0, x1, …): a `LinkSysT` beside it (FV/E2E/LinkArmT.lean, LinkGoodT.lean, …) with `InSubsetT`,
`CompiledEitherT`, `RetRegsOk` in its `Thm`, program callees integer-signature (`declSigB`, calls
integer-only in `functionET`) so call sites keep x0..; `functionET` still excludes float calls and
the S11f arithmetic.

**S11e5 Stage C, slice 5a (float `Args`/`Rets` in `ctlCheck`).** The executable control-form
check `ctlInstOk` (`FV/Backend/Regalloc.lean`) accepts class-compatible `Args`/`Rets` pairs
(`argPairOk`, `retPairOk`: an `f32`/`f64` vreg in v0–v7, an int vreg as before), so a function
with float parameters or returns is no longer rejected by `lowerRFunc` ("control-form check
(ctlCheck) failed"); everything else stays int-vreg only. Old acceptance implies new
(`ctlInstOk_of_int`, `ctlCheck_of_int` over the kept `ctlInstOkInt`/`ctlCheckInt`). The
register-level `Args`/`Rets` proofs (`realizes_args`, `ret_machine`) run on class-general pairs
(`argPairsC`, `operands_argsC`/`operands_retsC`, `rets_usesC`), so the register-level and E2E
statements are unchanged; only d8–d15 (`keep`) are claimed preserved across calls. Witness:
`FVTest/Backend/FloatCtlT.lean` (`(f64, i64, f32) -> f64`: widened check accepts, integer check
rejected; `Dominated`, `LowerScopeT`).

**Slice 5b (typed control-form facts, parts).** `Proof/SpillCtlFormsT.lean`:
`spillInstOk_retsC`/`spillInstOk_argsC` (float `Rets`/`Args` pairs fixed to v0–v7, x0–x8 for
int, meet `Spill.SpillInstOk`; v0–v7 are outside `calleeSaved`). `Proof/AbiClassRegs.lean`:
`sigArgLocs_regsC` (the typed placement's registers are distinct and each parameter's is x8 for
`sret` or of its class) and `spillInstOk_entryArgsT` (the typed entry `Args`). `functionET`
does not check that the entry block's parameter types are the signature's (a CLIF-verifier
fact): `Proof/EntryClass.lean` states it (`EntryClassOk`) and decides it on the input
(`entryClassOkB`, `entryClassOk_of`); witness `FloatCtlT.entryClassOk_fCtl`. Parent decision:
the typed chain takes the control-form/form-coverage/kill-free/class facts as run-time-decided
premises (`ctlSpillB`, `formsCoveredB`, `killFreeB`, `resClassOkB`, `entryClassOkB`), like
`lowersB` in `fnScopeB`. **Follow-up (input-only totality for floats):** proving those facts for
every typed-scope input needs the V3/V4 abstract interpretations over `CtxInvT`. Their soundness
is tied to E in the engine itself: `aPrune` prunes with the E exclusion checker `fails`, `γ`'s
`.xv .data` means an `instE` instruction's data, `value_type` gives `eCTys`, and `put_in_reg`
gives an int vreg (`IselCovSem`, `IselCovCheck`, `IselCovExt`, `IselCovFns`, `IselCovCtor`). The
follow-up is a parametrised copy of the engine (`IselCov{Dom,Sem,Le,Form,Check,Sound,Fns,Ext,
Ctor}`, about 3.5k lines) with a typed domain (pruning by `failsT` over `AVT`; a value kind for
operands in integer positions, from `CtxInvT.intOps`: every `InstructionData` variant of the
typed scope except `Ternary` (`select`), `Store`, `LoadNoOffset` (`bitcast`, `atomic_load`) and
the calls has all its values in integer positions, so `put_in_reg` of such a field is an int
vreg; float forms such as `fcsel` need the dual float fact, which needs the verifier's operand
typing of `select`/`store`/`bitcast`), regenerated `shpTabT`/`covTabT` with kernel
certificates (about 7 min, 3 GB each, as `shpTab`), the extern soundness over `CtxInvT`, the
hand-checked call/`try_call`/`br_table` rules over `CtxInvT` (`IselShp{Call,Try,BrTable}`, about
1k lines), and `iselCtlHypT`: several days of work.

**Slice 5c (the ten typed control families, FloatsC5R).** `TypedRules` holds for the exported
program: `E2E.typedRules_program` (`E2E/TypedRulesProg.lean`), so every `hT : TypedRules`
premise of the typed final, dead-cleanup, world and scope theorems is discharged. The proofs are
the integer ones (`IselCtl*`) over `CtxT`: `Proof/IselCtlUnmatchTI.lean` (`termUnmatchableT_program`,
`branchExcludedUnmatchableT_program`, `tryUnmatchableT_program`, `tryIndUnmatchableT_program`:
format arguments only), `Proof/IselCtlTermTI.lean` (`trap_ruleOkT`, `ret_ruleOkT`: `return` pins
value `x` to the next return register of `valClassOf ctx x`, `mapM_valueRegT`, `retRegsC_eq`,
class-general `rets` over `argPairsC`; `lowerTermRulesCorrectT_program`),
`Proof/IselCtlCallTI.lean` (`call_bl_ruleOkT`, `call_got_ruleOkT`, `call_ind_ruleOkT`: arguments
and callee integer vregs by `CtxInvT.intOps` (`mapM_valueRegTI`), integer returns by
`CtxT.resTysE` (`CtxT.call_retClasses`); `callRulesCorrectTP_program`, `indRulesCorrectTP_program`
and the unpinned `callRulesCorrectT_program`, `indRulesCorrectT_program`),
`Proof/IselCtlBranchTI.lean` (`brif`, `tbnz`, `tbz`, `jump`, `br_table` on `TermIntPos`
operands: `is_nonzero_cmp_okT`, `ExtOut.semT`, the `band` operand by `CtxInvT.intOps`;
`branchRulesCorrectT_program`), `Proof/IselCtlTryTI.lean` (`try_bl_ruleOkT`, `try_got_ruleOkT`,
`try_ind_ruleOkT` on `TermIntPos` arguments; `tryRulesCorrectTP_program`,
`tryIndRulesCorrectTP_program`, `tryRulesCorrectT_program`, `tryIndRulesCorrectT_program`).
Witnesses `FVTest/Backend/FloatCtlRulesT.lean`: typed, non-integer contexts of `fCtl` (the
terminator families give `TermCallsT`; `return v0` of an `f64` is in v0), `fCall` (the `call`
and `call_indirect` roots fire on subset-E calls between float values) and `fTry` (an integer
`try_call` with `TermIntPos` in a function with float values). With slice 5a's widened
`ctlCheck`, the float-signature witness `fMv` (float parameters, return and block parameters) now
has `CompiledT`/`CompiledAT` and `FormsCovered` (`FVTest/E2E/FloatFinalT.lean`: `compiledT_mv`,
`compiledAT_mv`, `formsCovered_mv`); `regLevelCorrect_backend_ex` is unchanged (its `Args`/`Rets`
steps run on class-general pairs since slice 5a). `entryClassOkB` is not in the typed scope: no
theorem of the typed chain consumes it (a mismatched entry `Args` pair already fails `ctlCheck`
and so `lowerRFunc`); it becomes a premise with the typed control-shape analysis (`iselCtlHypT`,
slice 5b follow-up). Open: `SpillCtlCheck`/`DeadCleanupCtl` rebuild needs `IselShpTotal`
(about 7.7 GB).

**Slice 8, typed link layer (FloatsLinkT; built).** Completeness of the typed spill chain's
control-form decider: `Proof/SpillInstCheckComplete.lean` (`opsOkB_of_opsOk`,
`spillInstOkB_of_spillInstOk`, `ctlSpillB_of`; witness `FVTest/Backend/SpillInstCheckCompleteW.lean`).
The link/binary/exec layers have typed copies (`FV/E2E/*T.lean`: `LinkArmT`, `LinkCheckT`,
`LinkGoodT`, `StackBoundT`, `BinCheckT`, `BinaryT`, `BinaryGoodT`, `ExecBytesT`, `ExecStaticT`,
`ExecRunNT`, `ExecGoodRunT`, `ExecGoodReadsT`, `ExecGotT`, `ExecProvenT` and the `DeadCleanup*T`
versions), generated from the integer modules by their constant dependencies and patched by hand:
`LinkSys.OkT` (`InSubsetT`, `CompiledEitherT`; an `sret` function in subset E keeps the integer
contract; program callees return integers, `calleeInt`), `LinkSys.ThmT` with `RetsOkT` (returns
by class, x0.. for `sret`), `LinkGoodT` on the typed world theorems with `E2E.typedRules_program`,
`ExecRefinesT` (`ExecBytesT`: the returned values in the ABI return register of their class;
`ExecRefinesT.toExecRefines` on integer returns), and the typed checker `okRWithT`/`okRWith_soundT`
(`PipelineCheckT`) for both pipelines. Theorems: `Link.compileExe_correctT` (`_depthT`, `_peakT`;
`FV/Link/ExeT.lean`) and `Link.DeadCleanup.compileExe_correctT` (`FV/Link/DeadCleanupExeT.lean`):
for `leanLink S file0 = .ok file` on `InScopePT S.input` with the decided output checks `OutOkT`
(`OutOkTCleanup`; `FV/E2E/LinkOutT.lean`, `LinkOutCleanupT.lean`: `checkAlloc`'s verdict, form
coverage with the artifact's frame, `sretRets`, `entryRegs`, `outFits`, call sites, facts whose
completeness is proven only for subset E), the executable machine run of `file`'s words refines
the whole-program CLIF run with `ExecRefinesT`; no rule-family premise. Integer corollaries
`compileExe_correct_viaT` (`_depth_viaT`, `_peak_viaT`, `DeadCleanup.compileExe_correct_viaT`)
re-derive the conclusions of `Link.compileExe_correct*` from their exact premises
(`FV/E2E/LinkScopeIntT.lean`: `inScopePT_of_inScopeP` from `resClassOkB_of`, `ctlSpillB_of`,
`formsCovered_complete`, `spillKillFree`; `outOkT_of_inScopeP`/`outOkTCleanup_of_inScopeP` from
`chks_resultsT`). Witness `FVTest/Link/FloatExeT.lean`: a linked program of `%w` (float load,
constant, `select`, store, `bitcast`) and `%mv` (`(f64, i64, f32, i8) -> f64`, float block
parameters) is in `InScopePT`, passes `OutOkT`/`OutOkTCleanup` and links with both pipelines, so
both typed theorems apply; `viaT_baseline` on the integer executable witness. Audit
`scripts/audit/floats-typed.lean`.

**Public scope, backend (per function).** `lean-backend` (and so `cargo fv`) reports a
function outside subset E verified when it is in the typed scope `Backend.verifiableT`
(`Compile.functionET` with `storeTypedB`, `abiSigs`, `indSigsOk`; `unverifiedReason?`) and its
lowering passes the typed validator (`Backend.lowerCheckFor`: `lowerCheckT` outside subset E);
the theorems are `backend_correct_finalT`/`backend_correct_final_cleanupT` with
`E2E.typedRules_program` (`FV/E2E/VerifiableT.lean`: `InSubsetT.of_verifiableT`,
`verifiable_or_verifiableT_of_unverifiedReason`, `lowerChecked_spec`; witness
`FVTest/E2E/FloatVerifiedW.lean`). Next: the executable compiler's gate for plain `lean-link`
(`Link.DeadCleanup.compileExeT`: `InScopePT` + `OutOkTCleanup` with
`Link.DeadCleanup.compileExe_correctT`). Decision (parent, 2026-10-22): `lean-link --verified`
stays integer-only — its claim reaches the Rust source through front-end theorems
(`Front.bundle_correct_raw*`) that exist only for integers; only plain `--lean-link` widens.

**Slice 8, totality half (typed input scope, FloatsTotT).** `E2E/LinkScopeInputDefsT.lean`:
`fnScopeInTB` keeps every conjunct of `fnScopeInB` over the typed scope (`functionET`,
`lowerScopeTB`) with `fnScopeTB`'s input checks `storeTypedB`/`tryArgClassOk`; a function outside
subset E must also meet `resClassOkB` and the run-time decider `lowerOutTB` (`lowerFunction`
succeeds; `ctlSpillB` of its output; `emitCondsB`, `formsCoveredB default` and
`ctlInstsB` — `ctlInstOk` everywhere, `Args` first in block 0 — of `prepare`'s output), i.e. what
the typed chain does not prove yet; `InScopeInT`, `fnScopeInFailsT`. Literal-pool `f64const`
stays outside by `functionET`'s `f64PoolFree`. Proven: `Prep.prepare_okT` (`prepare` is total on
`Dominated`/`LowerScopeT`: `trap_shapeRT`/`ret_shapeRT`/`termShapeR_runTermT`, `raw_termT`,
`prepIn_of_lowerT`; `Proof/PrepareTotalT.lean`), the allocation/emission half on the typed
pipeline (`E2E/EmitTotalT.lean`: `emitReady_spill_of`, `lowerAllocReady_emit_of` from
`PrepDomain`, `AllocChecked`, `FormsCovered`, `CtlInsts` and `emitCondsB` alone;
`lowerRFunc_spillAllocT`, `backend_total_emitT`), and in `E2E/LinkScopeInputT.lean` the integer
inclusion `fnScopeInTB_of_fnScopeInB` (no extra premise) with its converse on subset E
(`fnScopeInB_of_fnScopeInTB`), `fnScopeTB_of_inT` (outside E the typed input scope is in
`fnScopeTB`, so `backend_correct_finalT_scope` applies), and **`pipeT_okT`**: `pipeT` succeeds on
every function of `fnScopeInTB` for every allocator answer, with `lowerCheckT`, `prepCheck`,
`AllocChecked` and `FormsCovered`; `resultsT_ok_inT` (crates), `resultsT_ok_input` (the integer
conclusion re-derived). Witnesses `FVTest/E2E/FloatTotalT.lean` (`fW`: float load/const/select/
store/bitcast, decided in `fnScopeInTB`, compiled by `pipeT_okT`; `crateW`; integer `fInt`).
The dead-cleanup pipeline (FloatCleanupT; built): `E2E/DeadCleanupTotalT.lean` carries
`lowerOutTB`'s facts on `prepare`'s raw output `vcp` to `prepare (prune vc) = .ok (preparedCleanup
vc vcp)` with no new premise and for every rule set (cleanup deletes pure instructions only and
keeps labels, interfaces and terminators: `preparedCleanup_formsCovered`, `preparedCleanup_ctlInsts`,
`preparedCleanup_emitCondsB`), `spillLocal_cleanupT`, `spillAccepted_cleanupT` (the raw code's
`killFreeB` availability restricted by `preparedCleanup_spillAvail`), `backend_total_emit_cleanupT`;
`E2E/LinkScopeInputCleanupT.lean`: **`pipeCleanupT_okT`** (`pipeCleanupT` succeeds on every
function of `fnScopeInTB` for every allocator answer, with `lowerCheckT`, `prepCheck (prune vc)`,
`AllocChecked`, `FormsCovered`), `resultsCleanupT_ok_inT`, `resultsCleanupT_ok_input`; witnesses
`FVTest/E2E/FloatCleanupTotalT.lean`.
Remaining for `Link.compileExe_total_reach_inputT`, in order: dropping `lowerOutTB`'s
`lowerFunction` check (typed ISLE progress: done, `Prg.lowerFunction_ok_inputT` below); typed
size/emission analyses
(`iselSz`, `iselEmit`) for `emitCondsB`; completeness of `ctlSpillB`/`formsCoveredB`/
`resClassOkB` on the typed scope (slice 6's open items) and typed `vc_ctl` (control-shape
analysis) for `ctlInstsB` (`killFreeB`: done, below); `leanLink`'s per-function checks
(`chks`: `functionE`, integer `lowerCheck`, `checkAlloc` of the spill allocation) and
`compileExe`'s gate widened to `InScopeInT`, then the LinkSysT port for correctness.

**Slice 8, typed ISLE progress (FloatProg).** V7's progress analysis (`IselPrg*`) over the typed
scope, so that `lowerFunction` is total on `fnScopeInTB` without `lowerOutTB`'s `lowerFunction`
check. Merged parts: the driver half `Driver.lowerFunction_okT` (`Proof/LowerTotalT.lean`:
`buildCtx_okT`, then every premise of `lowerFunction_ok` over `LowerScopeT` but `IselProg`); the
model of the extern helpers on the typed context invariant `PInvT` (`IselPrgInvT`: `CtxInvT`, the
instructions in `instET`, integer operand positions `intArgs`/`termIntOperands`, result types,
callees): `aextT_sound`, `actorT_sound`, `aidata_soundT` (`IselPrgExtT`/`ExtSoundT`/`CtorNoneT`/
`CtorSoundT`; `emit` is checked against every float instruction the decoder knows, so new float
roots need a regenerated table, not a new model); `pinv_buildT` and its terminator/`try_call`
variants (`IselPrgCtxT`); the typed roots `stmt_rootT`/`term_rootT`/`try_rootT` (`IselPrgCoverT`,
`IselPrgCoverTermT`; `formOfT`, `stmtFormsT`, `termRootsT` in `IselPrgRootT`); V7's hand-checked
rules over `PInvT` (`handRules_okT`, `IselPrgHandT`); the `f64const` sub-table `f64Tab`
(`IselPrgTabF64`, generated by `FVTest/Backend/IselPrgGenT.lean`). `IselPrgDom` gains the operand
kinds `fpModImm`/`movModImm`. Audit `scripts/audit/floats-prog.lean`.
**Done: `Prg.lowerFunction_ok_inputT`** (`Proof/IselPrgDriverT.lean`): `lowerFunction` succeeds on
every function with `functionET`, `sigAbiOk`, `dominatedB`, `LowerScopeT` (`lowerScopeT_of` of
`lowerScopeTB`), `arityOkB`, `entryParamsB`, `extendsWidenB`, `driverInB`, `iselInB`, all conjuncts
of `fnScopeInTB`, so `lowerOutTB`'s `lowerFunction` check can be dropped. Parts: the typed table
`prgTabT` (`IselPrgTabT`, generated; 1090 entries, 68.6 min to check, `IselPrgTab` 52 min);
`iselProgT_of_input` from `stmtProgT`/`termProgT`/`tryProgT` (`IselPrgDriver`'s proof over the
typed pieces); `tryCall_lastT` (`IselPrgTryLastT`: a `try_call`'s operands are integer positions,
`termIntOperands`); and the `f64const` rule 585 by hand (`IselPrgHandF64`, `handOkT`): the
interval domain cannot see that a pattern of at least `2^32` is `f64PoolFree`, so `hand_585T`
takes the bits from the matched `f64const` of `f` (`PInvT.instET`; `prgTabT_f64Safe`: no `lower`
entry describes a slot without CLIF instruction holding `f64const` data), uses `f64Tab`'s
`constant_f64` entry below `2^32`, and from `2^32` on follows `constant_f64`'s rules
(`constant_f64_hi`: `0` and `u32_from_u64` fail, then the `fmov d` immediate or the zero low half,
whose calls are `f64Tab` entries). The proof is generic in the rules: a new float root (fcmp,
conversions, rounding) needs `prgTabT`/`f64Tab` regenerated (`lake env lean --run
FVTest/Backend/IselPrgGenT.lean FV/Backend/Proof/IselPrgTabT.lean
FV/Backend/Proof/IselPrgTabF64.lean`), and a new extern constructor a model case. Witness
`FVTest/Backend/FloatProgT.lean` (`f64const` by all three pool-free routes and float `select`,
outside subset E).

**Slice 8, typed completeness of the run-time deciders (FloatChecksComplete).** `killFreeB` is
proven on the typed scope: `E2E.spillKillFreeT` (`E2E/SpillKillFreeT.lean`: `Dominated`,
`LowerScopeT`, `AbiSigsOk`, `ArityOk`, `tryArgClassOk` → `Spill.killFreeB` of `prepare
(lowerFunction f)`) and `LinkCheck.killFreeB_of_scopeT` (from `fnScopeInTB`'s decided conjuncts
`dominatedB`, `lowerScopeTB`, `sigAbiOk`, `indSigsOk`, `arityOkB`, `tryArgClassOk`), so
`lowerOutTB`'s `killFreeB` conjunct is dropped (Floats14; `fnScopeTB_of_inT`, `pipeT_okT` and
`pipeCleanupT_okT` take it from `killFreeB_of_scopeT`). Parts: `Kill.killRunsHypT`
(`Proof/KillDriverT.lean`; the killed-vreg analysis is a uniform invariant over every root rule
of the exported program, so only its two rule exclusions, `nop` 587 and I128 636/637, are
re-proven over `CtxInvT`), `Kill.tryDefsExactT` (`Proof/KillTryDefsT.lean`; the `try_call`'s
operands are integer positions, `termIntPos_of`), `Kill.killFreeB_lowerT`
(`Proof/KillAssembleT.lean`, `KillAssemble` over `LowT`/`vcBlocksOfT`), statements
`KillRunsHypT`/`TryDefsExactT` (`Proof/KillHypT.lean`). No premise names a float root: new
roots need no new proof. Witness `FVTest/E2E/FloatKillFreeT.lean` (`fW`). The other four stay
run-time conditions: on the current typed scope (`instET`: subset E, float constants, float
`load`/`store`, `select`, `bitcast`; integer externs) they hold for every function as far as the
rules go (float roots emit `FormOk`'s float forms into float vregs, no float root emits a control
form, float `Args`/`Rets` pairs use v0–v7), but each proof needs a typed abstract interpretation
of the ISLE rules: `formsCoveredB` the V3 coverage engine over `CtxInvT` (slice 5b follow-up,
`IselCovT`), `ctlSpillB` and `ctlInstsB` the V4 control-shape engine (`iselCtlHypT`, typed
`CtlShape`), `resClassOkB` a result-class fact tied to the result type (the class model
`stmt_clsT` gives recorded classes only, and the root contracts' `ResultsHeld` leaves the class
free), which the typed coverage engine would also give (as `stmt_cov` does for subset E). A root
that emits a form outside `FormOk` (e.g. a conversion) would need `FormOk`/`covTab` widened first.

**Slice 8, the two typing gaps of the typed input scope (FloatChecks2).** Two of those four do
*not* hold on every function of `fnScopeInTB`'s other conjuncts; both gaps are CLIF-verifier
typing that the typed movement scope does not check (found by random typed-scope functions;
with both checks, every sample passed all four). (1) The entry block's parameter classes:
`function %a(f64, i64) -> i64 { block0(v0: i64, v1: i64): return v0 }` fails `ctlSpillB` (and
`ctlInstsB` when the mismatched `Args` pair survives `prepare`); the existing
`Backend.Proof.entryClassOkB` decides it. (2) Float `select` operands: `fW` with
`select.f64 v1, v0, v3` (`v0 : i64`) lowers to an `fcsel` of an int vreg and fails
`formsCoveredB`; new `Compile.selectTypedB` (`FV/Compile/SelectTyped.lean`, as `storeTypedB`).
`E2E/LinkScopeInputDefsT2.lean`: `fnScopeInTB2 := fnScopeInTB && entryClassOkB &&
selectTypedB`, `InScopeInT2`, `fnScopeInFailsT2` (`fnScopeInTB`/`InScopeInT` unchanged);
`E2E/LinkScopeInputT2.lean`: `fnScopeInTB_of_T2`, `inScopeInT_of_T2`, integer inclusion
`fnScopeInTB2_of_fnScopeInB`, `inScopeInT2_of_inScopeIn`. Witnesses
`FVTest/E2E/FloatScopeT2.lean` (`fEntry`, `fSel`: each fails exactly one run-time check and the
new typing check). `resClassOkB` never failed.

**S11e5a (typed direct calls, on top of S11e4).** The lowering of a `call` is typed as
Cranelift's: `gen_call_output` allocates one fresh vreg per ABI return of the return's class
(`machinst/lower.rs:630`, `retClass`), `gen_call_args` places arguments by `sigArgLocs`
(x0..x7 / v0..v7, separate counters) and stores stack-passed ones with `stackArgStore`
(`str s`/`str d` for a float vreg; `abi.rs:1819`), `gen_call_rets` puts outputs in the return
registers of their classes (`retRegsC (regsClasses rss)`, at most 8 in all; `abi.rs:1995`).
`instData` no longer rejects a float `call`. **Remaining interim** (parent decision): `sigIntB`
stays on `call_indirect` (`instData`) and `try_call`/`try_call_indirect` (`exnTableOpnd`):
`Compile.functionE` does not constrain `f.sigDecls`, so an indirect call with a float return
would put a float value into the integer driver model (`CtxSpec.ctxE`/`tysOf_int` →
`loop_run`), and `LowerTryOk`/`tryRegsOf`/`CallOk`/`ShapeOf` are integer-shaped. Integer proofs
get the call's integer returns from `CtxInv.call_retClasses` (results `i8..i64`) and the
externs' integer parameters from `functionE` (`handOk_call`/`stmt_shp` gain `hxi`/`hE`). The
coverage interpretation's `gen_call_output` gives an int or float vreg (`.flat 3 true`), so
`stmt_cov` checks the `call` rules' int results by hand (`IselCovCall`: `out_2508`/`out_2518`/
`out_2529`, `root_hand_res`; `covStmt_ok` excludes rules 1031..1033). Stock keeps integer calls
(its own `gen_call_output` allocates int vregs): `Cov.actorI` is the transfer function before
typed calls (`gen_call_output` gives int vregs) and `Stock.Proof.Coverage.ctor_value_sound_int`
restores that conclusion for Stock's constructors (`ctor_value_sound` keeps its statement over
`Cov.actor`; witness `ctor_value_sound_int_witness`). The checked-in 704-entry `covTab` is kept:
the generator has given 707 entries since V6c's `.num` leaves (same output on `main`), see
`FVTest/Backend/IselCovGen.lean`. Witnesses: `FVTest/Backend/AbiTyped.lean` (a call of
`(f64, i64, f32) -> f64` uses v0, x0, v1 and defines its result from v0) and a native check
against Cranelift (qemu, C callees linked: 4/4 runs agree, including a stack-passed `f64` stored
with `stur d0`).
On the Stage C typed model (slices 1-3 above), `IselTermFactsCallT`'s `call` proofs take the
outputs of either class (`ctor_gen_call_output_typed`, `outRegsC_single`), while
`Compile.functionET` still keeps extern signatures integer. Next: Stage B, typed `try_call`
(`tryRegsOf`/`gen_try_call_rets` and `LowerTryOk` with classes, `CallOk`/`ArgReg` with v0..v7
and class-matched fixed operands for the spill chain, `ShapeOf` with typed return registers for
linking); Stage C, float extern signatures in `functionET` and the typed spill chain (slice 6),
which lift `call_indirect`/`try_call_indirect` (`sigIntB`).

**S11f, first part (#239): the scalar float arithmetic roots at `CtxInvT`.** The eleven
arithmetic roots of `lower` (`floatArithRootRule`: 662 `fadd`, 664 `fsub`, 666 `fmul`, 668
`fdiv`, 670 `fmin`, 672 `fmax`, 674 `sqrt`, 676 `fneg`, 678 `fabs`, 679 `fpromote`, 680
`fdemote`; `rule_lower_485`…`rule_lower_559`) are in the closure and proven over float-capable
contexts: `LowerRulesCorrectFT p` (`IselContract`) says each is `LowerRuleOkT`, and
`lowerRulesCorrectFT_program` (`IselLowerAll`) proves it from `fadd_okT` … `fdemote_okT`
(`Proof/IselFloatArith.lean`; `fbin_holds`/`fun_holds`: CLIF's `evalFloat` and the emitted
`FpuRRR`/`FpuRR` compute the same shared-core function, round to nearest even); the integer
`lowerRulesCorrect_program` dispatches them through `(…_okT …).toOk`. The machine side: `MInst`
forms `fpuRR`/`fpuRRR`/`fpuRRRR`/`fpuCmp`/`fpuRound`/`fpuToInt`/`intToFpu` (decoding, operands,
`mapRegs`, `emitOk`, encodings), `ispecFP` (`ispec`'s fallback: `fpu2Out`, `fpu1Val`,
`fcmpOut`) with `Refines` by `ref_fpuRRR`/`ref_fpuRR`/`ref_fpuCmp` (`RefinesInsts2`) and the
regalloc `Corr` lemmas (`RegallocInstsFP`), and `RelocProvTab`'s `provTab15` (terms 364
`fpu_rr`, 368 `fpu_rrr`). The exclusion checker is generalised to `failsTG p iOps fOps`
(sound under `InstSplit S`, `failsTG_sound`; `failsT` is its typed-scope instance, statements of
`failsT_sound`/`lower_nonroot_nomatchT` unchanged) with the variant `lower_nonroot_nomatchTA`
over `InstScopeTA` (instructions in `Compile.instETA = instET ∨ fArithET`, `FV/Compile/SubsetT`;
`exclOkTA_program` by one kernel decision). Witnesses: `FVTest/Backend/FloatArithCtxT.lean`
(`ctxInvT_float_arith`: a function with all eleven operations passes `ctxOkT`; `lower` fires the
eleven roots on it; `instScopeTA_float_arith`, `float_arith_fcmp_nomatch`). Oracle:
`FVTest/Backend/float_arith.clif` (NaN propagation and quietening, signalling operand first,
default NaN, ±∞, ±0, subnormals, rounding ties) through `scripts/lean-backend-filetests.sh`.
**Deferred: `fcmp`.** `rule_lower_2176` (`fcmp` with `fp_cond_code`) is not a closure root
(`closure.rs` `BACKEND_FLOAT_ROOTS`, `Closure.lean`: 171 roots, 354 excluded), `instData`
rejects `fcmp`, and the `fcmp` arm of `is_nonzero_cmp_okT` stays absurd; `fpuCmp`'s `ispecFP`
arm and `ref_fpuCmp` are in place for it. Open: `fcmp` (the `fp_cond_code` conditions), the
conversions (`fpu_to_int_cvt{,_sat}`, `int_to_fpu`), `fma`/rounding, and threading
`LowerRulesCorrectFT`/`InstScopeTA` into the driver and the end-to-end scope.

**S11e6 (#419), slice 1: `call` with `f32`/`f64` arguments and returns in the typed family.**
`Proof/IselCtlCallF.lean`: `CallRulesCorrectTFP` (the pinned `call` family, rules 1031 `bl` and
1032 GOT + `blr`, for every extern signature) and `callRulesCorrectTFP_program`. Arguments are
passed in their values' vregs of their classes (`valClassOf`), fixed to `sigArgLocs`' locations
(x0..x7 / v0..v7, separate counters, `sret` in x8); stack-passed ones are stored by
`stackArgStore` (`str s`/`str d` for a float vreg, so the family assumes `MemRefinesFP` beside
`MemRefinesR`; `argStoresC_run`, `argsAt_after_storesC`; that a float vreg holds a float value of
byte size 4/8 comes from the frame typing, `argClasses_of_frame`); returns get fresh vregs of
their classes defined from `retRegsC`'s registers (`outDefsC`, `results_callC`). The callee
contract `CallsRefineP` is unchanged (class-agnostic). The contexts are `CallCtxT` (`CtxInvT`'s
data, result types and class-aware registers, `CtxInvT.toCallCtx`), because `CtxInvT` types every
`call` argument as an integer (`intArgs`); `callCtxOkB` decides it. `callRuleOkTP_of_TFP`: the
integer-argument family over `CtxT` is an instance. Witnesses `FVTest/Backend/FloatCallF.lean`:
`fCallF` (`%g(f64, i64, f32) -> f64`: uses v0, x0, v1, def v0 into a float vreg) and `fCallStk`
(nine `f64` arguments, the ninth `str d` at `[sp]`, an `f32` return), both `CallCtxT` and not
`CtxInvT`; their prepared code passes `ctlSpillB` and `lowerRFunc` (`ctlCheck`). Open (next slices): typed `try_call` (`tryRegsOf`/`gen_try_call_rets` by class, a
typed `LowerTryOk`), `call_indirect`/`try_call_indirect` (`sigIntB`), and plugging the families
into the typed chain (`CtxInvT`'s `intArgs` without the `call` arguments, extern signatures
`sigET` in the typed scope with an argument-class check).

## 4. Known hazards

- Proofs that derive a type from its width (`ty_i64_of_width`, width injectivity in
  `IselFamAluBBase`, `ofClif_int_width`, `mem_eTys` from `ty ≠ i128`, `RuleEmbed.tyInt_ofClif`)
  become false with f32/f64 and need an `isInt` premise, not new `cases` arms.
- `tyE t := t != .i128` and `Isel.eTy` would silently admit floats; they must test
  `isInt` until the float rules are proven.
- `Isel.argLocs` takes byte sizes only, so it cannot tell `i64` from `f64` (S11e2: the typed
  `argLocsC`/`abiArgLocs` take classes; S11e3: the lowering's `sigArgLocs` places floats in
  v registers; S11e5a: a direct `call` too, `call_indirect`/`try_call*` reject float signatures
  until stages B/C); the
  ABI change touches `ArgsIn`, callee contracts and the linking proofs (`docs/contracts/e2e.md`).
- Changing `Clif.Syntax` rebuilds everything downstream, including the heavy
  `FV.Opt.Proof.*` modules (TO-PROVE §7: serial, ≤3 at a time).
- `clif-native`'s random differential generator rejects float parameters
  (`rust/crates/clif-native/src/diff.rs`); float random diffs need it extended.
- Mid-end: `Isle.Opt` drops float nodes and leaves `zero_constant`, `f32_from_uint` unmodelled
  (`docs/contracts/isle.md`); float CLIF parsed for the first time can reach them.
