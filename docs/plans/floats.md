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
targets yet (driver, lockstep and end-to-end theorems keep `CtxInv`/`Compile.functionE`; `csemG`
leaves float accesses undefined); the literal-pool `f64const` (`emit_u64_le_const`) is not
modelled, so such a function is reported unsupported.

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
Open: `TermEmitsT` and `Low.raw_back` for float-capable contexts (the terminator rules' shapes at
`CtxInvT`: a `return` of float values, conditions in integer positions), and the typed
`alias_facts`/`lowerCheckT_complete`.

## 4. Known hazards

- Proofs that derive a type from its width (`ty_i64_of_width`, width injectivity in
  `IselFamAluBBase`, `ofClif_int_width`, `mem_eTys` from `ty ≠ i128`, `RuleEmbed.tyInt_ofClif`)
  become false with f32/f64 and need an `isInt` premise, not new `cases` arms.
- `tyE t := t != .i128` and `Isel.eTy` would silently admit floats; they must test
  `isInt` until the float rules are proven.
- `Isel.argLocs` takes byte sizes only, so it cannot tell `i64` from `f64` (S11e2: the typed
  `argLocsC`/`abiArgLocs` take classes; S11e3: the lowering's `sigArgLocs` places floats in
  v registers, and calls reject float signatures until S11e5); the
  ABI change touches `ArgsIn`, callee contracts and the linking proofs (`docs/contracts/e2e.md`).
- Changing `Clif.Syntax` rebuilds everything downstream, including the heavy
  `FV.Opt.Proof.*` modules (TO-PROVE §7: serial, ≤3 at a time).
- `clif-native`'s random differential generator rejects float parameters
  (`rust/crates/clif-native/src/diff.rs`); float random diffs need it extended.
- Mid-end: `Isle.Opt` drops float nodes and leaves `zero_constant`, `f32_from_uint` unmodelled
  (`docs/contracts/isle.md`); float CLIF parsed for the first time can reach them.
