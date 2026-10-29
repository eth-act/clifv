# M7: the end-to-end theorem `backend_correct`

The legacy-driver cleanup stage and its matching proof consumers are described in
[dead-cleanup.md](dead-cleanup.md); original theorem variants remain available.
The production lowering dispatcher enables the first structurally selected Stock
class through full-code compatibility, preserving these theorem statements and
their input conditions; see [stock-driver.md](stock-driver.md).

Additive actual-output consumers use `CompiledValidatedA`/`CompiledValidated`
(`FV/E2E/ValidatedLowering.lean`, `ValidatedWorld.lean`) and the cleanup variants
in `ValidatedCleanup.lean`. They require source/SSA validation of the actual raw
VCode, preparation validation of the actual prepared VCode, and the existing
allocation/emission/layout facts. They do not require equality with the legacy
constructor. `CompiledProduction` covers the old `CompiledEither` contract and
both validated-output modes; its world and non-interference theorems use the same
source and machine semantics. Old contracts and theorem variants remain available.
`E2E.LinkCheck.pipeTWithLowering_spec` in `LoweringProvenance.lean` binds the actual lowering callback result to every
subsequent artifact stage, allocator answer and function/base index.

The actual successful Stock contract witnesses cover all six D0 configurations,
arbitrary names, run metadata and allocator answers, in both cleanup modes
(`StockD0ActualConsumerWitness.lean`). Positive try-call and TLS helper witnesses
use concrete legacy compilations (`ValidatedWitness.lean`). These contracts are
proof interfaces, not per-program certificates. Broader Stock classes still need
fixed source-correctness proofs and downstream checker/linker/proof-writer
integration before production activation.

`LinkSys.OkProduction` in `LinkProduction.lean` retains all 38 non-compilation
fields of `LinkSys.Ok` and uses the actual-output compilation contract.
`ActualPipelineCheck`, `ActualBinCheck` and `ActualCompilerModes` bind the same
callback result table to whole-program semantics, ELF bytes and relocation facts,
including the original allocator fallback flag and k/j/base indices.
`Link.leanLinkWithLowering` writes that table with every existing byte-writer
check; exact arbitrary-input compatibility lemmas cover both old linker modes.
These APIs are additive. Actual CLI/generated-proof/stack migration and universal
prologue activation remain required. The fixed non-legacy-history prologue
witness in `ActualPrologueWitness.lean` is not a production activation proof.

Producer: M7 (agents `M7Skeleton`, `M7Driver`; branch `agent/m7-driver`). Consumers: the
integrator, M4 (rule proofs), M6 (register level). Code: `FV/E2E/{Statement,Compose,Main}.lean`
(namespace `E2E`), the CLIF → VCode driver simulation
`FV/Backend/Proof/Lower{Seq,Rename,Contract,Frame,Shape,Lemmas,Sim}.lean`, the validators
`FV/Backend/Proof/{DriverCheck,PrepareCheck}.lean` (executable) with their soundness proofs
`FV/Backend/Proof/{DriverCheckSound,PrepareSound}.lean` (namespace `Backend.Proof.Driver`), the
harness `FVTest/E2E/Check.lean` (`lake exe lean-e2e-check`). Inputs: `backend-proof.md` (M4
contract `IselContract.lean`), `regalloc-proof.md` (M6), `encoder.md` (M5), `clif.md`
(`Clif.run`).

## Status (2026-09-27)

| Piece | State |
| --- | --- |
| Statement: subset, compiled code (incl. M7's validators), CLIF entry, memory/slot relation, ABI entry, body entry (`BodyEntry`), exit, trap relation, resource precondition, conclusion `ArmRefines` | done (`Statement.lean`) |
| Composition CLIF → VCode → prepared VCode → Arm (`backend_correct_of_layers`) | **proven** |
| CLIF → VCode driver simulation (`driver_correct`: statements, returns, traps, `jump` parallel copies, `brif`/`br_table` with and without edge blocks, entry `Args`, alias resolution, DFG consistency incl. `FrameTyped`, whole runs) | **proven** from `LowerShape` + `Cert` + M4 contracts + `DriverSem` |
| `Clif.run` typing (`instOutcome_types`/`evalInst_types`: results have `Inst.resultTypes`) | **proven** |
| `IselSim` from the driver (`iselSim_of_driver`) | **proven** |
| M4 `lower` calls on statements from M4's rule theorems (`instCalls_of_rules`, via `lowerInstOk_runTerm`) | **proven** |
| M4 terminator calls `TermCalls` from M4's terminator rule statements (`termCalls_of_rules`, via `lowerTermOk_runTerm`/`branchOk_runTerm`) | **proven** |
| `MRStable` of the CLIF ↔ VCode relation (`mrStable_holds`) | **proven** |
| `Clif.run`'s initial state is a `ClifEntry` (`clifEntry_initState`) | **proven** |
| `LoweringObligations f vc` (`LowerShape` incl. `CtxInv`, `ValsBelow`, types; SSA certificate `Cert`) | **discharged**: `lowerCheck f vc = true` ⇒ it (`loweringObligations_of_check`); and without the validator on `Dominated`/`LowerScope` input (`lowerCheck_complete`, `Compiled.of_lower`; see "Validator completeness") |
| `PrepareCorrect sem vc vcp` (unreachable blocks, critical-edge splitting, RPO) | **discharged**: `prepCheck vc vcp = true` ⇒ it (`prepareCorrect_of_check`); and without the validator on `PrepDomain` VCode (`prepareCorrect_of_domain`, from `prepCheck_complete`; see "Validator completeness") |
| Validators run by the compiler (`FV/Backend.lean` `lowerChecked`, `FV/Backend/Regalloc.lean` `allocateRegalloc2`: a rejection is a compile error, except `checkAlloc`'s rejection of regalloc2's allocation, which falls back to the spill allocation, V4) | done |
| **`backend_correct`**, **`backend_correct_of_rules`** from the hypotheses below | **proven**, sorry-free |
| **`backend_correct_m4`** (`FV/E2E/Final.lean`): `backend_correct_of_rules` with all M4 predicates discharged (`lowerRulesCorrect_program`, `excludedUnmatchable`, `callRulesCorrect`, `indRulesCorrect`, `memRulesCorrect_program`, `lowerTermRulesCorrect`, `termUnmatchable`, `branchRulesCorrect`, `branchExcludedUnmatchable`, `tryRulesCorrect`, `tryUnmatchable`, `tryIndRulesCorrect`, `tryIndUnmatchable`) and `sem s := csem (F s) (ctx s) (X s)` (discharges `DriverSem` by `driverSem_csem`, `CallsRefine` by `callsRefine_csem` from `XCallsOk`, `IndCallsRefine` by `indCallsRefine_csem` from `XCallsIndOk`) | **proven**; axioms: `propext`, `Classical.choice`, `Quot.sound` (T6) |
| **`RegLevelCorrect`** for the backend's code (`regLevelCorrect_backend`, `FV/E2E/RegLevelCorrect.lean`, M6Ctl3): addresses outside the world `frameW K` (frame addresses `frameF` and, since agent/callee-fix, the callees' dead stack), context `⟨fa.k, af.slotBase⟩`, one external semantics `X`, machine `ArmStepX X H fa`; from `FormsCovered` and `CalleeOk` | **proven** |
| **`backend_correct_final`** (`FV/E2E/Final.lean`): `backend_correct_m4` with `hM6` discharged by `regLevelCorrect_backend` | **proven**; axioms: `propext`, `Classical.choice`, `Quot.sound`; every fixed backend lemma (M4/M5/M6, `Arm.Memory.read_write_bytes_different`) is kernel-checked (T6) |
| **`sret`** (2026-09-30, `agent/sret-proof`): functions with a struct-return pointer parameter and calls of `sret` callees are inside `backend_correct_final` (`InSubset.abiSigs`; see "`sret`" below) | **proven**; `lean-e2e-check`: all `sret` functions in scope accepted and covered |
| **`try_call`** (2026-09-30, `agent/trycall-proof`): functions with `try_call` of an extern are inside `backend_correct_final` **for their normal returns** (see "`try_call`" below); nothing is claimed about unwinding, landing pads or the LSDA | **proven** (`term_step_try`, `tryRulesCorrect`, `tryUnmatchable`, `realizes_tryCall`) |
| **Indirect calls** (2026-10-01, `agent/indirect-proof`): `call_indirect`, `func_addr` and `try_call_indirect` (normal return) are inside `backend_correct_final`: an indirect call of an extern under the contract `XCallsIndOk` (hypothesis `hXI`), an indirect call of a function of the program excluded by the run premise `TrapsExplicit.indirect`/`tryIndirect` (see "Indirect calls" below). Trusted-semantics growth: `Clif.stepCallIndirect` calls the extern at the callee address (`Clif.callExternAt`) where it was stuck | **proven** (`call_ind_ruleOk` 1033, `func_addr_ok` 1026, `try_ind_ruleOk` 1036, `stepCallIndirect_eq`, `term_step_try` over `IsTryWith`); `lean-e2e-check`: 1092 in scope (1083 before, plus the 9 functions of `corpus/clif-regress/call_indirect.clif`), 0 rejected, 0 not covered |
| **Atomics stage A** (2026-10-01, `agent/atomics-proof`): `bmask`, `atomic_load`, `atomic_store` and `fence` are in E (`Compile.instE`) and inside `backend_correct_final`, on the single-threaded Arm model (`docs/decisions/arm-model.md`, "Atomics"). `atomic_rmw`/`atomic_cas` stay outside E: their root rules (994–1004, 1007) are proven vacuous from `CtxInv.instE` | **proven** (`bmask_ok` 936, `fence_ok` 1024, `atomic_load_ok` 983, `atomic_store_ok` 984, `uextend_atomic_load_ok` 810, `atomic_loop_ok`; M6: `corr_csetm`/`corr_fence`/`corr_loadAcquire`/`corr_storeRelease`, `straight_loadAcquire`/`straight_storeRelease`, `ref_csetm`/`ref_fence`); `lean-e2e-check`: 1118 in scope (1092 before), 0 rejected, 0 not covered; filetests corpus 114/114, extrt 22/22, runtests 4672/0/0, `atomics_loops.clif` Lean 11/11; encode-check 1291 identical / 0 differ; `cargo fv` debug verified: fv-demo 1323/1346, survey 3156/3179, vendor 4324/4399, `compare.sh` SAME |
| **Atomics stage B** (2026-10-02, `agent/atomics-proof`): `atomic_rmw` (all 11 ops, i8–i64) and `atomic_cas` (i8–i64) are in E and inside `backend_correct_final`, on the same single-threaded Arm model (the LL/SC loop body runs once: `stlxr` succeeds and writes status 0). The loops are `isCtl` in `csem` (`loopSem`: one symbolic run of the body, FV/Backend/Proof/LoopRun.lean); register level in FV/E2E/RegLevelAtomic.lean (`realizes_rmwLoop`, `realizes_casLoop`). The RMW memory clause only fixes the low `ty.bytes*8` bits of the old-value def (smin/smax i8/i16 sign-extend x27 in place). The checker `ctlInstOk` requires every loop operand to be an int vreg. The CAS i32 comparison uses `uxtw` (deviation from Cranelift's upstream bug, docs/research/upstream-bugs.md) | **proven** (`atomic_rmw_*_ok` rules 2357–2377, `atomic_cas_ok` 2390; `rmwBody_spec`, `casHead_spec`, `stlxr_spec`; `csem_rmwLoop`, `csem_casLoop`). lean-e2e-check 1126 in scope / 0 rejected; cargo fv debug verified: survey 3174/3179, vendor 4381/4399, fv-demo 1332/1346 |
| **Stack-passed parameters and `call` arguments** (2026-10-01, `agent/stack-tls-proof`): functions with more than 8 parameters (an `sret` pointer does not count) and `call`s of externs with more than 8 parameters are inside `backend_correct_final`. `InSubset` drops `regParams`/`callRegArgs` (a `try_call`'s callee and the indirect calls keep at most 8 register parameters: `tryRegArgs`, `indSigs`). Entry: `ArgsIn` puts a stack location `off` (`locsOf`, `sigArgLocs`) at `sp + off` of the ABI entry state (`StackArgAt`); the entry code loads it from `fp + 16 + off` (`DriverCheck.entryLoads`, `entry_step`). Calls: the outgoing stores go to `[sp + off]` (`argStores_run`), the callee contract `XCallsOk` takes `ArgsAt` (stack arguments read from memory at `sp + off`). `Rel` gains the outgoing-area size `out` (`OutRel`: `[sp, sp + out)` fits, avoids `F` and holds no live CLIF byte; `backend_correct_final` takes `out := intBase`). `lowerCheck` adds `callsStackOkB` (every call's stack area fits `vc.outgoing`, `stackLayoutOk`) and `entryOkB`; `prepCheck` keeps `outgoing`. Specialisations (new ⇒ old for ≤ 8 parameters / no stack arguments): `InSubset.of_regArgs`, `argsIn_iff_of_regs`, `argsAt_iff_of_regs`, `xCallsOk_of_regArgs`, `Rel.holds_zero` | **proven** (`call_bl_ruleOk`/`call_got_ruleOk` any arity, `entry_step`, `callsStack_of_check`, `entryOk_of_check`, `stackArgsAvoid_frameF`, `outgoing_le_intBase`); `lean-e2e-check`: 1146 in scope (1126 before), 0 rejected, 0 not covered |
| **`tls_value`** (2026-10-01, `agent/stack-tls-proof`): `tls_value.i64` of a `symbol tls` global value (offset 0; `elf_gd`, cg_clif's TLS model) is in E (`Compile.instE`, `globalE`) and inside `backend_correct_final` for the one thread `Clif.run` models (its instance of the variable is the memory's symbol). M4: root rules 1129 (`elf_gd`, `tls_value_ok`) and 1130 (`macho`, vacuous), `MemRefines`' TLSDESC clause (`memRefines_csem`). M6: `ElfTlsGetAddr` is `isCtl`; `csem` gives `[X.sym n 0, X.tp]` and the flags `X.tlsFlags n w` (`ExtSem.tp`/`tlsFlags`); the machine hooks the TLSDESC sequence (`ArmStepX`: `adrp` advances the pc, `ldr` runs `H.tls n tmp`) under the trusted contract `TlsOk` (premise `hTls`, only for a function with a `tls_value`; see "`tls_value`" below); `realizes_tls`/`os_tls` (FV/E2E/RegLevelTls.lean). x30 joins `Masked` (`docs/contracts/regalloc-proof.md`: no weakening for other functions). Validators: `lowerCheck` (`noTls_of_check`) and `prepCheck` (`noTls_of_prepCheck`) keep `ElfTlsGetAddr` out of the VCode of a function without `tls_value`; `ctlInstOk` requires int vregs | **proven**; `lean-e2e-check`: 1148 in scope (1146 before), 0 rejected, 0 not covered; cargo fv debug verified fv-demo 1336/1346, survey 3174/3179, vendor 4398/4399 |
| **Last unverified functions** (2026-10-01, `agent/last-unverified`): (1) stack-passed arguments of a `try_call` are inside `backend_correct_final`: `TryRuleOk` takes `SigStackOk e.sig outB` instead of "at most 8 parameters", `TryRulesCorrect` also `MemRefines`/`OutArgsOk` (as `CallRulesCorrect`), `TryCalls` takes the outgoing area, `DriverHyp.tries` carries `TryStack f out`, `lowerCheck`'s `callsStackOkB` also checks `try_call` callees (`tryStack_of_check`); `InSubset.tryRegArgs` and `Backend.regArgCalls` are gone. (2) `Opt.Legal.check` accepts `try_call` (expanded arguments/returns, normal-return arguments `expandTry`) and `call_indirect` without `i128` operands (plan `callInd`); `backend_correct_legal` drops `hci`/`hnt` and takes `hCT`, `hXI` and `hind` (vacuous without such calls: `backend_correct_legal_callFree` is the former statement). (3) recursion: `cargo fv` renames a function's self-call declaration to an extern alias (see "Calls of the function itself") | **proven** (`try_sym_lowerTryOk`/`try_got_lowerTryOk` any arity; `sim_try`, `sim_callInd`, `check_callInd`); `cargo fv` debug: fv-demo 1340/1346 (6 skipped), survey 3179/3179, vendor all verified |
| **Linking** (2026-10-02, `agent/link-proof`): the CLIF side of linking the per-function theorems is proven — a whole-program run `Clif.runLoop base P` (calls and `try_call`s of functions of `P` enter them) that returns or traps is a per-function run of `P.only f` under `Clif.linkEnv P base` (`Clif.runLoop_link`) — and `E2E.backend_correct_linked` states `f`'s Arm code against the whole-program run, with the program callees' contracts as premises. Discharging those from the callees' own theorems is **not** done (see "Linking" below) | **proven** (CLIF layer, contract-level theorem); Arm-level discharge open |
| **Callee contract with a dead stack, non-vacuity** (2026-10-02, `agent/callee-fix`): the former `CalleeOk` was unsatisfiable by every callee that saves its return address below `sp` (proven on main as `calleeOk_saves_lr_false`), so `backend_correct_final` and the theorems built on it were vacuous for every function calling such a callee. The callee contract now leaves the callees' dead stack (`K` bytes below the caller's `sp`) unspecified, is required only at the compiled code's call sites, and the theorems are proven again; a witness callee that pushes two frames meets every contract premise, for callees without results and for callees returning their argument (`E2E.final_contracts_witness`/`final_contracts_id`, `E2E.backend_correct_final_witness`/`backend_correct_final_id`, `FV/E2E/NonVacuity.lean`). See "Callee contract with a dead stack" and "Non-vacuity" below | **proven**; `try_call` callees: open (the exception payload registers, see there) |
| **`try_call` callee contract, non-vacuity** (2026-10-02, `agent/trycall-contract`): the former `CalleeTryOk` fixed the exception payload registers of a `try_call`'s call (x0/x1 when not return registers) to `X.call`'s world, which a callee that does not write them cannot meet (it leaves the caller's values, which the world masks), so the theorems were vacuous for every function with a `try_call`. The payload defs are now dead on the normal-return edge: the allocated-code semantics havocs them there (`havocFrom`), the regalloc checker forgets them on that edge only (`CheckCtx.edgeForget`; kept for the handler edges), and `CalleeTryOk` constrains only the results, at the compiled code's `try_call` sites (`VCode.TrySite`). Witness: `E2E.backend_correct_final_try_witness` (see "`try_call` payload registers" and "Non-vacuity") | **proven** (`checkAlloc_sound` with `edgeForget_inv`, `realizes_tryCall`, every E2E theorem); lean-backend reports `try_call` functions verified for normal returns again |

### Final hypotheses (`E2E.backend_correct_final`, 2026-09-28)

Notation (since agent/callee-fix): `FF s := frameW K (RAFrame.compute vcp rf).intBase
(RAFrame.compute vcp rf).size af s` — the addresses outside the world of the activation entered
in `s`: its allocator-private frame addresses `frameF` (spill/save slots, the fp/lr pair and
padding above the CLIF slots, the code words) and the callees' dead stack, the `K` bytes below
the body's `sp` (`StackBelow K (spv s - frameDrop af)`); `K` is a parameter of the theorem (the
callees' stack budget), `cx := ⟨fa.k, af.slotBase⟩`.

| Hypothesis | Kind / owner |
| --- | --- |
| `InSubset p f`, `Compiled f k vc vcp rf af fa fb` | the compiler ran (pipeline + validators) |
| `FormsCovered cx vcp` | per-function decidable premise (`formsCoveredB`, the covered straight-line forms `FormOk`, including the per-instruction bitmask check `logicImmOk`; control forms are handled by the proof); decided by `lean-e2e-check` (corpus + extrt + runtests: 913 of 913 checked functions covered, M6Refines); a theorem on `LowerScope` input (V3: `formsCovered_complete`, `E2E.backend_correct_final_of_lower`; see "Validator completeness") |
| `∀ s, CalleeOk (FF s) K X H vcp.CallSite` | callee contract of the machine's call hook `H` at the call sites of the compiled code (AAPCS64: `CallSoundCtl` of every call — from a state whose `K` bytes below `sp` fit and lie in `FF s`, the callee leaves the world `X.call` computes outside `FF s`, keeps `sp` and the frame outside that dead stack, the callee-saved registers, and puts the results in the def registers —, return to pc+4 from an aligned `sp`, `X.call` error-free and program-preserving; see "Callee contract with a dead stack") — environment |
| `(∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk (FF s) X H vcp.TrySite` (`hCT`) | only for a function with a `try_call`, at its `try_call` sites: on a normal return the result registers of the call (its first `ti.rets` defs) hold what `csem` gives them; the exception payload registers past them are unconstrained (havocked on that edge, see "`try_call` payload registers") — environment; vacuous for a function without `try_call`, and for sites whose callee returns nothing (`calleeTryOk_of_rets0`) |
| `hasTls f = true → ∀ s, TlsOk (FF s) K X H` (`hTls`) | only for a function with a `tls_value`: the machine's TLSDESC hook `H.tls` ends after the sequence, puts the variable's address `X.sym n 0` in x0 and the thread pointer `X.tp` in the temporary, keeps every other register but x30, the memory outside the `K` bytes below `sp` (a resolver may save registers there) and the program, and leaves the flags `X.tlsFlags n w` — trusted (`docs/decisions/arm-model.md`, "Thread-local storage"); vacuous for a function without `tls_value` |
| `∀ s, XCallsOk env (f.externs.map (·.2)) (Rel.holds ⟨FF s, syms, slotOff, OB⟩ f) X` (`OB := (RAFrame.compute vcp rf).intBase`, the outgoing stack-argument area) | external contract for the externs `f` declares: callees, linker symbols — environment. The arguments are given by `ArgsAt` (register ones in their registers, stack-passed ones in memory at `sp + off`; for externs with at most 8 parameters this is the former "at most 8 values, all in registers", `xCallsOk_of_regArgs`); the callee returns a world related by `Rel.holds`, so in particular its outgoing area `[sp, sp + OB)` still avoids the frame and holds no live CLIF byte (`OutRel`; trivial when `OB = 0`, `Rel.holds_zero`). A call returns one value per ABI return of the declaration (`sigRets`), the first ones the extern's results (`PrefixHold`); for declarations without `sret` this is implied by the former extern-independent contract (`xCallsOk_of_results`) |
| `∀ s, XCallsIndOk env (indSigs f) (Rel.holds ⟨FF s, syms, slotOff, OB⟩ f) X` (`hXI`) | external contract for the indirect calls of `f` (`call_indirect`, `try_call_indirect`), per call-site signature (`Backend.indSigs f`): a `blr` whose target holds `X.sym n 0` of an extern `n` of `env` behaves as `env.extern n` does under that signature (the same clause as `XCallsOk`'s GOT call) — environment; vacuous for a function without indirect calls (`xCallsIndOk_nil`, `backend_correct_final_indirectFree`) |
| `∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b` (`hsym`) | linker: the external semantics' symbol addresses are the linked ones — environment; with `hslot` it discharges the former `MemRefines` hypothesis (`memRefines_csem`, M6MemRef) |
| `af.slotBase = slotOff` (`hslot`) | the relation's slot-region offset is the frame's slot base — caller (instantiate `slotOff := af.slotBase`) |
| per run: `AbiEntry fb base ra s`, `StackAvail K af s` (the frame and the callees' `K` bytes fit below `sp` and hold no code), `BodyEntry af s w₀`, `ArgsIn f.sig args s`, `ClifEntry f args cs`, `Rel.holds ⟨FF s, syms, slotOff, OB⟩ f cs.frame.slots cs.mem w₀`, `TrapsExplicit env p cs` (with the `try_call`/`try_call_indirect` trap clauses, and the indirect-call clauses `indirect`/`tryIndirect`: an indirect call of the entered function reaches no function of `p`; all vacuous for a function without them: `TrapsExplicit.of_tryFree`, `TrapsExplicit.of_indirectFree`) | caller of the theorem |

Conclusion: `ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)`.
`Refines` of `csem` is discharged (`refines_final`/`refines_csem`, M6Refines), as is `MemRefines`
(`memRefines_csem`, M6MemRef).
`MemRelOk` is internal (`memRelOk_holds`).

### `sret` (struct-return pointer)

The ABI facts are the compiler's (`FV/Backend/Isel.lean`, differentially tested against
Cranelift): an `sret` parameter is passed in x8 and does not take a slot of x0..x7
(`sigArgLocs`); a signature with an `sret` parameter and no returns returns the pointer in x0
(`sigRets`); `lowerFunction` appends the entry block's `sret` parameter to every `return`
(`sretRet`, `abiTerm`); a call of an `sret` callee places the pointer in x8 and defines x0.
The proof covers them as follows.

* **Scope** `InSubset.abiSigs`: `sigAbiOk` of `f`'s signature and of every extern's — `normal`
  parameters and returns plus at most one `sret` `i64` parameter, and then no returns
  (`Backend.abiSigs`; other special purposes such as `vmctx`/`sarg` stay unverified: cg_clif
  emits neither on aarch64, 0 functions in fv-demo, the survey, `examples/deps` and vendor,
  2026-10-22).
* **Entry** `ArgsIn sig args s`: a register-located argument in its register (`locsOf`:
  x0.. in order, the `sret` parameter in x8), a stack-located one at `sp + off`; with at most 8
  parameters this is "argument `i` in `x (argIdx sig i)`" (`argsIn_iff_of_regs`), and without
  `sret` `argIdx sig i = i` (`argIdx_of_noSret`). `lowerCheck`'s entry `Args` (`pre`) uses the same registers;
  `BodyEntry` keeps x0–x8 (`argsIn_body`, `argIdx_lt`).
* **Return**: `LowerShape`/`lowerCheck` lower `abiTerm f B.term`; the certificate makes the
  appended `sret` value available at every `return` (`Cert.term`), so the `rets` returns the
  CLIF values followed by the pointer. The driver's and the layer statements' return clause is
  `PrefixHold vals outs` (the CLIF values are the first ABI returns); the conclusion
  `ArmRefines` is unchanged (CLIF return values in x0.., memory), so for an `sret` function it
  claims the memory the function wrote through the pointer, not the value of x0.
* **Return register** (S7, #31, `agent/abi-s7`): `E2E.backend_correct_final_abi`
  (`FV/E2E/SretReturn.lean`) has `backend_correct_final`'s premises plus `sretStableB f`
  and the conclusion `ArmRefinesAbi … (sretArg f args)`: on a return, x0.. hold `vals ++
  sretArg f args` (`sretArg`: the `sret` argument when `sigRets` returns the pointer, else
  nothing; `ArmRefinesAbi.armRefines` gives back `ArmRefines`). `backend_correct_final_sret`:
  for a function with an `sret` parameter `i` and no returns, x0 holds `args[i]` (the pointer
  the caller passed in x8; `vals = []` by `runLoop_returned_tys_entry`). The chain: `term_step_abi`
  (the return's use values hold `vals ++ sv`, `sv` the frame's `sretRet f` values, `AllHold`),
  `sim_run_abi`/`driver_correct_abi` (`RunOkAbi Q`: `sv` satisfies any `Q` that holds of
  `sretRet f` in every reachable state; `term_step`, `sim_run`, `driver_correct` are the
  corollaries with `Q := True`, statements unchanged), `IselSimAbi`, then
  `backend_correct_{of_layers,_,of_rules,m4,final}_ex_abi`. The CLIF fact (`sret_reach`,
  `FV/Backend/Proof/SretStable.lean`): every state reachable from the entry is one activation of
  `f` without callers at a block's statements or at a `try_call`'s pending normal-return jump,
  with the `sretRet f` register as at entry (`StOk`, `stOk_step`, `stOk_reach`), when
  `sretStableB f` holds: the value is below `freshValue`, no statement result and no parameter of
  a block a terminator continues at (`runTargets`) binds it, and the entry parameters are
  distinct (Cranelift's verifier guarantees all of it: SSA, no branch to the entry block).
  `lean-e2e-check` reports `sretStableB` per function. Measured on the `cargo fv` bin-check
  dumps (2026-10-22): every function returning its `sret` pointer passes (fv-demo 234, survey
  249, `examples/deps` 4966). Witness: `SretReturnWitness.sw_returns_sret` (the cg_clif shape
  `(i64 sret, i64)` storing its argument through the pointer, compiled by the real pipeline,
  all contract premises discharged by the `NonVacuity` callees). The dead-cleanup variant has
  its `_abi` copies (`FV/E2E/SretReturnCleanup.lean`: `backend_correct_final_cleanup_abi`,
  `backend_correct_final_cleanup_sret`, witness `SretReturnCleanup.sw_returns_sret_cleanup`),
  and so has the typed chain (`FV/E2E/SretReturnT.lean`: `ArmRefinesTAbi`, each value of
  `vals ++ sretArg f args` in the return register of its class in the combined list;
  `backend_correct_finalT_abi`, `backend_correct_finalT_sret` for an integer `sret` parameter;
  driver `term_stepT_abi`/`sim_runT_abi`/`driver_correctT_abi`, `term_stepT`/`sim_runT`/
  `driver_correctT` the corollaries; witness `SretReturnWitness.sw_returns_sretT`).
  The executable theorem has its copy too: `Link.DeadCleanup.compileExe_correct_abi`
  (`FV/Link/DeadCleanupExeAbi.lean`; premise `sretStableB f` for the outside-called `f`,
  conclusion `ExecRefinesAbi … (sretArg f args)`), through `FV/E2E/SretReturnLink.lean`
  (`backend_correct_program_{core,budget,stack}_abi`, `binary_correct{,_of_checks}_abi`,
  `binary_correct_exec_{staticN,of_reads,of_insn,proven}_abi`) and `FV/E2E/SretReturnWorld.lean`
  (`backend_correct_world{,_cleanup,_pipeline}_abi`). Only the outside activation's return is
  strengthened: its return branch applies `backend_correct_world_pipeline_abi` to `f` with the
  callee contracts of the unchanged linked induction (`LinkSys.thm` at depth `M - 1`), so a
  compiled callee's contract still claims only its CLIF results (a Lean-compiled caller never
  reads x0 after an `sret` call). `sret_reach` holds for the per-activation run on `P.bare`
  (no program functions, every call an extern). Witness: `Link.DeadCleanup.SretWitness
  .exec_returns_sret` (`function %s(i64 sret)` compiled by `compileExeU`, x0 = the pointer).
  Over the mid-end: `backend_correct_opt_abi`/`backend_correct_opt_proven_abi`
  (`FV/E2E/SretReturnOpt.lean`; premise `sretStableB (Opt.optimize f cfg)`, the optimiser keeps
  the signature so `sretArg` is the source's; witness `SretReturnWitness.sw_opt_abi`). Through
  the `i128` legalisation: `backend_correct_legal{,_env,_wide,_env_wide}_abi`
  (`FV/E2E/SretReturnLegal.lean`; premise `sretStableB g` on the legalised `g`, conclusion
  `ArmRefinesLegalAbi … (sretArg g args')`; witness `SretReturnWitness.swl_legal_abi`, an
  `(i64 sret, i128)` function legalised by the compiler's pass); the dead-cleanup copies
  `backend_correct_legal{,_env}_cleanup_abi` (`FV/E2E/SretReturnLegalCleanup.lean`, witness
  `swl_legal_cleanup_abi`). The other variants (the linked `_unwind` theorems, the direct/opt
  legalisation copies, `OptX`/`_opt_exe*`) keep the CLIF-values conclusion.
  *With unwinding* (`agent/AbiS7d-unw`, `FV/E2E/SretReturnUnwind.lean`):
  `E2E.backend_correct_final_unwind_abi` (and `_ex_abi` for `CompiledA`) has
  `backend_correct_final_unwind`'s premises plus `sretStableXB f` and the conclusion
  `ArmRefinesUAbi … (sretArg f args) (Clif.runLoopX …)` (returns: x0.. hold `vals ++ sretArg f
  args`; traps and exceptions as `ArmRefinesU`, `ArmRefinesUAbi.armRefinesU`);
  `backend_correct_final_unwind_sret`: for an `sret` parameter `i` and no returns, a returned run
  with unwinding leaves `args[i]` in x0 (`vals = []` by `runLoopX_returned_tys_entry`). Chain:
  `sim_runX_abi`/`driver_correctU_abi` (`RunOkUAbi Q`, `FV/Backend/Proof/LowerSimUAbi.lean`),
  `IselSimUAbi`, `iselSimUAbi_of_driver`, `iselSimU_final_abi`,
  `backend_correct_of_layersU_ex_abi`. A caught exception continues at a `try_call`'s handler
  block, which `sretStableB`'s `runTargets` do not include, so the CLIF fact (`sret_reachX`,
  `FV/Backend/Proof/SretStableX.lean`: `StOkX`, `stOkX_stepX`, `stOkX_reach` over
  `E2E.ReachX`; pending `jump`s to normal-return or handler blocks) takes the stronger check
  `sretStableXB f` = `sretStableB f` and no handler block (`exnTargets`) has the `sretRet f` value
  as a parameter (also guaranteed by Cranelift's verifier; not measured on the crates). Witness:
  `SretReturnUnwindWitness.sw_returns_sret_unwind` (`sw` with its compilation and unwinding
  tables, `unwCheck`, `XRaise.none`/`Unw.UnwHooks.none`).
* **Calls**: `gen_call_args` puts argument `i` at `(locsOf sig)[i]`: a register (with at most 8
  parameters `x (abiArgIdx …)[i]`, `sigArgLocs_regs`) or a store to `[sp + off]` of the outgoing
  area (`argStores_run`); `gen_call_output` allocates one def per
  `sigRets` entry. `CallsRefine`/`XCallsOk` are stated for the declared externs (`exts :=
  f.externs.map (·.2)`) with `ds.length = (sigRets ext.sig).length` defs, `outs.length =
  ds.length` and `PrefixHold rvals outs`; an `sret` call has no CLIF result (`CtxInv.resTys`),
  so its extra def is not related to anything (`results_call`). `ExternsNormal` is gone
  (`CallRuleOk` assumes `ExternsIn f exts`).

### Typed ABI placement (`f32`/`f64`, S11e2/S11e3/S11e5a)

`FV/Backend/Isel.lean` models Cranelift's aarch64 `compute_arg_locs` for both register classes:
`abiArgLocs` puts an integer parameter in the next of x0..x7 and an `f32`/`f64` one in the next of
v0..v7 (separate counters), then 8-byte-minimum naturally aligned stack slots (`argLocsC`), the
`sret` pointer in x8 (`paramLocs`); `abiRetRegs` puts integer returns in x0..x7 and float ones in
v0..v7 (`retRegsC`, `none` past 8 of a class). Witness: `(f64, i64, f32)` goes to `[v0, x0, v1]`
(`Proof.abiArgLocs_sigFIF`, `abiRetRegs_sigFIF`; spill and `sret` cases next to them in
`FV/Backend/Proof/AbiClass.lean`).

S11e3 cuts the function's own entry and return over to the typed placement: `sigArgs`/
`sigParamBytes` admit `f32`/`f64` parameters, `sigArgLocs` is `paramLocs` (an `f32`/`f64`
parameter in the next of v0..v7, a stack-passed one loaded by `stackArgLoad` into a float vreg),
`buildCtx` maps a float value to `.vreg x .float`, and `gen_return` returns per class
(`retRegsC`, at most 8 values in all). Witnesses: `FVTest/Backend/AbiTyped.lean` and
`E2E.argsIn_sigFIF` (`ArgsIn sigFIF [a, b, c] s` is `a` in v0, `b` in x0, `c` in v1, through
`E2E.argsIn_iff_of_locs`; `E2E.argsIn_iff_of_regs` keeps the x-register form and takes
integer parameters, `hi`).

S11e5a types the direct `call` (Cranelift's `Lower::gen_call_output`, `machinst/lower.rs:630`,
and `Callee::gen_call_args`/`gen_call_rets`, `machinst/abi.rs:1819`/`1995`): `gen_call_output`
allocates one fresh vreg per ABI return of the return's class (`retClass`), `gen_call_args`
puts argument `i` at `sigArgLocs`' location (x0..x7 / v0..v7 by class, separate counters,
`sret` in x8, then the stack; a stack-passed float is stored by `stackArgStore` with `str s`/
`str d`), and `gen_call_rets` defines the outputs from the return registers of their classes
(`retRegsC (regsClasses rss) 0 0`, at most 8 values in all). `instData` no longer rejects a
`call` with an `f32`/`f64` parameter or return. Witness (`FVTest/Backend/AbiTyped.lean`): a
`call` of `(f64, i64, f32) -> f64` uses v0, x0, v1 and defines its result from v0. Native
check (qemu, `clif-native --link` of C callees built by clang): integer-signature functions
that call `(f64, i64, f32) -> f64|i64|f32` and a nine-`f64` callee (the ninth stored by
`stur d0, [sp]`) return the same values from the Lean backend's object as from Cranelift's
(4/4 runs). At S11e5a, functions with `f32`/`f64` parameters or returns of their own fell back
(`ctlCheck`: `Args`/`Rets` of int vregs only); since S11e5 Stage C slice 5a `ctlCheck` accepts
float `Args`/`Rets` in v0–v7 (`argPairOk`, `retPairOk`, `ctlCheck_of_int`;
`docs/contracts/backend-proof.md`), and the register-level `Args`/`Rets` proofs are
class-general (`realizes_args`, `ret_machine`), with the end-to-end statements unchanged.

Form coverage (V3) with typed calls: the transfer function `Cov.actor` gives `gen_call_output`
an int or float vreg (`.flat 3 true`; `CtorRes` records the signature argument), so
`covStmt_ok` excludes the `call` rules 1031..1033 and `stmt_cov` (statement unchanged) gets
their int results by hand in an integer context (`IselCovCall.out_call`, from
`CtxInv.call_retClasses`, and `sigIntB` for `call_indirect`; `root_hand_res`). Stock's own
`gen_call_output` allocates int vregs only: `Cov.actorI` is the integer-call transfer function
(the one before S11e5a) and `Stock.Proof.Coverage.ctor_value_sound_int` gives Stock's
constructors that conclusion (`ctor_value_sound` keeps its statement over `Cov.actor`; witness
`ctor_value_sound_int_witness`).

Remaining interim (S11e5 stages B/C): `instData` still rejects a `call_indirect` and
`exnTableOpnd` a `try_call_indirect` with an `f32`/`f64` parameter or return
(`sigIntB`; the totality scope `stmtInB`/`tryInB` says so; a direct `try_call` of such a callee is
lowered since S11e6 slice 2b, `exnTableOpndC`, outside the scope, whose extern signatures are
integer). `Compile.functionE` does not
constrain `f.sigDecls`, so a float indirect call would put a float value into the integer driver
model (`DriverCheck`, `CtxSpec.ctxE`/`tysOf_int` → `loop_run`), and the `try_call` contracts
(`tryRegsOf`, `LowerTryOk`, `CallOk`/`ArgReg`, `ShapeOf`) are integer-shaped. Every theorem
above still has the integer scope (`Compile.functionE` tests `isInt`): a `call` in scope has
integer returns (`CtxInv.call_retClasses`) and integer parameters (`hxi`), so its `locsOf`,
`stackBytes`, `stackLayoutOk` are the x-register placement `argLocs` (`Proof.sigArgLocs_eq`);
`ArgsAt` and the linking contracts still speak about x registers only.

### Float data movement (S11e4): not yet under the end-to-end theorem

The ISLE float data-movement roots are proven over the float-capable context `CtxInvT` with
the `IntPos` typing of the integer operands (`lowerRulesCorrectT_program`,
`memRulesCorrectRT_program`; `docs/contracts/backend-proof.md`, "Float data movement"), and the
float accesses need the new instruction-semantics obligation `MemRefinesFP Rd`. The
end-to-end chain does not consume them yet: `backend_correct_final` takes
`LowerRulesCorrect`/`MemRulesCorrectR` over `CtxInv` (integer values only, `Compile.functionE`),
and `csemG` leaves `fpuLoad`/`fpuStore` undefined (`GuardR` is `False` there). `E2E.csemGF`
(`FV/E2E/GuardedFP.lean`) is `csemG` extended by the guarded float accesses; it satisfies
`Refines`, `MemRefinesR Rd` and `MemRefinesFP Rd` (`refines_csemGF`, `memRefinesR_csemGF`,
`memRefinesFP_csemGF`), which shows the premises of `MemRulesCorrectRT` are satisfiable.

**The float lockstep (S11e5 Stage C slice 4).** `csem`'s specification fallback `mspec` states
the scalar float loads/stores (the arms of `fspec`), so `csem` refines them on every world
(`csem_fpuLoad`, `csem_fpuStore`, `memRefinesFP_csem`) and `csemGF` is a sub-semantics of `csem`
(`csemGF_sub`) that extends `csemG` (`csemG_csemGF`) with its pinned call contracts
(`callsRefineP_csemGF`, `indCallsRefineP_csemGF`). Two `csemGF` runs of one instruction on
worlds that agree outside `Z ⊇ F`, reads guarded by `¬ Z`, go in lockstep
(`csemGF_lockstep2`): a float load reads the same bytes, a float store writes the same value at
the same address (`sp`/`x29` agree). On pairs of worlds (`FV/E2E/GuardedFPPair.lean`):
`guardedStepF`, `guardedStep0F`, and the guarded simulation composition of a statement and of a
`try_call` from per-step contracts at any guarded sub-semantics with the lockstep
(`lowerInstOk_pair_of`, `lowerTryOk_pair_of`), instantiated at `csemGF` (`lowerInstOk_pairF`,
`lowerTryOk_pairF`); `instCalls_pair_viaF`, `tryCalls_pair_viaF`, `tryIndCalls_pair_viaF` derive
the statements of `instCalls_pair`, `tryCalls_pair`, `tryIndCalls_pair` through it (the integer
contracts lifted along `csemG ⊑ csemGF` by `LowerInstOkP.sem_ext`/`LowerTryOkP.sem_ext`). The
shipped value semantics has the same (`valueSemGF`, `valueSemGF_lockstep2`,
`lowerInstOk_pairF_value`, `instCalls_pair_value_viaF`; `FV/E2E/DeadCleanupGuardedFP.lean`).
Witnesses: `FV/E2E/GuardedFPWitness.lean`. Remaining: the typed per-step contracts (rules over
`CtxInvT`, dispatched as `lowerInstOkP_runTerm` is), the typed driver/`vcode_ni` that consumes
them, and the widened scope.

**The typed end-to-end chain (S11e5 Stage C slice 7).** For the typed movement scope
(`InSubsetT`: `Compile.functionET`; `CompiledT`/`CompiledAT`: the typed validator
`lowerCheckT`) the conclusion is `ArmRefinesT` (`FV/E2E/ComposeT.lean`): a returned value is
held by the ABI return register of its type's class (`retRegsT`: x0.. for integers, v0.. for
`f32`/`f64`), not necessarily an X register; for integer returns it is `ArmRefines`
(`ArmRefinesT.toArmRefines`, `backend_correct_of_layers_ex_ofT`). `PrepareCorrect` and
`RegLevelCorrect[Ex]` are reused unchanged. The typed driver `driver_correctT`
(`Proof/LowerSimT.lean`) consumes the typed calls of `Proof/LowerContractT.lean`; the final
theorems `backend_correct_final_exT`/`backend_correct_finalT` (`FV/E2E/FinalT.lean`, at `csem`,
float accesses by `memRefinesFP_csem`) take the open typed rule families as one premise
`TypedRules`; `backend_correct_final_ofT` re-derives `backend_correct_final`'s conclusion
through the typed chain; `backend_correct_finalT_alloc` (`FV/E2E/FinalDirectT.lean`) composes
slice 6's typed spill chain. Witness: `FVTest/E2E/FloatFinalT.lean`.

**The typed executable compiler (S11e5 Stage C slice 8).** `Link.compileExe_correctT`
(`_depthT`, `_peakT`; `FV/Link/ExeT.lean`) and `Link.DeadCleanup.compileExe_correctT`
(`FV/Link/DeadCleanupExeT.lean`) are `compileExe_correct*` for the typed input conditions
`InScopePT` (float data movement, float parameters and returns), with `E2E.typedRules_program`
inside (no rule-family premise), for `leanLink S file0 = .ok file` and the decided output checks
`OutOkT`/`OutOkTCleanup` (`FV/E2E/LinkOutT.lean`, `LinkOutCleanupT.lean`); the conclusion
`ExecRefinesT` places each returned value in the return register of its class. The typed
link/binary/exec layers are the `FV/E2E/*T.lean` copies of the integer ones. The integer
theorems' conclusions follow from their exact premises through the typed ones
(`compileExe_correct_viaT`, `_depth_viaT`, `_peak_viaT`, `DeadCleanup.compileExe_correct_viaT`;
`FV/E2E/LinkScopeIntT.lean`). Witness `FVTest/Link/FloatExeT.lean`; audit
`scripts/audit/floats-typed.lean`.

### `try_call` (the normal return)

`Clif.run` models a `try_call fnN(args), sigM, block(ret…)[, handlers]` as the call of `fnN`
with its results bound to fresh values (`Function.freshValue`), then the jump to the
normal-return successor with the `retN` arguments (`Clif.stepTryCall`, two steps). It has no
unwinding: a callee never resumes at a handler. The backend lowers the terminator with
`lower_branch` rules 1034 (`bl`) / 1035 (GOT + `blr`) in a context whose `tryRegs` are the
return and payload vregs allocated before the call (`tryRegsOf`), replaces the call the rule
emits by the `tryCall` terminator (`tryFix`), and gives every successor an edge block (the
handlers' are the landing pads, the last one the normal return, `jump` to the successor with
the `retN`/value arguments).

* **Scope** `InSubset.tryExterns`: a `try_call` calls an extern that is not a function of `p`
  (like `externCalls`); `Compile.termE` admits `try_call` and `try_call_indirect` (see
  "Indirect calls"). A `try_call`'s callee may take stack-passed arguments (agent/last-unverified:
  the stores into the outgoing area precede the `tryCall`, `try_sym_lowerTryOk`/
  `try_got_lowerTryOk`; `lowerCheck`'s `callsStackOkB` checks the callee's area against
  `vc.outgoing`).
* **Float returns (S11e3, a fix; S11e6 typed)**: a `try_call`/`try_call_indirect` whose
  signature has an `f32`/`f64` parameter or return fell back (`exnTableOpnd`: `try_call with
  f32/f64 parameters or returns`). Before, `tryRegsOf`/`gen_try_call_rets` gave every return an
  integer vreg in x0..x7 (`retRegs`), while AAPCS64 returns a float in v0..v7: a wrong ABI. It was
  not observable before S11e3 (a float return could not be used: `buildCtx` rejected `f32`/`f64`
  block parameters, so the wrong x0 def was dead), but with S11e3's float values it would have
  read the normal-return value from x0. S11e6 slice 2 types these returns (`retRegsC`,
  `tryRegsOfC`): `lowerFunction` lowers a direct `try_call` of a float signature (outside this
  theorem's scope, whose extern signatures are integer; `try_call_indirect` still falls back).
* **Claim**: exactly the normal return. `ArmRefines` is unchanged: when `Clif.runLoop`
  returns or traps, so does the Arm code. A run that passes through a `try_call` is related
  only along the path where the callee returns normally.
* **Traps** `TrapsExplicit.tryCall`: the step of a `try_call` terminator of the entered function
  does not trap (the callee returns normally), as calls in statements are excluded by
  `TrapsExplicit.stmt` (a call is not an explicit trap).
* **Callee contract** `CalleeTryOk F X H S` (`FV/E2E/RegLevelTry.lean`, hypothesis `hCT`, only
  for functions with a `try_call`, at its sites `S = vcp.TrySite`): the call of a `try_call`
  defines, beyond the results, the exception payload registers x0/x1 that are not return
  registers (`gen_try_call_rets`); on a normal return their values are unconstrained by the
  ABI, so they are dead on that edge (havocked by the allocated-code semantics, forgotten by the
  regalloc checker on the normal-return edge only), and the clause states only that the hooked
  callee leaves in the result registers (the first `ti.rets` defs) the values `csem` gives them.
  `CallsRefine` has a third clause for the `tryCall` (proven for `csem` from `XCallsOk`,
  `callsRefine_csem`), which continues at successor `ti.handlers.length` (the normal return).
* **Not claimed by `backend_correct_final`**: nothing about unwinding. The unwinding theorem
  below covers it; for functions outside that theorem the landing pads, the exception payload
  on the handler edges, the call-site table/LSDA (`callSites`, `.gcc_except_table`), the
  `.eh_frame` rows and the personality routine stay trusted.
* **The exceptional edges (S10e, #232)**: `E2E.backend_correct_final_cleanup_unwind` (the
  shipped dead-cleanup chain; `E2E.backend_correct_final_unwind` without it,
  `FV/E2E/FinalUnwind.lean`) concludes `ArmRefinesU … (Unw.ArmStepU X H U T fa) s
  (Clif.runLoopX env p fuel cs.toX)`. An exception caught by a handler reaches the landing pad
  with the payload (x0 = object, x1 = 0). An uncaught one (`unwound e cm`) is an Arm return to
  the caller (`ArmRet`: return address, entry sp, callee-saved registers) with the object in x0
  (`ExnRel`) and the memory agreeing. The premises beyond `backend_correct_final`'s:
  * the validator `lowerCheckU` (`lowerCheck` and `unwCheck`: the handler edges);
  * the externs' exceptional results `XRaiseOk`/`XRaiseIndOk` and their exclusivity with normal
    returns `XRaiseExcl`;
  * the raising callees' contract `CalleeUnwOkG` (a raising callee keeps sp, the frame and the
    callee-saved registers; the unwinder restored our call's state);
  * the tables the unwinder reads, taken as the emitted ones: `T.lsda` from `callSites`, the CIE
    `cieInsns` and the FDE rows `unwindRows` (S10f discharges these from the linked bytes);
  * the decidable checks `savedCheck` (the callee-save slots hold the entry values at every
    call) and `padsNonzeroB` (landing pads at non-zero offsets); the `_any` variants
    (`backend_correct_final_cleanup_unwind_any`, `backend_correct_final_unwind_any`, and the
    `_any` variants of the legal/opt/sret/linked theorems below) need no check on the calls of
    the last block (#622: the call-site bridge `siteAt_any` holds for every block since #553);
    the theorems without the suffix keep the former check `lastCallsOk` as a premise and are
    their corollaries. `lean-backend` cites the `_any` theorems and no longer runs `lastCallsOk`.
  * `TrapsExplicitX` for the runs with unwinding.

  Trusted by design, like std: the model of the Itanium unwinder and of the personality routine
  (`FV/Unw/Model.lean`: `Unw.unwindAt`, `Unw.personality`, `Unw.restore`), and the decoding of
  the emitted tables as that model reads them. With `XRaise.none`/`Unw.UnwHooks.none` the theorem
  specialises to the normal-return shape (`E2E.backend_correct_final_of_unwind_any`). `lean-backend`
  labels a function whose checks pass `compiled, verified`. A function failing a check keeps
  `compiled, verified for normal returns (…; unwinding check failed: <check>)`. So does a
  function compiled with `--opt` with unproven rule sets (no unwinding theorem composes them),
  or an `i128`-legalised function compiled without the dead cleanup.
* **`i128` legalisation with unwinding (S10f, #233)**: `E2E.backend_correct_legal_unwind`
  (`FV/E2E/LegalUnwind.lean`) composes `Opt.Legal.X.check_refinesX` (`FV/Opt/Proof/LegalSimX.lean`:
  `Opt.Legal.check` plus the handler-edge check `Opt.Legal.exnOk` (`FV/Opt/LegalExn.lean`) make
  the legalisation `g` refine `f`'s run with unwinding: returns by the ABI groups, traps, and
  exceptions leaving `f` with the same memory) with `backend_correct_final_cleanup_unwind` at
  `g`, under the trusted Rust environment with unwinding `Clif.Rust.xenvWith raises obj`
  (`FV/Opt/Proof/LegalRustX.lean`, contracts proven: `xenvWith_envOkX`; `panic=unwind` is
  `Clif.Rust.xenv`). Conclusion `ArmRefinesLegalU` (returns of the expanded results, traps,
  `ArmRefinesU`'s exception clause). Premises: `backend_correct_final_cleanup_unwind`'s at `g`,
  `check`/`exnOk`, the program conditions `hext`/`hext'`/`hind` (as `backend_correct_legal`),
  the ABI-split arguments `hexp` and the two `ClifEntry`s, `TrapsExplicitX` of both runs;
  `backend_correct_legal_unwind_env` takes any environment with `Opt.Legal.X.EnvOkX`.
  `lean-backend` labels an accepted legalised `try_call` function `compiled, verified (try_call:
  unwinding by backend_correct_legal_unwind; …)` when its legalisation, recomputed from the
  source function, is the compiled one, `check` and `exnOk` accept it and the unwinding checks
  pass (dead cleanup only). Non-vacuity (`FV/E2E/LegalUnwindWitness.lean`):
  `Clif.Rust.LegalXWitness.refines` (`check_refinesX` on `%w(i128)`, a `try_call` whose callee
  `%throw` raises and whose `tag0` handler catches, `caught`; every premise discharged) and
  `E2E.LegalUnwindWitness.legal_unwind_applies` (`backend_correct_legal_unwind` on the shipped
  pipeline's output for the legalised `%w`, receipt `checks_true`; open as in
  `DeadCleanupUnwindWitness.final_applies`: `hC`/`hCT`, `hsym`, the entry premises).
* **The mid-end with unwinding (S10f, #233)**: `E2E.backend_correct_opt_exe_cleanup_unwind`
  (`FV/E2E/OptUnwind.lean`; without the dead cleanup `backend_correct_opt_exe_unwind`): the Arm
  code compiled from `Opt.optimizeExe f cfg` (proven rule sets, `--opt-proven-only`), run on the
  machine with unwinding, refines the run with unwinding of the *source* program from `f`'s entry
  (`ArmRefinesU`). It composes `E2E.optExe_entryX` (the optimised program's runs with unwinding
  refine the source's: `Opt.optimizeProgramExe_refinesU`, `FV/Opt/Proof/PipelineU.lean`, from
  `Opt.runLoopX_refinesU`, `FV/Opt/Proof/SemSimU.lean`) with
  `backend_correct_final_cleanup_unwind` at the optimised function. The mid-end's simulations
  cover the handler edges of `try_call` (`Opt.HCont`: the renamed exception table catches the
  same exceptions and resumes at related handler blocks, the payload bound at each side's fresh
  value; `Opt.FunSimU`; per stage `removeUnreachable_simU`, `simpOk_simU`, `editOk_simU`).
  Premises: `backend_correct_opt_exe_cleanup`'s with the environment with unwinding (externs keep
  the link-time symbols when they return and when they unwind, `Opt.EnvKeepsSymbolsX`; proven for
  the trusted Rust environment, `E2E.xenvWith_keepsSymbolsX`), and
  `backend_correct_final_cleanup_unwind`'s unwinding premises at the optimised function;
  `TrapsExplicitX` of the optimised program's run. `lean-backend --opt --opt-proven-only` labels
  a `try_call` function `compiled, verified (try_call: unwinding by
  backend_correct_opt_exe_cleanup_unwind; …)` when its compiled form is `Opt.optimizeExe` of its
  source function (recomputed) and the unwinding checks pass on the optimised function.
  Legalised then optimised: `E2E.backend_correct_legal_opt_unwind` (`FV/E2E/LegalOptUnwind.lean`;
  `_env` for any environment with `Opt.Legal.X.EnvOkX` and `Opt.EnvKeepsSymbolsX`), labelled
  `… unwinding by backend_correct_legal_opt_unwind` when the recomputed legalisation (accepted by
  `check` and `exnOk`) optimises to the compiled function. Non-vacuity
  (`FV/E2E/OptUnwindWitness.lean`): `E2E.OptUnwindWitness.refines` (`optExe_entryX` on
  `%w(i64)`: `v2 = v0 + 0; try_call %throw(v2)`, rewritten by the mid-end to
  `try_call %throw(v0)`; `%throw` raises, the `tag0` handler catches; every premise discharged),
  `opt_unwind_applies`, `opt_unwind_applies_legacy` and
  `E2E.LegalOptUnwindWitness.legal_opt_unwind_applies` (the theorems on the shipped pipeline's
  output; open as in `LegalUnwindWitness.legal_unwind_applies`: `hC`/`hCT`, `hsym`, the entry
  premises).
* **Linked programs with unwinding (S10f, #233)**: whole-program CLIF runs with unwinding are
  per-function runs under linked environments (`Clif.runLoopX_link{,R,N,D}`,
  `FV/Clif/LinkClifX*.lean`); per function with the world and non-interference
  `E2E.backend_correct_world_pipelineU`/`backend_correct_world_ni_pipelineU`
  (`FV/E2E/WorldUnwind*.lean`, `PairRaise.lean`, `PairDriverU.lean`, `FV/Backend/Proof/LowerSimUW.lean`).
  `LinkSysU` (`FV/E2E/LinkArmU.lean`) is `LinkSys` plus the base callees' raising hook `Ub`,
  their CLIF environment `envX` and Arm-level exceptional results `XRb`; `LinkSysU.OkU` (the
  base contract: `CalleeUnwOkG` per base call site with the GOT guard, `baseNoRaise`, places and
  allocations kept by raising externs, the per-function unwinding checks and tables) and
  `OkUNI` (non-interference of base raises, vacuous when no base callee raises). The depth
  induction `LinkSysU.thmUN` (`LinkArmUIndNI.lean`; `thmU` with `¬ NeedNI`) gives
  **`E2E.backend_correct_program_budgetU'`** / **`_peakU'`** (`FV/E2E/LinkArmUProgNI.lean`):
  the linked machine with unwinding `L.machU M f` refines `Clif.runLoopX L.envX L.P (M+1)
  cs.toX` (`ArmRefinesU`: returns, traps, and an exception leaving `f` with the object in x0 and
  the caller's frame restored). Witnesses: `LinkArmUProgWitness.budgetU_applies` (a base callee
  raises through a program function; `run_unwinds`), `LinkArmUProgNIWitness.budgetU'_applies`
  (on `NonVacuityLink`'s program, which has `NeedNI`); the entry premises stay open there.
* **Executables with unwinding (S10f, #233)**: `Link.DeadCleanup.compileExeU S file0 = .ok file`
  is `compileExe` plus `unwOkB S file` (`FV/Link/ExeUCompile.lean`): `Link.EhCheck.ehOkR`
  (`FV/Link/EhCheck.lean`: through the trusted lookup model `FV/Unw/EhFrameHdr.lean`, the
  executable's `.eh_frame_hdr` search finds, for every pc of every Lean-compiled function, an
  FDE whose CFI and LSDA decode to exactly the tables the theorem uses; `ehOkR_sound`) and
  `unwFnsB` (the per-function unwinding checks, `unwFnsB_sound`).
  **`Link.DeadCleanup.compileExe_correct_unwind`** / **`_peak`** (`FV/Link/ExeUnwind.lean`):
  under `compileExeU` and the base premises (`BaseU`, `OkUNI`), the file's tables are the
  compiled functions' (`compileExeU_tables`) and `backend_correct_program_budgetU'`/`peakU'`
  hold for the linked system of the executable. `lean-link` evaluates `unwOkB` (with dead
  cleanup; under `--opt` `compileExeOptU`, below): when it holds the `coverage:` line adds `exceptional edges:
  Link.DeadCleanup.compileExe_correct_unwind, …_peak`, otherwise it prints `exceptional edges
  not covered (unwOkB: <reason>)` and still writes the file. Bundles:
  `Front.bundle_correct_raw_unwind` (`FV/Front/RawExeUnwind.lean`: `bundle_correct_raw`'s
  normal edges for cg_clif's raw program and the exceptional edges for the compiled program) and,
  for `i128`-free bundles, `bundle_correct_raw_unwind_ren` (the exceptional edges stated on the
  raw program, by `Clif.runLoopX_ren`, `FV/Front/RenameRunX.lean`). Witnesses:
  `Link.EhCheck.Witness.unw_call`, `Link.DeadCleanup.UnwindWitness.unwind_applies`,
  `Front.RenameRunXWitness.renamed_unwinds`, crate-proofs
  `Crates.FrontendBundleUnwindWitness.bundle_unwind_witness` (g_u128's bundle). With `i128`:
  **`Front.bundle_correct_raw_unwind_src`** (`FV/Front/RawExeUnwindSrc.lean`):
  `bundle_correct_raw_unwind_ren` without its `i128`-free premise. A return, a trap (of a source
  run without load/store traps) or an exception leaving `f` of cg_clif's run with unwinding is
  refined by the linked machine with unwinding of the compiled `legalize (f.rename σ.fwd)`
  entered with the ABI-split arguments (`MachAt`): the results split by `f`'s return groups, the
  same trap, the same exception, the memories renamed. It composes `Front.raw_legal_unwind` (the
  CLIF half: `Clif.runLoopX_ren` and the program-level legalisation with unwinding) with
  `compileExe_correct_unwind`. Premises beyond `compileExe_correct_unwind`'s: `SrcScopeB`; where
  a function mentions `i128`, the linked environment's `HelperOk`/`ExtLegal`/`EnvKeepsBounded`
  and `ExtLegalX`/`EnvKeepsAllocsX`/`ExnArityOk` (`Clif.Rust.xenvWith` has them); `Opt.Legal.exnOk`
  of every legalised function; the source entry with the compiled entry's slots and renamed
  memory; the source run's memories below `2^64` (dropped by
  `Front.bundle_correct_raw_unwind_src_nobnd`, `FV/Front/RawExeUnwindSrcNB.lean`: derived by
  `E2E.SrcBoundedX` from `MachAt`'s stack, legalize128.md "The memory bound derived"); for traps,
  no load/store trap on the source run. *The program-level legalisation with unwinding* (`FV/E2E/LegalProgX.lean`,
  **`E2E.LegalProgram.legalProg_refinesX`**): S3's `legalProg_refines` for `Clif.runLoopX` on
  `ProgCtxX` (`ProgCtx` plus the unwinding contracts where a function mentions `i128`, `IndScopeX`
  with indirect calls, `exnOk` of every legalisation) from good states (`GoodFromX`); proof: S3's
  fuel induction, the source run per function under the guarded linked environment
  (`Clif.runLoopX_linkR`), each activation by `Opt.Legal.X.check_refinesX2`
  (`FV/Opt/Proof/LegalSimX2.lean`, two environments) or `identX_run`, the target unlinked by
  `Clif.unlinkX_run` (`FV/E2E/LinkClifRevX.lean`, the converse of `runLoopX_linkR`). Witnesses:
  `E2E.LegalProgram.XWitness.caught_refines`/`unwound_refines` (`w(i128)` `try_call`s
  `mid(i128)`, whose call of `%throw` raises; every premise discharged by `decide +kernel`),
  `Front.RawExeUnwindSrcWitness.raw_caught`/`raw_unwound`. The executable-bytes machine with
  unwinding: below (its theorems keep the per-state facts `RunOkU` open).
* **The optimising executable with unwinding (S10g, #404)**: `Link.DeadCleanup.compileExeOptU S
  file0` is `compileExeU S.opt file0` (`compileExeOpt`, then `unwOkB` of the optimised input;
  `compileExeOptU_placed`: what `lean-link --opt` decides) (`FV/Link/OptExeUnwind.lean`).
  `compileExeOpt_correct_unwind`: `compileExe_correct_unwind`'s statement (`UnwindStmt`) for the
  optimised input. **`compileExeOpt_correct_unwind_peak`**: through the mid-end — for `f` of the
  input's program (after the `i128` legalisation, before the mid-end) and its optimisation `f'`
  entered with the same registers, slots and memory, the linked machine with unwinding of the
  optimised program of depth `d` (a bound on the optimised run's call depth, `DepthLeX`) refines
  **every** run with unwinding of the input's program from `f`'s entry (`ArmRefinesU`). Proof: the
  mid-end's simulation with handler edges at program level (`FnInput.opt_simU`,
  `funsSimU_prog`, the entries related by `sru_entry`, `Opt.runLoopX_refinesU`) matches each
  return, trap and exception by the optimised run's at some fuel, and
  `compileExe_correct_unwind_peak` at that fuel. Premises beyond `compileExe_correct_unwind_peak`'s:
  the linked CLIF environment keeps the link-time symbols (`Opt.EnvKeepsSymbolsX`), the trap
  premise at every fuel. Witness: `Link.DeadCleanup.OptUnwindWitness.stmt`/`peak_applies`
  (`%rec`'s optimised executable; `compileExeOptU` by `native_decide`).
* **Completeness of the per-function unwinding checks (S10g, #404, in progress)**
  (`FV/Link/UnwFnsComplete.lean`, namespace `Link.EhCheck.Complete`): three of `unwFnsB`'s six
  checks pass on what the pipeline emits, from structural premises on the allocation `af` and
  the emitted code (`lowerRFunc vc rf = .ok af`, `emitFunc k af = .ok fa`, `fa.layout = .ok fb`,
  the entry blocks `vc.blocks[0]?`/`rf.blocks[0]?`): **`callSites_complete`** (`HandlersOk af`:
  every `try_call` handler is a cleanup/catch tag, 0 or 1, whose landing pad is a block of `af`),
  **`padsNonzero_complete`** (`PadsOk af l0`: every `try_call` has a handler, none at the entry
  block: the entry label is at offset 0 and every other label after the prologue's `stp`/`mov`,
  `label_off_ge`), **`unwindRows_complete`** (the entry block's leading callee-save stores have
  negative 8-aligned CFA offsets, `SaveOk`, and the code is below 4 GiB; the emitted code starts
  with the entry label, the prologue and those stores' lines, `entry_static`). Witness:
  `Link.EhCheck.Complete.Witness.callSites_applies`/`padsNonzero_applies`/`unwindRows_applies`
  (`DeadCleanupUnwindWitness.tc`, a `try_call` with a landing pad and callee-saves).
  `HandlersOk`/`PadsOk` of the allocation follow from **`TryInfoOk vc`** of the prepared code
  (every `try_call` has a handler, each a tag 0/1 whose landing pad is a block other than the
  entry; decidable `tryInfoOkB`): `handlersOk_of_tryInfo`, `padsOk_of_tryInfo` (a `try_call` of
  `af` is one of `vc` with the same handlers, `tryCall_of_af`); witness `Witness.tryInfo_applies`.
  **`TryInfoOk` from the input** (`FV/Link/UnwTryIn.lean`): `tryInfoOk_of_input` — on in-scope
  input (`Dominated`, `LowerScope`, `Spill.ArityOk`) whose `try_call` tables have at least one
  item, each a `tag 0`/`tag 1` handler (**`tryTablesB f`**, decidable on the CLIF function),
  `prepare (prune vc)` of `lowerFunction f = .ok vc` satisfies `TryInfoOk`: `lowerFunction`
  builds the handlers from the items (`exnTableOpnd_items`, `tryInfoOf_tags`), `prepare`'s
  `setTargets` keeps the tags (`setTargets_tags`), every `tryCall` stays its block's last
  instruction (`Good`: `lower_good`, `prepare_good`, `good_sublist` for the cleanup), so its
  handlers' labels are CFG successors (`cfg_spec`) and none is the entry block (`EdgesOk.entry`,
  `preds_empty`). Corollaries `callSites_complete_input`, `padsNonzero_complete_input`; witness
  `Witness.tryInfoOk_applies`/`input_applies` (`FV/Link/UnwTryInWitness.lean`, on `tc`).
  **Landing pads through `MachBuffer`'s aliases (#553)**: `callSites`/`padsNonzeroB` resolve a
  handler's label through the emitter's block-label aliases `fa.alias` (`siteLabs`), so a
  handler forwarding to the entry block would get pad offset 0. The generic
  `padsNonzero_complete` (any `vc`) therefore takes the decidable `aliasEntryOkB af fa` (no alias
  resolves to the entry block); `padsNonzero_complete_of` takes the weaker fact that no alias of
  another label does. On the pipeline's output that fact is a theorem: `alias_ne_entry` (every
  alias passes `aliasOk`; line 0 of the plan is the entry label followed by the prologue, so it
  represents only the entry and the blocks forwarding to it) with `fwd_ne_entry_input` (no
  block forwards to the entry: a forwarding block's `jump` is its prepared block's last
  instruction — `TargetsLast` from the ISLE runs, `vc_emit`/`prep_emit`, which needs
  `extendsWidenB` — hence a CFG successor, and `lowerRFunc`'s `ctlCheck` excludes the entry).
  So `padsNonzero_complete_input` takes `extendsWidenB f` (part of `fnScopeB` and of every input
  scope) instead of a check on the compiled code, and `unwCondB`/`unwCondInB` have no alias
  condition. Witnesses `Witness.fwd_applies`/`aliasNoEntry_applies`/`padsNonzero_of_applies`.
  `lake exe lean-link` still reports `aliasEntryOkB` per executable (report only).
  **`unwCheck` from the input** (`FV/Link/UnwCheckIn.lean`): `unwCheck_complete` — on input in
  `Dominated`/`LowerScope` with `tryTablesB` and **`tryRetsB f`** (every `try_call` signature has
  at most two ABI returns, so the call defines x0 and x1 only, as `tryUOk` requires; decidable on
  the CLIF function), `unwCheck f vc` holds for `lowerFunction f = .ok vc`. Parts: a call
  statement's code contains a call (`Backend.Proof.stmtCall_hasCall`, `UnwCallStmt.lean`: the
  rules of `lower` whose root format is `Call`/`CallIndirect` are the `call` rules 1031–1033 and
  the `return_call` rules 1038–1040, which never match a call; one kernel decision
  `lower_callHas_fmts`); a `try_call` rule emits call-free code then one call with the
  `try_call` defs (`Backend.Proof.UnwShape.tryEmS_run`, `UnwTryShape.lean`, the inversions of
  `KillTryDefs` with the code kept), so the call is last, its operands compute, its defs are late
  with distinct vregs and fixed to x0/x1, and an `exnN` argument is the def in `xN`; the first
  handler's label holds `lowerFunction`'s edge block (`edgeBlocks`, found at its label by
  `LowerShape.labels`); the edge into the handler's block satisfies `Cert`'s edge conditions
  (`Driver.edgeOk_succ`: `certBlock_ok`'s edge argument for every successor, not only the normal
  edge). Witness `Witness.unwCheck_applies` (`FV/Link/UnwCheckInWitness.lean`, on `tc`).
  **`savedCheck`** (`FV/Link/UnwSavedIn.lean`): the allocation part by construction —
  `savedCheckRF_spill` (spill allocation), `savedCheckRF_build` (regalloc2's answer as `buildRFunc`
  reads it: the saved registers are every callee-saved register its locations mention), so
  `savedCheckRF_pipe` for every allocator answer the pipeline lowers; `savedCheck_of`/
  `savedCheck_pipe` add that the allocation lowers. **`unwindRows`** (`unwindRows_complete`,
  `FV/Link/UnwFnsComplete.lean`): with Cranelift's frame (#549: `stp x29, x30` / `mov x29, sp`,
  then the saved registers pushed below the frame record) the rows are `prologueRows ++
  pushRows af.saves 8` for every function whose code is below 4 GiB; `unwindRows_complete_frame`
  wraps it. No frame condition is left (the former `saveFrameB`/`leadOkB` are deleted).
  Witness `Witness.savedCheck_applies`/`unwindRows_frame_applies`/`unwindRows_applies`.
  **What is left, collected** (`FV/Link/UnwFnIn.lean`): `unwCondB g a` = the input condition
  `tryTablesB`, code below 4 GiB, and the check without a completeness proof here, `unwCheck`
  (`lastCallsOk` is no longer needed since #622); `fnUnwB_of_pipe` (a function
  of `fnScopeB` whose cleanup pipeline succeeded, any allocator answer, passes `fnUnwB`) and
  `unwFnsB_of_conds` (on an `InScopeIn` input, `unwCondsB` of the compiled functions gives
  `unwFnsB`). **Totality with unwinding on `lean-ld`'s inputs** (`FV/Link/ExeULdIn.lean`):
  `Link.DeadCleanup.compileExeU_total_ldIn` — `compileExe_total_ldIn`'s premises plus `unwCondsB`:
  `lean-ld` links, `compileExe` succeeds, and `compileExeU` succeeds once the written executable
  passes `ehOkR`; witness `ULdInWitness.compileExeU_total_ldIn_witness`.
  **Measured** (report only: `lake exe lean-link` prints `unwinding conditions:` per executable,
  `Link.DeadCleanup.unwReport`; debug, panic=unwind, `--lean-link --verified`, lean-ld): fv-demo
  2 executables (461 and 903 functions, 83/173 with `try_call`), survey 18 executables (3,179
  functions, 498 with `try_call`), fv-demo `--build-std` (28,554 functions, 3,596 with
  `try_call`) and deps' `deps_demo` (17,091 functions, 2,588 with `try_call`): `tryTablesB` 0,
  `unwCheck` 0, `ehOkR` 0, `lastCallsOk` 3 in deps (3 `regex` functions; 5 before #484) and 1 in
  std (measured before #484). Before #549 the frame condition `saveFrameB` was a real run-time
  limit (a > 32 KiB spill area stored the callee-saves through x16 without CFI rows; repro on
  #479, `examples/bigframe-unwind`); Cranelift's frame pushes them under the frame record, so
  the limit is gone.
  **Without `unwCheck`** (`FV/Link/UnwCondIn.lean`): `unwCondInB g a` =
  `tryTablesB`, `tryRetsB`, code below 4 GiB;
  `Link.EhCheck.Complete.unwCondB_of_in` (by `unwCheck_complete`),
  `unwCondsB_of_in` (`InScopeIn` lift), `Link.DeadCleanup.compileExeU_total_ldCond`; witness
  `ULdCondWitness.compileExeU_total_ldCond_witness`. Measured (debug, panic=unwind,
  `--lean-link --verified`): deps without std, 4 executables (15,200–19,845 functions,
  2,321–2,988 with `try_call`), every condition 0 (`lastCallsOk` 3 → 0 by #515); fv-demo 0.
  Open: completeness of `lastCallsOk` (#518) and `ehOkR` on lean-ld's output (#519).
  **The outgoing bound from the input** (`FV/Backend/Proof/IselOutBound*.lean`,
  `FV/Link/UnwOutIn.lean`): the input condition **`outBoundB g`** (`outBoundLe 32560`: every
  `call`/`call_indirect` statement and every `try_call`/`try_call_indirect` terminator passes at
  most 32560 bytes on the stack, `stackBytes` of the callee's, the `call_indirect`'s or the
  exception table's signature) bounds the outgoing area:
  `Backend.Proof.OutBound.lowerFunction_outgoing_le` (`LowerScope f → outBoundLe Bd f = true →
  lowerFunction f = .ok vc → vc.outgoing ≤ Bd`), carried through `prune`/`prepare` by
  `Link.EhCheck.Complete.vcp_outgoing_le`. Parts: only `gen_call_info`/`gen_call_ind_info` change
  the outgoing area (`externCtor_out`, by the `externCtor_split` automation); neither is in the
  certified term set `callTab` (one kernel decision each), so runs of every rule but 1031–1036
  keep it (`UModel` `outModel`), and the `call`/`try_call` rules set it to
  `max outgoing (stackBytes sig)` exactly (`call_bl_outEq`, `call_got_outEq`, `call_ind_outEq`,
  `try_bl_outEq`, `try_got_outEq`, `try_ind_outEq`); `lowBlocks_bnd` carries the bound through the
  recorded lowering. Witness `OutBound.Witness.outgoing_le_applies` (ten `i64` arguments: the
  bound 16 is reached).
* **The executable-bytes machine with unwinding (S10g, #404)** (`FV/E2E/DeadCleanupExecUnwind.lean`):
  `E2E.DeadCleanupExecBytes.stepU I B Ub file` is `DeadCleanupExecBytes.step` (the processor on
  the file's words; calls of code outside the program and TLS by the base hooks; a call of a
  function of the program is executed from the file's words), except at a call of code outside
  the program whose callee raises (`Ub`, `LinkSysU.Ub`: the callee and every frame below it
  unwound, the call's state restored), where one step runs **phase 2 of the unwinder on the file's
  tables** (`walk`, the unique end of the frame walk `Walk`): the frame of return address `ra` is
  looked up in the file at `ra - 1` (`Link.EhCheck.unwTables`, libunwind's lookup of a caller's
  frame) and handled by `Unw.unwindAt` (`unwFrame`: the personality installs a landing pad, unwinds
  the frame by its row, or stops); a frame unwound by its row (`Continues`) whose restored return
  address designates program code (`img I (ra' - 1)`) continues the walk with that frame, otherwise
  the walk ends there (a pad, an error, or the exception leaving the program: an AAPCS64 return to
  the outside caller, x0 the exception object). The model is `LinkSysU.machU` of the input
  (`uSys`, `machU_uSys`). **`act_simU`**: every activation of the nested machine is simulated
  (`Sim`: registers, memory but at the relocated instruction bytes), and an activation that leaves
  its frame by unwinding is matched by the executable's raising step whose walk (`Pending`) is at
  the caller's frame, so the walk composes frame by frame across the nested activations
  (`frame_out`: one frame's phase 2 on `Sim`-related states, given the frame's save slots off the
  relocated bytes, `RestoreOk`; `unwFrame_call`: the file's lookup at a call of `g` is `g`'s tables,
  `TabsOk` from `compileExeU_tables`). `exec_of_modelU` transfers `ArmRefinesU` to **`ExecRefinesU`**
  (a return, a trap, the exception leaving `f` with ExnRel on x0, the live CLIF bytes outside the
  relocated instruction bytes as the memory; `ExecRefinesU.toExec`: `ExecRefines` for runs without
  exceptions). Theorems (`FV/Link/ExeUnwindExec.lean`, `FV/Link/OptExeUnwindExec.lean`):
  **`Link.DeadCleanup.compileExe_correct_unwind_exec_of_good`** (no reachable call cycle),
  **`compileExe_correct_unwind_exec_peak_of_good`** (the run's peak call depth),
  **`compileExeOpt_correct_unwind_exec_peak_of_good`** (through the mid-end): under
  `compileExeU`/`compileExeOptU`, `compileExe_correct{,_peak}`'s premises for the outside call in
  `r`, `compileExe_correct_unwind{,_peak}`'s for the linked program with unwinding with that call's
  world, the raising base callees reading no relocated instruction byte (`UnwSim`, `HooksSim`'s
  counterpart) and the outside caller's call instruction no program code (`¬ img I (x30 - 1)`:
  else libunwind would take the caller's frame for a program frame), the executable machine with
  unwinding from `r` refines the whole-program run with unwinding, given `RunOkU`, the per-state
  facts of the model's run with unwinding (`StepOkU`: `StepOk` on `machU` plus `RestoreOk` at a
  raising call; a frame left by unwinding lands on its return). **`RunOkU` is proven**
  (`FV/E2E/DeadCleanupExecUnwindGood.lean`, `runOkU_of_good`) from the per-state facts the linking
  statement with unwinding exports (`LinkSysU.ThmGU`, `RunGoodLU`: `actGoodXU` — `RL.GoodX` or a
  raising call state `RLU.RaiseXF` with D1, the exit landing on the return, the restored `sp`, a
  `blr`'s facts, the callee contract's premise, and `FrameOkU`: the save slots the frame's row
  restores lie in the activation's frame — at every state of `ReachLU`;
  `backend_correct_program_budgetUG'`/`_peakUG'`), so the theorems without it are
  **`Link.DeadCleanup.compileExe_correct_unwind_exec`**, **`compileExe_correct_unwind_exec_peak`**,
  **`compileExeOpt_correct_unwind_exec_peak`** (`FV/Link/ExeUnwindExecGood.lean`), with
  `HooksSim` (as `compileExe_correct`) instead of `RunOkU`. Witnesses:
  `Link.DeadCleanup.UnwindExecWitness.exec_applies`/`opt_exec_applies`,
  `UnwindExecGoodWitness.exec_applies`/`opt_exec_applies` (closed base, `BaseOk` discharged), and on `%rec`'s written
  executable the walk's frame computed: `frame_continues` (the file's lookup, no LSDA, a CFA rule:
  the self-call's frame is unwound in every state), `frame_eq` (its phase 2 on the file is the
  model's), `walk_out`.
* **Validators**: `lowerCheck` re-runs the `try_call` lowering (`lowTerm`, `TryLow`), checks the
  normal-return edge block (`succOk`: its `jump`, no parameters, the branch arguments
  `normArgReg`, `retN` indices below the callee's return count), and checks that a `tryCall`
  appears in the VCode only when the function has a `try_call` (`noTryCall_of_check`);
  `prepCheck` keeps that (`noTryCall_of_prepCheck`) and `ctlCheck` rejects a `clobberAll` try
  call; `shapeOk` checks `st0.nextVreg ≤ f.freshValue` (the call's result values never
  overwrite a value of `f`, `LowerShape.fresh`).
* **Proof**: `term_step_try` (`LowerSim.lean`) matches the two CLIF steps with the
  terminator's code up to the `tryCall` (M4: `LowerTryOk`, from `TryRulesCorrect`/
  `TryUnmatchable`, `tryCalls_of_rules`), the goto to the normal-return edge block and its
  `jump`; `sim_run` is by strong induction on the fuel. Register level: `realizes_tryCall`
  (`bl`/`blr`, then `b continuation`).
* **Try-free functions**: every new premise is vacuous (`hCT`, `TrapsExplicit.tryCall`,
  `InSubset.tryExterns`), so the statement specialises to the former one. The mid-end and
  `i128` theorems (`backend_correct_opt`/`_opt_proven`, `backend_correct_legal`) keep
  `try_call` out with an explicit premise (`hnt : ∀ B ∈ f.blocks, B.term.isTry = false`);
  `lean-backend` flags such functions unverified under `--opt`/`--opt-proven-only`.
  `backend_correct_legal` covers `try_call` since agent/last-unverified
  (`docs/contracts/legalize128.md`).

### `tls_value` (one thread; TLSDESC hook in M6, real local-exec words on the executable)

`Clif.run` has one thread: `tls_value.i64 gvN` of `gvN = symbol tls %v` gives the address of
the memory's symbol `v` (`Clif.Mem.symbols`, as `symbol_value`). The backend lowers it by
Cranelift's `elf_gd` rule to `ElfTlsGetAddr v x0 tmp`, emitted as the TLSDESC sequence
`adrp x0, :tlsdesc:v; ldr tmp, [x0, :tlsdesc_lo12:v]; add x0, x0, :tlsdesc_lo12:v; blr tmp;
mrs tmp, tpidr_el0; add x0, x0, tmp`.

* **Scope**: `Compile.instE` admits `tls_value.i64`, `globalE` admits `symbol tls`; a `tls`
  symbol with an offset is rejected by the lowering (`instData`, Cranelift drops the offset).
* **M4**: `tls_value_ok` (rule 1129, `IselTls.lean`) from `MemRefines`' TLSDESC clause (the
  first def is the linked symbol's address, the world agrees up to the flags);
  `tls_value_macho_ok` (rule 1130) never matches (`tls_model` is `elf_gd`).
* **M6**: `csem` (`ElfTlsGetAddr` is `isCtl`) gives the defs `[X.sym v 0, X.tp]` and the world
  with the flags `X.tlsFlags v w`. The machine `ArmStepX` hooks the sequence: the `adrp` only
  advances the pc, and at the `ldr` the rest runs as one step `H.tls v tmp`. Its contract
  `TlsOk F X H` (`FV/E2E/RegLevelTls.lean`, premise `hTls`) is trusted: the step ends after
  the sequence, x0 is `X.sym v 0`, `tmp` is `X.tp`, every other register but x30 and the flags,
  the memory and the program are unchanged, and the flags are `X.tlsFlags v w` for a world `w`
  of the state. `os_tls`/`realizes_tls` prove the item case of `realizes_all` from it.
  `RunsAs` counts the machine steps existentially (the hooked sequence takes 2 steps for 6
  lines).
* **x30** is in `Masked` (the `blr` writes it); see `docs/contracts/regalloc-proof.md` for why
  this does not weaken the statement for other functions.
* **Validators**: `lowerCheck` checks `hasTls f || !vc.hasTls` (`noTls_of_check`), `prepCheck`
  `vc.hasTls || !vcp.hasTls` (`noTls_of_prepCheck`), so `hTls` is needed only for a function
  with a `tls_value` (`hasTls_of_vcode`); `ctlInstOk` requires both defs to be int vregs.
* **Mid-end and `i128` theorems**: `backend_correct_opt`/`_opt_proven` take `hTls` for the
  optimised function, `backend_correct_legal` for the legalised `g`.
* **Executable, hook-free (T1, #37)**: in a static executable rust-lld (and `leanLink`)
  relaxes the sequence to local exec, `movz x0, #hi, lsl #16; movk x0, #lo; nop; nop; mrs tmp,
  tpidr_el0; add x0, x0, tmp` with `hi * 2^16 + lo = TpOff` (`BinCheck.RelocOk` checks the four
  relaxed words). The Arm model has the thread pointer (`StateField.TPIDR`, `MRS TPIDR_EL0`,
  co-simulated against qemu), so `E2E.ExecBytes.binary_correct_exec_proven_tls` (`_depth_`,
  `_peak_`; `FV/E2E/ExecTlsProven.lean`) and `Link.compileExe_correct_tls` (`_depth`, `_peak`;
  `FV/Link/ExeTls.lean`) are about the machine `stepT`, which runs these six words on the
  processor (only calls of code outside the program are hooks). The M6 machine of the proof
  still hooks the sequence, with the base environment `leBase I B file`: its hook `leTls` is what
  the six words do given the thread pointer `B.tp`, so `TlsOk` holds by construction
  (`tlsOk_le`) and so does `HooksSim`'s TLS clause (`hooksSim_le`); `tls_step` proves the model's
  two steps against the executable's six; D1 for the TLSDESC `ldr` word (`TlsCf`, from
  `GoodX.next`: `Insn.pairFirst` includes `adrpTlsDesc`; `emitFunc_tlsClosed`) and the thread
  pointer being unchanged by every model step (`mach_tpidr`, `Arm.r_TPIDR_exec_inst`) are
  proven. What stays is the **loader's thread-pointer contract** `TlsLoader I B file r`: the
  entry state's `TPIDR_EL0` is `B.tp`, code outside the program keeps it, and the running
  thread's instance of each thread-local variable of a TLSDESC relocation is at
  `B.tp + TpOff`, the address the CLIF semantics gives it (`I.symAddr`). Since `I.symAddr` of a
  TLS symbol is its `st_value` (its offset in the TLS segment), the address clause pins
  `B.tp = -tlsA file` (`tlsLoader_addr_canon`): the theorem is about the thread whose TLS block
  the CLIF memory's symbols denote. `baseOk_closedLe` shows `BaseOk` of `leBase` satisfiable for
  programs with `tls_value` (the closed base needs none).

### Indirect calls and function addresses

**Semantics (trusted-semantics growth).** `Clif.stepCallIndirect` (`FV/Clif/Run.lean`) takes the
callee value as a code address. A function of the program at that address is entered, as
before. Otherwise it now calls the extern at that address
(`Clif.callExternAt`): the first name of `env.names ++ Program.externNames` (the environment's
further code symbols — empty by default, agent/link-scope —, then the externs the functions of
`p` declare, which `Program.initMem` gives link-time `symbols`) whose address is the callee
value, run as `env.extern` with the argument and result types checked against the call site's
`sigN`, like `Clif.stepCall`; an extern whose signature the environment knows (`env.sigOf`,
none by default; `Clif.linkEnvN` gives each function of the linked program its own) is called
only when `sigN` matches it (`Signature.abiMatch`, agent/scope-widen, "Widening 14"). Before
this change such calls were stuck.
`Clif.stepTryCallIndirect` inherits it. `docs/contracts/clif-subset.md` records the change;
`scripts/clif-filetests.sh` and the differential tools are unchanged by it (see there).

* **Scope** `InSubset.indSigs`: the call-site signatures of the indirect calls (`Backend.indSigs
  f`: the `sigN` of each `call_indirect` and each `try_call_indirect`'s exception table) have
  at most 8 parameters and pass `sigAbiOk` (`Backend.indSigsOk`, part of `Backend.verifiable`).
  `InSubset.noCI`/`noFA` and `CtxInv.noFA` are gone; `CtxInv.resTys` takes a `call_indirect`'s
  result types from its `sigN` declaration. `Compile.termE` admits `try_call_indirect`.
* **Run premises** `TrapsExplicit.indirect`/`tryIndirect`: at a `call_indirect` statement /
  `try_call_indirect` terminator of the entered function, no function of `p` is at the callee
  address (such a call enters that function: calls between the program's functions are
  outside the theorem, as `InSubset.externCalls` excludes direct ones);
  `TrapsExplicit.tryCallInd`: a `try_call_indirect` does not trap (the callee returns normally).
* **Contract** `XCallsIndOk env (indSigs f) MR X` (`FV/E2E/RegLevelDriverSem.lean`): for each
  call-site signature, a `blr` (`X.call none (u :: args)`) whose target's low 64 bits are
  `X.sym n 0` of an extern `n` of `env` whose known signature (`env.sigOf n`, if any) the call
  site's matches, on arguments of the call site's parameter types (as `Clif.callExternAt`
  checks both), returns what `env.extern n` returns (one output per
  `sigRets`, the results first, the memory relation kept) — the clause `XCallsOk` states for a
  GOT call of a declared non-colocated extern, for every extern of `env`. With `hsym` (the external
  semantics' symbol addresses are the linked ones) and `MemRel.symbols` it gives the M4
  contract `IndCallsRefine` for `csem` (`indCallsRefine_csem`).
* **Rules** (M4): `rule_lower_2529` (`call_indirect`, id 1033: `blr` of the callee value's vreg
  under the call site's ABI, `call_ind_ruleOk`, `IndRulesCorrect`), `rule_lower_2486`
  (`func_addr`, id 1026: `load_ext_name` of the declaration at offset 0, as `symbol_value`;
  `func_addr_ok`, in `MemRulesCorrect`), `rule_lower_2561` (`try_call_indirect`, id 1036 of
  `lower_branch`, `try_ind_ruleOk`, `TryIndRulesCorrect`/`TryIndUnmatchable`). `LowerTryOk` is
  stated for the call instruction of the terminator (`.call fn args` resp.
  `.callIndirect et.sig callee args`), and `term_step_try` covers both (`IsTryWith`).
* **Driver**: `step_stmt`/`stepCallIndirect_eq` relate a `call_indirect` step to `instOutcome`
  (the extern at the address) under the run premise; `lowerCheck` re-runs the lowering of both
  terminators (`lowTerm`, `succOk`, `edgeIds`) and checks `sigDecls`-based result types
  (`ctxResTysOk`).
* **Specialisation**: for a function without `call_indirect`/`try_call_indirect`,
  `indSigs f = []` (`indSigs_eq_nil`), so `InSubset.indSigs` and `hXI` are vacuous
  (`InSubset.of_indirectFree`, `xCallsIndOk_nil`, `backend_correct_final_indirectFree`) and so
  are the new `TrapsExplicit` clauses (`TrapsExplicit.of_indirectFree`): the statement is the
  former one.
* **Mid-end**: `lstep` does not model `call_indirect`, so `backend_correct_opt`/
  `_opt_proven` keep the premise that the function has none (`hci`, next to `hnt`); the
  indirect-call contract is then vacuous. `lean-backend` flags `call_indirect` functions
  unverified under `--opt`. **`i128`** (agent/last-unverified): `backend_correct_legal` covers a
  `call_indirect` without `i128` operands (premises `hXI` and `hind`) and `func_addr`
  (`Opt.Legal.check` rejects `try_call_indirect`).

### Calls of the function itself (recursion, `cargo fv`)

`InSubset.externCalls` excludes calls of functions in the activation's program. The driver
uses `P.bare`, whose function table is empty: every call, including a direct self-call, uses
the environment's callee contract. `Backend.verifiable` checks the local subset and signature
conditions; `InSubset.of_verifiable` proves these imply `InSubset P.bare f`.

`cargo fv` compiles the original self-declaration and call without renaming symbols or
creating an alias body. Linking supplies the whole-program contract for the callee at `f`'s
own address; `DeclN` includes the caller's own name. Taking that address is also supported.
This is a per-activation guarantee, not an assumption that recursion terminates or has a
fixed stack bound. `compileExe_correct` requires no reachable call cycle;
`compileExe_correct_depth` (L1d, #204) covers recursive entries with `frameDrop + D·M` bytes of
stack for a run of at most `M + 1` steps, and `compileExe_correct_peak` with `frameDrop + D·d`
bytes for a run of peak call depth `d`, whatever its length ("The executable compiler",
"Recursive programs").
`E2E.LinkWitness.DirectSelf` witnesses a native recursive CLIF function's `InScopeP`, local
verification and self edge, and proves its depth-independent stack budget is `none`;
`Crates.CompileExeRecWitness` compiles it with `compileExe` and applies
`compileExe_correct_depth` to a concrete run, `Crates.CompileExePeakWitness`
`compileExe_correct_peak` to one whose stack is too small for the fuel premise.

**#88 integration verification:** full Lean/tool build and crate proofs pass; all 14 audited
theorems use only permitted axioms. Filetests: corpus 114/114, extra 22/22, runtests 4672
passed with no failures (existing 7 errors unchanged); encoding 1292 identical, 0 different;
E2E checker 1150 accepted, 0 rejected. `cargo fv test --lean-link --keep-temps` passes all
20 fv-demo tests, including recursive calls returning the function's own address; the report
marks `recursive_address` verified in both compiled units, not fallback. Both executables
are written by `Link.compileExe`, binary checks 2/2. Survey tests: 53 passed, binary checks
18/18. `cargo fv run --lean-link --keep-temps` on deps compiles 17,091 functions, passes its
binary check and runs the JSON/hash/word-count/factorial program. Unwinding is exercised,
not newly proven; CLIF semantics are unchanged.

* **Regression file**: `corpus/clif-regress/call_indirect.clif` (a vtable built with
  `func_addr` and dispatched through, a function address returned as a value, `try_call_indirect`).

### Self tail calls as loops (S8a, #32, 2026-10-22, `agent/return-call-s8`)

The backend rejects `return_call`. A function's `return_call` of **itself** is compiled as a
loop before the backend, so the executable reuses the frame and the stack does not grow per
tail call.

* **Transform** (`FV/Opt/TailLoop.lean`, kept free of proofs): `selfTail f fn` — `fnN`
  declares `f`'s own name with `f`'s parameter and return types; `eligB f` — no stack slots, no
  `try_call`/`try_call_indirect`, the first block's parameter types are the signature's, at
  least one self `return_call`. `loop f` (else `f`): a new entry block (id `newId f`, fresh
  parameters `freshValue f + i` of the first block's types, `jump b0(q)`) before `f`'s blocks,
  each self `return_call fnN(args)` replaced by `jump b0(args)`.
* **Refinement** (`FV/E2E/TailLoopSim.lean`): `Opt.TailLoop.TailRel P P'` (each function of `P'`
  is its counterpart of `P` or `loop` of it). `TailRel.refines`: for distinct names in `P`,
  externs keeping the slot-placement oracle (`Clif.EnvKeepsPlace`) and entries `cs`, `cs'`
  (`ClifEntry`, same arguments, slots, memory) with a consistent oracle stack at `cs`
  (`SpsOk`), `Clif.runLoop B P' m cs'` returns/traps as `Clif.runLoop B P k cs` for some `m`,
  and when `P`'s run is final, `DepthLe B P d cs → DepthLe B P' d cs'`. Simulation `TR`: equal
  memories, callers pairwise related, frames related by `FRm m` (`false`: the same function,
  registers extended; `true`: the eligible source function and its `loop`, terminators
  `termT`); a source step is one target step, two when it enters a transformed function (the
  new entry block's `jump`). The self `return_call` step (`selfTail_rel`): `Clif.run` frees no
  slot (none), pops the activation's oracle stack pointer and pushes the same one
  (`selfTail_mem`, from `SpsOk`), re-enters the first block with fresh registers; the target's
  `jump` keeps its (larger) registers.
* **Executable compiler** (`FV/Link/TailCompile.lean`, `FV/Link/TailExe.lean`,
  `FV/Link/TailExeLd.lean`): `FnInput.tail` (the transformed function printed after the file's
  header, used when it parses back to itself), `LinkSpec.tail`, `Link.DeadCleanup.compileExeTail S
  = compileExe S.tail`. `compileExeTail_correct`, `compileExeTail_correct_peak`: the premises of
  `compileExeOpt_correct{,_peak}` on `S.tail` plus `Clif.EnvKeepsPlace B.env` and `SpsOk cs`,
  without the optimiser's register equality (the transformed entry binds the new block's
  parameters); the conclusion is about `prog S.inputCleanup` (self `return_call`s included),
  the peak variant with `frameDrop (art S.tail.inputCleanup f').af + D * d` for the **input**
  run's depth `d`. `compileExeTail_total_reach_input`, `compileExeTail_total_ld`:
  `compileExe_total_reach_input`/`file0OkB_ld` on `S.tail` (`withSizes_tail`).
* **Witness** `Crates.DeadCleanupExeTailPeakWitness.cleanup_tail_peak_witness`: `sum(n, acc)`
  (`return_call sum(n - 1, acc + n)`) compiled by `compileExeTail`; the input run of
  `sum(10, 0)` returns `55` with call depth `0`; with `frameDrop + D * 0` bytes of stack the
  executable machine returns `55` in x0.
* **Not covered**: DEFERRED "Tail calls" (`return_call` of another function, `return_call_indirect`,
  the `tail` convention, slots/`try_call`, the source-level and `--opt` variants).

### Callee contract with a dead stack (2026-10-02, `agent/callee-fix`)

**The flaw.** `CalleeOk.os` was `OperandsSound F (callExec H) (csem F ctx X) (.call info)`: from
every state `s` with the caller's world `w` (`SameWorld F s w`), the hooked callee's state had to
equal `X.call`'s world on all memory outside the caller's frame addresses `F`. `X.call` sees only
`w`, which masks the pc, x30 and the allocatable registers; a callee that stores its return
address `pc + 4` (or a callee-saved register, or a spill) below `sp` writes bytes outside `F` that
depend on them. So no such callee met the contract whenever its `X.call` returned (proven on
main: `E2E.calleeOk_mem_world`, `E2E.calleeOk_saves_lr_false`), and every end-to-end theorem was
vacuous for a function calling a callee with a frame — our own prologue
`stp x29, x30, [sp, #-16]!` included. Auditing the other per-call clauses found a second
obstruction of the same kind: `os` quantified over **every** `CallInfo`, including calls whose
def registers are not the callee's return registers. Two calls of the same callee with the same
arguments, one defining x19 (allocatable, not clobbered) and one without defs, force the hooked
callee to both write `X.call`'s result to x19 and preserve x19: unsatisfiable whenever `X.call`
returns a value — which `XCallsOk` demands for every extern with a return.

**Old premises** (main 5a3ee06), with `FF s := frameF lo hi af s`
(`lo`/`hi` = `intBase`/`size` of `RAFrame.compute vcp rf`):

```lean
structure CalleeOk (F : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks) : Prop where
  os : ∀ ctx info, OperandsSound F (callExec H) (csem F ctx X) (.call info)
  pc : ∀ d s, Arm.r .ERR s = .None → Arm.r .PC (H.call d s) = Arm.r .PC s + 4
  ext : ∀ d uses w outs w', X.call d uses w = some (outs, w') → Arm.r .ERR w = .None →
    Arm.r .ERR w' = .None ∧ w'.program = w.program
def CalleeTryOk (F) (X) (H) : Prop := ∀ ctx info ti c wh ops regs i' s w outs w', …
structure TlsOk (F) (X) (H) : Prop where …
  seq : … → (∀ a, (H.tls n (.x k) s).mem a = s.mem a) ∧ …
def StackAvail (af) (s) : Prop := af.frameSize + 16 ≤ (spv s).toNat ∧ ∀ a, CodeAddr s a → …
(hC : ∀ s, CalleeOk (FF s) X H) (hCT : … → ∀ s, CalleeTryOk (FF s) X H)
(hTls : … → ∀ s, TlsOk (FF s) X H) (hres : StackAvail af s)
(hX hXI hrel : … Rel.holds ⟨FF s, …⟩ …)
```

**New premises** (`FV/E2E/RegLevelSim.lean`, `RegLevelCall.lean`, `RegLevelTry.lean`,
`RegLevelTls.lean`, `Statement.lean`; `OperandsSoundCtlAt` in
`FV/Backend/Proof/RegallocOperands.lean`), with a new theorem parameter `K : Nat` (the callees'
stack budget) and `FF s := frameW K lo hi af s`:

```lean
def StackBelow (K : Nat) (sp a : BitVec 64) : Prop := a.toNat < sp.toNat ∧ sp.toNat ≤ a.toNat + K
def frameW (K lo hi : Nat) (af : AFunc) (s : Arm.ArmState) (a : BitVec 64) : Prop :=
  frameF lo hi af s a ∨ StackBelow K (spv s - BitVec.ofNat 64 (frameDrop af)) a
/-- OperandsSoundCtl at one state `s`, world compared outside `F`, frame kept on `FK` -/
def OperandsSoundCtlAt (F FK) (exec) (sem) (i) (ctl) (s) : Prop
def CallSoundCtl (F : BitVec 64 → Prop) (K : Nat) exec sem i ctl : Prop :=
  ∀ s, K ≤ (spOf s).toNat → (∀ a, StackBelow K (spOf s) a → F a) →
    OperandsSoundCtlAt F (fun a => F a ∧ ¬ StackBelow K (spOf s) a) exec sem i ctl s
def VCode.CallSite (vc : VCode) (info : CallInfo) : Prop  -- a `call`/`try_call` of `vc`
structure CalleeOk (F : BitVec 64 → Prop) (K : Nat) (X : ExtSem) (H : ArmHooks)
    (S : CallInfo → Prop) : Prop where
  os : ∀ ctx info, S info → CallSoundCtl F K (callExec H) (csem F ctx X) (.call info) .next
  pc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (H.call d s) = Arm.r .PC s + 4
  ext : (unchanged)
-- `callExec H` runs the hook only from an aligned `sp` (AAPCS64)
def CalleeTryOk (F) (X) (H) (S : CallInfo → Prop) : Prop := ∀ ctx info ti, S info → (as before)
  -- since agent/trycall-contract: S : CallInfo → TryInfo → Prop, results only ("`try_call` payload registers")
structure TlsOk (F) (K : Nat) (X) (H) : Prop where …
  seq : … → K ≤ (spOf s).toNat → … ∧ (∀ a, ¬ StackBelow K (spOf s) a →
    (H.tls n (.x k) s).mem a = s.mem a) ∧ …
def StackRoom (n : Nat) (s) : Prop := n ≤ (spv s).toNat ∧ ∀ a, CodeAddr s a → n ≤ (a - (spv s - n)).toNat
def StackAvail (K : Nat) (af) (s) : Prop := StackRoom (af.frameSize + 16 + K) s
(hC : ∀ s, CalleeOk (FF s) K X H vcp.CallSite)
(hCT : … → ∀ s, CalleeTryOk (FF s) X H vcp.CallSite)
(hTls : … → ∀ s, TlsOk (FF s) K X H) (hres : StackAvail K af s)
(hX hXI hrel : … Rel.holds ⟨FF s, …⟩ …)    -- FF s now includes the dead stack
```

The conclusion `ArmRefines` and every other premise are unchanged. `RegLevelCorrect` takes `K`
(its `StackAvail K` premise); `backend_correct`/`_of_rules`/`_m4` take it through `hM6`.

**Why the new callee premises are weaker.** For every `F`, the old `CalleeOk F X H` implies the
new `CalleeOk F K X H S` for every `K` and `S`: `CallSoundCtl` only adds preconditions (`K ≤ sp`,
the dead stack outside the world, membership in `S`, an aligned `sp` for `pc`) and only weakens
the frame clause (`FrameKeep` outside the dead stack); the memory comparison is the same
`SameWorld F`. With `K = 0`, `StackBelow 0` is empty, so `frameW 0 = frameF` and `StackAvail 0`
is the former `StackAvail`: the new theorem at `K = 0` is the former one with the weaker callee
contract. For `K > 0` the world excludes the dead stack, which is what makes the callee premises
satisfiable by real callees (they write state-dependent bytes there), at the price of two run
premises that real setups meet: no live CLIF byte in the `K` bytes below the body's `sp`
(`MemRel.valid` against `frameW`, and `OutRel` for the outgoing area) and no code there
(`StackAvail K`).

**Why they are sufficient.** The proof only uses the contract at its call sites, from `Q`: there
`sp` is the body's `sp` (`StRel.sp`), so the dead stack of the call is exactly the activation's
(`RL.F = frameW R.K …`), `K ≤ sp` follows from `StackAvail K` (`RL.K_le`), and the frame
addresses `R.FK = frameF …` (spill/save slots, fp/lr, code) are disjoint from it
(`frameF_not_below`, `RL.FK_not_below`), so they are kept (`RL.callAt`). The simulation relation
`Q` compares the world outside `R.F` and keeps the frame on `R.FK` (`realizes_op_core` takes
`OperandsSoundCtlAt R.F R.FK`; the straight-line instructions' `OperandsSound R.F` give it by
`OperandsSoundCtl.at`). Nothing the theorem tracks lives in the dead stack: live CLIF bytes avoid
`FF s` (`MemRel.valid`), the explicit stack slots and the outgoing area are at or above the body's
`sp`, the stack-passed parameters above the entry `sp` (`stackArgsAvoid_frameW`). The register
part of the contract (results in the def registers, x19–x28 and the low halves of v8–v15 kept,
x16/x17 and x30 masked, `sp`, x18, x29, flags and the other unmasked fields as `X.call`'s world)
is unchanged: a real callee computes its results and flags from its arguments and the world, and
restores the callee-saved registers. The call-site restriction removes only calls the compiler
never emits.

**Audit of the other per-call clauses.** x30, x16/x17, the allocatable registers and the pc are
masked (no change); the v-registers: only the low 64 bits of v8–v15 are kept (AAPCS64); flags: part
of the world, given by `X.call` (a callee's flags are a function of its arguments and the world);
`TlsOk`: the memory clause had the same flaw (a dynamic TLSDESC resolver saves registers on the
stack) and now leaves the dead stack unspecified; `XCallsOk`/`XCallsIndOk` constrain only `X`
(no machine state), `ext` only `X.call`'s error flag and program; `BodyEntry` (`w₀.mem = s.mem`,
registers as at entry) relates the caller-chosen body world to the entry state and is met by
construction; `AbiEntry` and `StackAvail` are facts of the entry state. `CalleeTryOk` had the
remaining flaw, fixed next.

### `try_call` payload registers (2026-10-02, `agent/trycall-contract`)

**The flaw.** A `try_call`'s call defines its results, then the exception payload registers
that are not return registers (`gen_try_call_rets`: x0/x1 after fewer than two results). The
former contract (over the call sites `vcp.CallSite`, every `ti`) was

```lean
def CalleeTryOk (F) (X) (H) (S : CallInfo → Prop) : Prop :=
  ∀ ctx info ti, S info → ∀ c wh ops regs i' s w outs w', … →
    csem F ctx X (.tryCall info ti) (useVals ops regs s) w = some (outs, w', .goto ti.handlers.length) →
    ∃ s', callExec H i' s = some s' ∧ ∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2
```

and `csem` gives the payload defs `regVal p.2 d.1` of `X.call`'s world `p.2`. A callee that does
not write x0/x1 leaves the caller's values there, which the world masks (`SameWorld` ignores the
allocatable registers): no `X` can know them, so the contract was unsatisfiable for such callees
and every theorem vacuous for every function with a `try_call`.

**The fix.** On the normal return the payload defs are dead (only the handler edges read them):

* `TryInfo.rets` (set by `tryInfoOf` to `(sigRets sig).length`) counts the call's results;
  `MInst.normalDead (.tryCall _ ti) = some (ti.handlers.length, ti.rets)`: the defs past the
  first `ti.rets` are dead on the edge to successor `ti.handlers.length`.
* **Allocated-code semantics** (`FV/Backend/Proof/VCodeSem.lean`): `HavocOuts i ctl outs outs'`
  now takes the control outcome; `havocFrom i ctl` is `keptDefs` or, for a `try_call`'s call with
  outcome `goto ti.handlers.length`, `some ti.rets`: the payload defs take any value there.
  `csem` is unchanged (its payload values no longer matter).
* **Regalloc checker** (`FV/Backend/RegallocCheck.lean`): `CheckCtx.edge b s` is
  `edgeCopy b s (edgeForget b s a)`; `edgeForget` forgets the dead defs of `b`'s terminator when
  `s` is the successor `normalDead` names (`forgetOps`), so the payload vregs stay available on
  the handler edges and leave every set on the normal-return edge. Soundness: `op_sound` gives the
  invariant after the instruction with those defs forgotten (`tryForget i ctl ops`),
  `edgeForget_inv` turns it into the invariant of `edgeForget` (equal forgetting on the normal
  edge; more when another successor number reaches the same block), `checkAlloc_sound` unchanged.
* **The contract**, over the compiled code's `try_call` sites:

```lean
def VCode.TrySite (vc : VCode) (info : CallInfo) (ti : TryInfo) : Prop  -- a `tryCall info ti` of `vc`
def CalleeTryOk (F) (X) (H) (S : CallInfo → TryInfo → Prop) : Prop :=
  ∀ ctx info ti, S info ti → ∀ c wh ops regs i' s w outs w' s', … →
    csem F ctx X (.tryCall info ti) (useVals ops regs s) w = some (outs, w', .goto ti.handlers.length) →
    callExec H i' s = some s' → ∀ p ∈ (defRegs ops regs outs).take ti.rets, regVal s' p.1.2 = p.2
(hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk (FF s) X H vcp.TrySite)
```

**Weaker.** The old contract implies the new one: `callExec` is deterministic, the new clause
asks for a prefix of the old def list, and only at the `try_call` sites (with their own `ti`).
At sites whose callee returns nothing (`ti.rets = 0`) it holds for every hook
(`calleeTryOk_of_rets0`); otherwise it asks what `CalleeOk` already says of the results `X.call`
returns, for the first `ti.rets` defs.

**Sufficient.** `realizes_tryCall` takes the world, frame, kept registers and callee-saved
registers from `CalleeOk` at the plain call (`RL.callAt`), the results from `CalleeTryOk`, and
lets the `MStep` write the values the callee left in every def register (`HavocOuts` with
`take_machine_defs`; `operandsSound_post` builds the store), so `Q` holds at the normal-return
successor. Acceptance: no allocation of the corpus reads a payload vreg on a normal-return edge
(lean-backend-regalloc-test: 0 allocation errors).

### Linking (2026-10-02, `agent/link-proof`)

`cargo fv` compiles each function `f` of a program `P` as its own CLIF file, in which every
other function of `P` is an extern; `backend_correct_final` is per function. This section states
what is proven about putting them together, and why the program callees' contracts are still
premises.

**CLIF layer** (`FV/E2E/LinkClif.lean`, namespace `Clif`; no change to `Clif.run`):

```lean
def Program.only (p : Program) (f : Function) : Program := { p with funcs := [f] }
/-- the run with unbounded fuel: the outcome of any run that ended, else `outOfFuel` -/
noncomputable def runLim (env : Env) (p : Program) (s : State) : Outcome
/-- a call of a function `g` of `P` runs `g`'s whole-program run; other externs are `base`'s -/
noncomputable def linkEnv (P : Program) (base : Env) : Env where
  extern n := match P.func? n with
    | some _ => some fun vals mem => match initState P n vals mem with
      | .ok s => runLim base P s | .trap c => .trapped c | .stuck m => .stuck m
    | none => base.extern n
/-- no `return_call` -/
def LinkFree (g : Function) : Prop
/-- no `call_indirect`, `try_call_indirect` -/
def IndFree (g : Function) : Prop
theorem runLoop_link {P : Program} {base : Env} {f : Function}
    (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs) (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hIF : ∀ g ∈ P.funcs, IndFree g) :
    ∀ (N : Nat) (s : State), LInv P s →
      (∀ msg, runLoop base P N s ≠ .stuck msg) → runLoop base P N s ≠ .outOfFuel →
      ∃ m, runLoop (linkEnv P base) (P.only f) m s = runLoop base P N s
```

`LInv P s`: every frame (running or suspended) runs a function of `P`, at a program point of one
of its blocks or at the pending normal-return `jump` of a `try_call`. Proof: `step_below`/
`runLoop_below_*` (a run with more callers below the stack is the run without them until its
bottom frame returns, which then resumes the first extra caller), `runLoop_returned_tys` (the
returned values have the bottom frame's return types, which the atomic call checks), and a
strong induction on the whole-program fuel that matches every whole-program step with the same
per-function step, except a call (`call` or `try_call`'s call) of another function `g` of `P`,
whose whole sub-run is one atomic per-function step (`runLim`, `runLim_eq`). The two semantics
allocate `g`'s stack slots identically (`enterFunc` on the same memory, freed at its return).

**Arm side** (`FV/E2E/Link.lean`, namespace `E2E`):

```lean
structure Linkable (P : Clif.Program) : Prop where
  names : (P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ P.funcs, Clif.LinkFree g
  indFree : ∀ g ∈ P.funcs, Clif.IndFree g
theorem armRefines_link (hP : Linkable P) (hf : f ∈ P.funcs) (hinv : Clif.LInv P cs)
    (h : ∀ m, ArmRefines fb base ra astep s (Clif.runLoop (Clif.linkEnv P baseEnv) (P.only f) m cs))
    (fuel : Nat) : ArmRefines fb base ra astep s (Clif.runLoop baseEnv P fuel cs)
theorem backend_correct_linked (hP : Linkable P) (hf : f ∈ P.funcs)
    (hsub : InSubset (P.only f) f) (hc : Compiled f k vc vcp rf af fa fb) (hcov) (hC) (hCT) (hTls)
    (hX : ∀ s, XCallsOk (Clif.linkEnv P baseEnv) (f.externs.map (·.2)) (Rel.holds ⟨FF s, syms, slotOff, OB⟩ f) X)
    (hsym) (hslot) (hent) (hres) (hbe) (hargs) (hcs : ClifEntry f args cs) (hrel)
    (htr : TrapsExplicit (Clif.linkEnv P baseEnv) (P.only f) cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop baseEnv P fuel cs)
theorem xCallsOk_link
    (hbase : XCallsOk baseEnv (exts.filter fun e => (P.func? e.name).isNone) MR X)
    (hprog : XCallsOk (Clif.linkEnv P baseEnv) (exts.filter fun e => (P.func? e.name).isSome) MR X) :
    XCallsOk (Clif.linkEnv P baseEnv) exts MR X
```

(`hcov`, `hC`, `hCT`, `hTls`, `hsym`, `hslot` and the run premises exactly as in
`backend_correct_final`, with the stack budget `K`, `FF`/`OB` as in "Final hypotheses"; the
indirect-call contract is
vacuous, `indSigs_nil_of_linkFree`.) So the Arm code of `f` refines the **whole-program** CLIF
run. Its premises are those of `backend_correct_final` at `env := linkEnv P base`,
`p := P.only f`: by `xCallsOk_link` the external contract splits into the base environment's
(externs outside `P`, unchanged) and, for a callee `g` of `P`, "`X.call` realises `g`'s
whole-program CLIF semantics" — a CLIF-defined contract instead of an opaque extern.

**Scope.** Programs without `call_indirect`/`try_call_indirect` (whole-program
`stepCallIndirect` looks up the address among all functions and `p.externNames` of the whole
program) and `return_call` (its slot freeing precedes the callee's allocation); distinct function
names; this older helper requires `InSubset (P.only f)`, excluding native direct self-calls.
The current whole-program theorem instead uses `InSubset P.bare f`, so it needs no alias.
Runs in which a program callee traps remain excluded (`TrapsExplicit.stmt`).

**Trusted** (in addition to `backend_correct_final`'s): the object merge and the linker —
every function's words at its own base (`AbiEntry` per activation), `syms`/`X.sym` the linked
symbol addresses (`hsym`), and the machine model of a call: at `bl g` the machine runs the hook
`H.call` (one step) whose contract `CalleeOk`/`XCallsOk` is a premise, now also for the
program's own functions.

**Why the program callees' contracts are not discharged** (the gaps):

1. *Dead stack* — **fixed** (agent/callee-fix, "Callee contract with a dead stack"): the former
   `CalleeOk` compared all memory outside the caller's frame with `X.call`'s world, so no callee
   saving its return address below `sp` could meet it (`calleeOk_saves_lr_false`, removed with
   the old contract). The contract now leaves the callees' `K`-byte dead stack unspecified and
   holds for such callees (`E2E.calleeOk_witness`, `E2E.witness_saves_lr`).
2. *Exact world.* `X.call` must give the exact 128-bit def registers and the exact world (flags,
   memory outside `F`) of the hooked callee, while a compiled callee's theorem fixes only the
   low bits of its results and the live CLIF bytes (`ArmRefines`).
3. *Frame locality.* `ArmRefines` does not say that the callee leaves the caller's frame `F` and
   the memory outside live CLIF allocations and its own stack unchanged, which `CalleeOk`
   (`FrameKeep`, `SameWorld`) needs.
4. *Slot placement.* `Clif.run` places a callee's slots with its bump allocator
   (`enterFunc`), the Arm code `sp`-relatively; the per-function theorem puts the entered
   function's slots at the Arm frame (`ClifEntry`, `SlotRel`). A program callee whose slot
   addresses escape (returned, compared) has different CLIF and Arm results, so its `linkEnv`
   contract is unsatisfiable; for the others it is satisfiable.
5. *`try_call` payload registers* — **fixed** (agent/trycall-contract, "`try_call` payload
   registers"): the payload defs are dead on the normal return and `CalleeTryOk` constrains only
   the results (`E2E.calleeTryOk_witness`).

The remaining plan is in `docs/DEFERRED.md` ("Linking").

### Linking at the Arm level (2026-10-02, `agent/arm-link`)

The program callees' contracts of `backend_correct_linked` are discharged from their own
per-function theorems, by induction on the call depth (`FV/E2E/LinkArm.lean`):

```lean
theorem backend_correct_program (L : LinkSys) (hL : L.Ok) (hf : f ∈ L.P.funcs) (M : Nat)
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) intBase size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)  -- agent/link-widen: stack-passed parameters
    (hrel : Rel.holds ⟨L.F, L.syms, slotBase, intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))  -- agent/link-widen: slot placement
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :  -- Widening 15: `P.bare`
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs)
```

(`backend_correct_program_returned`: returning runs, without `htr`.) The machine `L.mach M f`
runs `f`'s code with the linked hooks of depth `M` (`LinkSys.hooks`): a `bl g` of a function of
`P`, and a `blr` whose target register (as the machine decodes the instruction word at the pc,
`blrTarget`) holds the link-time address of a function `g` of `P` (`symCallee`), enter `g`'s
image (`enterAt`) and run its code until its first return (`linkedCall`: at the return address,
with the caller's `sp`, without error); other calls and TLS keep the base hooks. Layers added
for it:

* **M6 with kept addresses** (`regLevelCorrect_world`): `RL.G`, `frameWG` (frame, dead stack and
  addresses `G` the activation keeps: its callers' frames, the code), `StRel.gkeep`, the callee
  contract `CalleeOkG` (required at states that keep `G`, for the allocated call that is the
  instruction at the pc: `CallAt`, so a `blr`'s contract knows its target register),
  `BodyEntryW` (body-entry world equal to the entry state only outside `F` and on the entry
  `Args` registers), the final world (unmasked fields, `G`, program) at a return, and the trace
  of the run before it (every state but the entry at an address after a call of the function's
  code has the body's `sp`: `PostCall`, `RL.Good`, `Realizes` with a trace invariant). The entry
  is `AbiCall` (`AbiEntry` without the return address outside the code: a linked call may return
  into the callee's own code). `regLevelCorrect_backend` is derived (`G := ⊥`).
* **Per-function theorem with the final world** (`backend_correct_world`, `FV/E2E/LinkWorld.lean`,
  memory relation `RelW`: `Rel.holds`, the body's `sp`, no error): one VCode outcome realised by
  every Arm activation entered with the same body-entry world — the non-interference that makes
  `X.call` a function of the arguments and the caller's world (gap "exact world").
* **CLIF with bounded callee runs** (`Clif.linkEnvN`, `Clif.runLoop_linkN`, `LinkClifN.lean`).
* **The induction** (`LinkSys.thm`): `X M g` (the external semantics of an activation of `g` at
  depth `M`) computes a program call from a canonical state (`canon`: arguments in the callee's
  parameter registers, the code image, return address `raStar`); `progCall` shows the linked
  machine's call from every compatible caller state realises the callee's one VCode outcome
  (`ActRet`: results, world, callers' frames kept — gap "frame locality"); `calleeOk`/`xCallsOk`/
  `xCallsIndOk` discharge `CalleeOkG` and `XCallsOk`/`XCallsIndOk` of the activation's
  environment `envOf M g c` (`linkEnvN` without the functions of `P` that `g` does not declare,
  and with the declared ones returning only from a memory whose slot-placement oracle has the
  activation's `sp` `c` when program callees have slots: the run of `P.bare` — the program
  without functions, every program callee including `g` itself atomic, Widening 15 — is the
  same, `step_envOf`, `runLoop_envOf` under the activation invariant `ActInv`) at depth `M`
  from depth `M - 1`.

**Scope** (`LinkSys.Ok`): no `return_call`; parameters in distinct argument registers
(width ≤ 64) or on the stack;
program callees (functions some function of `P` calls or declares) may have stack slots and an
outgoing-argument area: a callee without slots has no slot region (`calleeFrame`), the slots of
one with slots fit in its slot region (`slotFits`; both checked per function on the code), and
the outgoing area of a function holds the stack-passed arguments of the program functions it
declares (`outFits`); program call sites pass integer
register arguments in the callee's parameter registers and take results from x0.. (checked per
site; the result clause constrains only the defs the site has; for a `blr` site, for every
function it may enter (`BlrTo`: one it may call, `MayCall`, that it declares or that one of its
indirect calls admits, `IndTo`; at a call through the GOT only the GOT symbol's function) with as
many register parameters, `blrRegs`); declarations
equal definitions; the return address of a call is outside the code of the function it calls,
or after a call instruction of that function's code and not at its entry (`RaOk`: a callee
sharing one copy of code with its caller, as `cargo fv`'s alias of a recursive function), stated
per call site (`raCall`, `raBlr`; the return address of a call is never the caller's own entry,
so a pointer call of a function to itself returns after the call); the functions of `P` have
distinct addresses, names sharing an address of no function of `P` are one base extern, the base
externs keep the symbols (`indScope`), a function's indirect-call signatures and the
functions it may call (`MayCall`: declared, or any function of `P` with an address — itself
included, Widening 15) with
the parameter types of one of them (`IndSigMatch`) pass no `sret` and at most 8 register
parameters (`indSig`),
and, when no program callee has stack slots (`¬ NeedSlots`), with an outgoing-argument area in
`P` the functions with an address have no slots (`addrSlots`; with `NeedSlots` the base keeps the
runs' allocations, `baseKeepsAllocs`, and the premise is vacuous).
**Trusted / premises**: the
link layout (bases, the code image `Img`/`imgMem`, return addresses outside callees' code or
after their calls,
`raStar`, distinct symbol addresses), the base
environment's contracts (calls outside `P`, `XCallsOk` and `XCallsIndOk` of the base externs,
TLS, the results of `try_call`s of base externs `baseTry`; when a function of `P` has an
outgoing-argument area, the base externs create no allocation, `baseNoAlloc`; when a program
callee has an outgoing area or a slot region (`NeedNI`), the base externs' non-interference
`baseNI` and TLSDESC flags independent of the world outside `F`, `baseTlsNI`; when a program
callee has stack slots (`NeedSlots`), the base externs keep the slot-placement oracle and create
no allocation, `baseKeepsPlace`/`baseKeepsAllocs`), the stack
budget `D` per call level, and the entry state (with `StackArgsAvoid L.Img` for an entry
function with stack-passed parameters, and, when a program callee has stack slots, the entry
memory's slot-placement oracle at the body's `sp` with the program's compiled frames, `hpl`).
The machine is depth-indexed (`L.mach M f` for runs of at most `M + 1` steps).

*Why `hpl` does not weaken the claim.* CLIF leaves the addresses of stack slots unspecified
(`stack_addr` yields some address of a fresh, uninitialised allocation), so no CLIF program can
depend on where its slots are; the CLIF semantics models this freedom with the slot-placement
oracle `Clif.Mem.place` (`none`: the bump allocator; `some`: a callee's slots at its compiled
frame's addresses below the caller's `sp`). `hpl` picks, for the reference CLIF run, the
placement the compiled code uses — one legitimate CLIF behaviour among those the source allows —
so that a callee's slot accesses and the caller's view of its dead stack refer to the same
bytes. It is vacuous without program callees with slots (`NeedSlots`). `PlaceAt` pins the
slot-byte oracle `Place.init` (SEM1) to `none`: callee slots start uninitialised in every
existing statement.

**Widening** (agent/link-widen):

1. *`try_call` between program functions* (normal returns; unwinding trusted, as per function).
   `Ok.noTry` is gone; `callRegs` constrains only the first `sigRets` defs (a `try_call`'s
   exception payload registers follow them), `tryRets` (a `try_call` of `h ∈ P` takes at most
   `h`'s results: `ti.rets`, the compiler's count of them) and `baseTry` (`CalleeTryOk` of the
   base hooks at `try_call`s of externs outside `P`; vacuous without them) are added — all
   implied by the former `noTry`. The contract `ActEntry.tries`/`regLevelCorrect_world`'s `hCT`
   is now `CalleeTryOkG` (required at the states that keep `G` at a call pc, like `CalleeOkG`;
   implied by `CalleeTryOk`, `CalleeTryOk.g`), since a linked callee runs the code image the
   caller keeps. `LinkSys.calleeTryOk` discharges it from the plain call's contract
   (`calleeTryOkG_of_call`: the results of a `try_call`'s call are the first `ti.rets` of the
   plain call's).
2. *Callees with CLIF stack slots and callees with an outgoing-argument area* (stack arguments
   of called functions): **done** (agent/link-widen, stage 2). Linking them needs
   **non-interference**: a callee's slot region
   `[sp_body + size, sp_body + frameSize)` and its outgoing area are part of its world but lie in
   the caller's dead stack, whose content at the call is garbage; the linked `X` runs the callee
   from the canonical state built from the caller's VCode world, which agrees with the machine
   state only outside the caller's `F`. The two body-entry worlds of the callee (canonical,
   actual) differ there, so the callee's VCode outcome must not depend on bytes that are not
   initialised in CLIF (a returning CLIF run never reads them; the code writes the outgoing
   area before a call reads it). Layers:
   * **The memory rules' read footprint** (`MemRefinesR Rd`, `LowerInstOkR Rd`,
     `MemRuleOkR`, `MemRulesCorrectR`, `memRulesCorrectR_program`): under a VCode semantics
     whose reads (loads, `ldar`, the LL/SC loops) are only required where every byte read
     satisfies `Rd`, every memory root rule is correct when the initialised bytes of the CLIF
     memory satisfy `Rd` (`InitIn Rd cm`): a memory rule's VCode reads only bytes its CLIF
     instruction reads. `memRulesCorrect_program` is derived from it (`Rd` true).
   * **The driver generic in the world** (`DriverHyp`, `InstCalls`, `TermCalls`, `TryCalls`,
     `TryIndCalls`, `LowerInstOk`, `LowerTermOk`, `LowerTryOk`, `VRetFrom`, `VTrapFrom`,
     `RunOk`, `sim_run` over `ISem CV W`/`MemRelTW W`; `DriverSemG`, the world-independent part
     of `DriverSem`): the simulation runs on any world type, so it can run on **pairs of
     worlds** (the two activations of a callee). `driver_correct` (Arm worlds, with the entry)
     takes `DriverSem` separately; its statement is otherwise unchanged.
   * **The lockstep of `csem`** (`FV/E2E/Lockstep.lean`, `csem_lockstep`): one instruction on two
     worlds that agree outside `Z ⊇ F` (`SameWorld Z`), whose reads avoid `Z` (`LockGuard`),
     with callees and the TLSDESC resolver that keep the agreement: the same outputs and control,
     worlds that agree outside `Z` minus the bytes written (`WriteSet`). The straight forms
     without memory access go through M6's `formOk_sound` (`OperandsSound Z`) at the canonical
     registers, which pass the checker's static checks (`canon_facts`, decided per form); the
     memory forms through their `MemRefines` characterisations; `ispec`/`mspec` and the control
     forms read the world only through the flags, `sp` and `x29`. The LL/SC loops on two runs:
     `rmw_lockstep2`, `cas_lockstep2`.
   * **Constant scratch defs in `csem`** (`RegallocCSem`): the defs M6 havocs no longer read the
     world's registers — `loopSem`'s defs past the first (the LL/SC scratch registers; `xchg`
     does not write x28) and a `try_call`'s defs past the callee's results (the payload
     registers) are 0. M6 never compares them (`MInst.keptDefs`, `havocFrom`); `MemRefines`
     leaves them unspecified.
   * **The call contracts with pinned calls** (`FV/Backend/Proof/IselContractP.lean`):
     `CallsRefineP Pc`/`IndCallsRefineP Pc` (the call clauses also assume
     `Pc name sig vals cm`, the call's extern, signature, argument values and CLIF memory),
     `LowerInstOkP Rd Pc`/`LowerTryOkP Rd Pc` (their runs assume `InitIn Rd cm` and
     `CallPin Pc env inst fr cm`: the instruction's returning CLIF call satisfies `Pc`), and the
     call, `call_indirect`, `try_call` and `try_call_indirect` rules under `MemRefinesR Rd` and
     the pinned contracts (`callRulesCorrectP`, `indRulesCorrectP`, `tryRulesCorrectP`,
     `tryIndRulesCorrectP`; the former statements are derived, `…_of_P`);
     `lowerInstOkP_runTerm`/`tryOkP_runTerm`/`tryIndOkP_runTerm` for every rule family.
   * **The guarded semantics** (`FV/E2E/Guarded.lean`, `csemG F ctx X Rd syms exts sigs sp0 Pc`: `csem` where
     the memory accesses have the memory rules' forms and every byte read satisfies `Rd`
     (`GuardR`), every call is pinned (`GuardC`, `CallG`: `Pc` admits it, the world is related
     to its CLIF memory with stack pointer `sp0`, its arguments are where the ABI puts them),
     `Args` excluded): it
     satisfies `Refines`, `MemRefinesR Rd`, `CallsRefineP Pc`, `IndCallsRefineP Pc`, and two
     runs of it on worlds that agree outside `Z ⊇ F` (`Rd := ¬ Z`) go in lockstep
     (`csemG_lockstep2`) when the callees of two pinned calls keep the agreement.
   * **The VCode non-interference** (`FV/E2E/Pair.lean`, `FV/E2E/PairDriver.lean`): the
     world-generic driver at `W = ArmState × ArmState` with `pairSem (csem …)` (the same
     instruction on both worlds, the same outputs) and `MRP` (`RelW` on both, agreement outside
     `Zof F D cm`: `F` and the bytes of `D` the current CLIF memory has not initialised; the
     initialised ones agree through `MemRel`). Its contracts (`instCalls_pair`,
     `termCalls_pair`, `tryCalls_pair`, `tryIndCalls_pair`, `driverSemG_pair`) come per CLIF
     step from the rule contracts on each world at `csemG (¬ Zof F D cm) (StepPin …)` (the
     step's CLIF call), paired by `seqRun_pair`; the entry by `entry_step2` (`LowerSim`: the
     entry code on two worlds with the same argument registers and stack-argument bytes gives
     one vreg file). `vcode_ni`: two body-entry worlds related to the same CLIF entry that
     agree outside `F ∪ D` return through the same `rets` with the same values, final worlds
     agreeing outside `F ∪ D`. Premises on the external semantics: `XNI` (two pinned calls on
     worlds agreeing outside `Z ⊇ F`, related to the same CLIF memory, with the same argument
     bytes, return the same values and worlds agreeing outside `Z`) and `XTls` (the TLSDESC
     flags do not depend on the world outside `F`). `backend_correct_world_ni` composes it with
     M6 (and the determinism of the VCode run, `vRetFrom_det`): the outcome of `w₀` is realised,
     up to `F ∪ D`, by every activation entered with a related body-entry world.
  Findings (why the earlier routes cannot work): the footprint cannot come from the memory
  relation alone, since `MemRelOk.store` must hold for every valid store, so no `MR` can say
  "the slot bytes are uninitialised" (a store into them must keep `MR`); and the VCode
  semantics cannot see the CLIF memory (its world is an `Arm.ArmState`, and every field the
  contracts leave free — masked registers, memory in `F` — is one `MR` must not depend on,
  `MRStable`). The footprint therefore has to come from the memory rules' proofs (the guard
  `Rd`, discharged at each read from the CLIF read's bytes), instantiated **per CLIF step**
  with `Rd := ¬ Zof F D cm`. A call's stack-passed arguments are in bytes of `D` (the
  outgoing area): the two runs agree on them only because each run's call is the step's CLIF
  call with its argument values, so the call contracts carry the pin `Pc` (a lockstep that
  tracks the written bytes cannot see that the call rule's stores wrote them). M6 does not
  change: two VCode runs with the same outcome are realised by the two activations through the
  existing per-function theorem.
  **The linking** (the steps of stage 2, in order):
   1. *Calls* (70d75f7): `LinkSys.Thm` with an activation's own `F` (a callee's `F` is its
      caller's minus its outgoing area and its slot region) and the non-interference clause
      (`NeedNI`-gated); `XNI` for the linked `X` (program callees from the induction,
      `progX_ni`/`xni`; base externs the `LinkSys.Ok` premise `baseNI`, needed only when a
      program callee has an outgoing area or a slot region); `progCall` equates the canonical
      and the actual call of such a callee through the clause. `XNI`/`CallG` carry the
      activation's `sp` (`spv w = sp0`), which turns the oracle guard below into the callee's
      placement.
   2. *Placement* (77f96df, trusted-semantics change, differential gates unchanged): the
      slot-placement oracle `Clif.Mem.place` (`enterFunc`/`Clif.enterSlots` push the
      activation's `sp` and place a covered callee's slots at its compiled frame's addresses
      below its caller's `sp`, `Mem.allocAt`; returns pop it, `Mem.leave`; `none` keeps the
      bump allocator).
   3. *Slotted callees* (`FV/E2E/LinkPlace.lean`, `LinkArm.lean`): a callee's whole-program run
      gives back the oracle and creates no allocation outside its arguments' and its slots'
      (`runLoop_place`, `runLoop_allocs`, `linkEnvN_keepsPlace0`), so the caller's relation holds
      after the call; `initState_mem` places the callee's slots in its slot region (`slotFits`),
      so its entry memory is related to its body-entry world with its own `F`. The activation's
      environment `envOf M g c` returns from a declared function of `P` only from a memory whose
      oracle has `c` (the activation's `sp`, `PlaceAt`); `xCallsOk`/`xCallsIndOk`/`xni` take the
      callee's placement from that guard. The guard does not change the run of `P.only g`: from
      its entry the run stays in `g`'s own frame (`step_callers`: `InSubset.externCalls`/
      `tryExterns`, no address for `g`) and keeps the oracle (`actInv_step`), so `ActInv` holds
      at every step and `step_envOf` applies. `LinkSys.Ok`'s `calleeSlots` is replaced by
      `calleeFrame` (a callee without slots has no slot region) and `slotFits`, plus
      `baseKeepsPlace`/`baseKeepsAllocs` (needed only with `NeedSlots`); `backend_correct_program`
      gains `hpl` (the entry memory's oracle at the body's `sp`; vacuous without `NeedSlots`).
      All new premises are vacuous or implied under the former scope. The witness has a called
      function with a stack slot (`t`) and one passing a stack argument (`u`).
3. *`sret` and stack-passed arguments between program functions*. `noSret`, `regParams` and
   `noOut` are gone. `sret`: the per-function theorem now exports the VCode return it took
   (`backend_correct_world`: `vc.RetsSite us`), and `sretRets` (the returns of an `sret`
   function carry its ABI results, checked on the code; vacuous without `sret`) gives the
   struct-pointer result x0 of the callee's one outcome; the CLIF call has no result
   (`returns_le_sigRets`). Stack-passed arguments: `Cond` carries `StackArgsAvoid L.F` (the
   arguments in the caller's outgoing area, part of every world, so the canonical and the actual
   caller state agree on them); `xCallsOk` derives it from the caller's `OutRel` and `outFits`;
   the callee reads them at `fp + 16 + off` of its body-entry world. After a call the caller's
   `OutRel` holds again because the callee's whole-program run creates no allocation outside its
   own slots (`runLoop_valid`: entered functions without slots, `baseNoAlloc`; with slots,
   `runLoop_allocs`). A program callee with an outgoing area of its own is covered by 2.
4. *Direct self-recursion, one copy* (agent/link-scope2): historical shared-code alias witness.
   `P` contains `r` (its self-call renamed to `r__fvself`) and `r__fvself`
   (`r`'s body and signature under the alias name, its self-call naming `r`), compiled to the
   same words and loaded at `r`'s address (`A r__fvself` and `A r` share `base` and `fb.words`;
   one copy in the image, as the linker resolves `r__fvself` to `r`). Each call returns into the
   callee's own code, so the linked call cannot find the return by "past it the machine stops"
   (`retStuck`). Instead:
   * M6 gives a trace (`regLevelCorrect_world`'s last clause, `PostTrace` in
     `backend_correct_world(_ni)` and `LinkSys.Thm`): every state of an activation's run before
     its return, but the entry, that is at an address after a call of its code (`PostCall`) has
     the body's `sp`, `frameDrop` below the entry `sp` (every realisation lemma gives `RL.Good`
     for the states of its run: a state after a non-call line is no post-call address,
     `RL.good_succ`; after a call the callee contract gives the body's `sp`).
   * `RetOf` also requires the caller's `sp`, and `linkedCall` takes the **first** return
     (`firstNat`). `linkedCall_eq`: with the return address outside the callee's code, an
     earlier return is impossible by `retStuck`; with it after a call of the callee's code and
     not at its entry (`RaOk`), an earlier return would be a post-call state with the entry `sp`,
     which the trace excludes (`frameDrop > 0`: `lowerRFunc` always builds a frame).
   * `raCall`/`raBlr` are weakened to `RaOk` (outside the callee's code, **or** `CallPc` of the
     callee's code with `pc + 4 ≠ base`); `CallerOk.ra`, `progCall`, `progOsCore` take `RaOk`;
     `MachEntry.abi`/`ActEntry.abi` are `AbiCall` (no return address outside the code).
   The witness checks it per call (`raOkB`, `raCallB_sound`) and states the shared base and words
   and that the calls of `r` and `r__fvself` return into each other's code (`oneCopyB`). For a
   crate, `r__fvself` resolves to `r` as a program call (not a base extern). This historical
   witness does not exercise native self-calls or recursion through a pointer; those are now
   admitted by the function-free activation model described above.
5. *Indirect calls between program functions* (`call_indirect`, `try_call_indirect`; and the
   `blr` of a call through the GOT). `Ok.noBlr` and `Linkable`'s indirect-call exclusion are
   gone (`Clif.LinkFree` excludes only `return_call`; `Clif.IndFree` is separate, still required
   by the per-function-contract theorem `backend_correct_linked`).
   * CLIF: `runLoop_linkN` admits indirect calls. The per-function program resolves a callee
     address through the declarations of `P.only f` (`Clif.callExternAt`), the whole program
     through all functions and declarations; they agree when `f` declares every name with an
     address but its own, the addresses are distinct and the base externs keep the symbols
     (`Clif.IndScope`; invariant: the memory's symbols are `syms`). A call reaching a function
     `h` of `P` is then atomic like a `call` (`atomic`: whole-program enter, per-function
     `linkEnvN` run of `h`).
   * M6: the callee contract was unsatisfiable for any hook that reads a `blr`'s target
     register: `CallSoundCtlG` quantified over every register assignment of the call at every
     call pc. It now holds for the allocated call whose instruction is at the pc
     (`OperandsSoundCtlAtI`, `Pc := CallAt fa base`; `callAt_of_q`, `realizes_op_core` passes the
     item's allocation) — a weaker premise of `regLevelCorrect_world`/`backend_correct_world`,
     implied by `CalleeOk` (`CalleeOk.g`); `backend_correct_final` is unchanged.
   * Arm: the linked hook of `blr` decodes the word at the pc with the Arm model's decoder
     (`blrTarget`; `blrTarget_of` from the encoder round trip `Insn.decode_encode`) and runs the
     function of `P` at that address (`symCallee`, `L.Xb.sym`). `X M g` is per activation: its
     `blr` branch is `progX` for a function `h` that `g` declares (other than `g`) with as many
     register parameters as the call has arguments, undefined for the other functions of `P`
     (so the contract at a `blr` reaching `g` itself, whose return the linked call could not
     find, is vacuous). The activation's CLIF environment is `envOf M g c` (the run of `P.only g`
     is unchanged, `runLoop_envOf`), so `XCallsIndOk` is needed only for declared callees
     (`xCallsIndOk`; register-passed arguments, no `sret`: `indSig`). `progOsReg` (and the
     `try_call` case of `calleeTryOk`) discharge the contract at `blr` sites, sharing
     `progOsCore` with `bl` sites. The indirect calls of `g` never reach `g` itself: `g` has no
     address (`indNoSym`, giving `TrapsExplicit`'s indirect clauses for callee runs).
   New premises (`blrRegs`, `blrTry`, `raBlr`, `indScope`, `indNoSym`, `indSig`, `addrSlots`,
   `baseXI`) are vacuous without indirect calls and `blr` sites, so implied by the former ones.
   Not covered: indirect calls of a function to itself (recursion through a pointer), indirect
   callees with stack-passed or `sret` parameters. Callers that do not declare the functions
   they reach through pointers: covered by 7.

6. *`i128` pairs between program functions*. The backend compiles a file with `i128` functions
   as its legalisation (`Opt.Legalize128.parsedFile128`: an `i128` parameter or result becomes
   an `i64` pair, AAPCS64-aligned with a pad where needed); `backend_correct_program` applies to
   that legalised program `P'` unchanged (`argRegs`' width ≤ 64 holds), so an `i128` passes
   between program functions as a register pair (x0–x7) and returns in x0/x1. Composition with
   the `i128` source: per function, `backend_correct_legal`/`_direct` relate the code of a
   legalised function to its source when its callees are externs (`hext`); for the witness's
   callee `a2` every function-level premise is discharged on the linked code itself
   (`E2E.LinkWitness.a2_legal`). Not covered: the whole-program run of the `i128` source
   program. That needs a program-level legalisation refinement: `Opt.Legal.check_refines` per
   function under a linked environment satisfying `ExtLegal` (a callee called with the split
   arguments returns the split results — the callees' source and legalised whole-program runs
   related), by induction on the call depth as `LinkSys.thm`, with `NoMemTrap` of the callee
   runs and `EnvKeepsAllocs` of the linked environment.

7. *Undeclared indirect callees (vtables)* (agent/link-scope). `cg_clif` declares only the
   functions a function references; a trait-object call loads the method from a vtable (a data
   object of another function) and calls it without declaring it. Changes:
   * Semantics (trusted-semantics growth, default unchanged): `Clif.Env.names` (further code
     symbols an indirect call may reach, `[]` by default); `Clif.callExternAt` searches
     `env.names ++ p.externNames`. With `names = []` every run is the former one (differential
     gates unchanged by construction).
   * CLIF linking: `Clif.linkEnvN P base M` has `names := P.names ++ base.names`, so the
     per-function program resolves an address to any function of `P` (or extern of `P`/`base`)
     whatever `f` declares; `Clif.IndScope P base syms` is the symbol keeping of `base` and the
     injectivity of the addresses of `P.names ++ base.names` (`IndDecl` is gone; weakened by
     Widening 10).
   * Arm: `LinkSys.MayCall g n` (`DeclN g n`, or `g` has indirect calls, `n ≠ g.name` and `n` has
     a link-time address) replaces `DeclN` in `X`'s `blr` branch, `envOf` (its `names` are
     `linkEnvN`'s), `blrRegs`, `blrTry`, `raBlr`, `indSig`; `Callee` gains the functions of `P`
     a function may call; `ActInv` carries the memory's symbols (for functions with indirect
     calls), from which `step_envOf` shows an indirect call reaches only `MayCall` functions.
   * Every new premise is implied by the former `Ok` (the former `indScope` made every function
     with an address a declared one, so `MayCall = DeclN` there, and `base.names = []`).
   * Real-crate finding (CrateCheck, survey `a_arith`): `blrRegs` required the results of every
     declared function of the `blr`'s arity in the site's defs, failing for a GOT call of a base
     extern without results (`panic_const_*`) next to a declared program function with one.
     `callRegs`/`blrRegs` now constrain only the defs the site has
     (`take (sigRets) (defs) = range (min (sigRets) (defs.length))`); weaker than before. The
     argument registers (`Lu`) and `blrTry` at GOT sites: Widening 8.
   * Witness: `d(vt, x)` loads `m`'s address from the vtable `vt` (`vtObj`: 8 zero bytes and a
     relocation to `m`, written into the entry memory by `Clif.Image.writeItems`; read-only
     allocation at `0xF8000`) and calls it by `call_indirect`, declaring nothing; `f` passes
     `symbol_value vt` to `d` (`f 41 = 802`). `backend_correct_program_witness` states
     `¬ DeclN fD fM.name`, `fD.externs = []`, the `blr` site, `m`'s address and the vtable bytes.

8. *Calls through the GOT pinned to their symbol* (agent/link-scope2). `blrRegs` (argument
   registers, results) and `blrTry` quantified over every function of `P` a `blr` site's caller
   may call with the site's arity, because M6's callee contract holds at every value of the
   target register. That rejected real crates: a GOT call of a base extern (`panic_const_*`,
   `try_call`s of std functions) next to a declared program function of the same register arity
   with other argument registers (an `sret` pointer in x8) or fewer results. The site's target is
   known statically: the lowering emits `loadExtNameGot t n; call (reg t)`.
   * VCode analysis (`FV/E2E/GotFlow.lean`): `GotV vc t n` (every def of `t` is
     `loadExtNameGot t n`, every call through `t` follows one in its block), decided by `gotB`
     (`gotB_sound`; `gotOf vc t` finds the symbol, `gotOf_sound`). Every returning or trapping
     VCode run of `csem` is one of `csemV (GotV vc)` (`vReturns_gotV`, `vTraps_gotV`: the
     invariant `GotInv`, a vreg set by a GOT load earlier in the block holds the symbol's address).
   * M6 (`RegLevelSim`): `csemV gv` is `csem` whose `call`/`try_call` through a vreg `t` with
     `gv t n` is defined only when the target value is `n`'s address (`gotGuard`). `RL.sem` is
     `csemV R.gv`; `CalleeOkG`/`CalleeTryOkG` and `regLevelCorrect_world` take `gv` (the contract
     is required only at the calls the VCode run reaches: weaker). `regLevelCorrect_backend` and
     `backend_correct_final` are unchanged (`gv := ⊥`, `csemV_bot`, `CalleeOk.g`).
     `ActEntry`/`backend_correct_world(_ni)` use `gv := GotV vcp`.
   * Arm: `LinkSys.BlrTo g t h` (`MayCall g h.name` and `h.name = n` for every `GotV vcp t n`)
     replaces `MayCall` in `Ok.blrRegs`/`Ok.blrTry` (weaker: one more hypothesis). `progOsReg`
     and `calleeTryOk` get the target value from the guard (`got_target`, by `symInj`).
     `LinkSys.Ok` changes only there; a checker following the former form adapts with `hb.1`
     (`BlrTo → MayCall`) or checks GOT sites against `gotOf` only.
   * Witness: `e` calls the base extern `pz(i64, i64)` through the GOT (x0, x1) and declares the
     program function `s(i64 sret, i64)` (x8, x0; one ABI result); the former `blrRegs` failed
     on it (`backend_correct_program_witness`: `GotV (A fE).vcp t "pz"`, `Lu.map (·.2) ≠ regLocs
     fS.sig`).
9. *Indirect callees restricted by the call-site signature* (agent/link-scope2). `indSig`
   required every function a function with indirect calls may reach (`MayCall`: every other
   function with an address) to take register arguments and no `sret`, so one vtable method with
   an `sret` or stack-passed parameter failed every indirect caller (13 fv-demo functions,
   CrateCheck). CLIF's `call_indirect` checks the arguments against the call site's `sigN`
   (`Clif.callExternAt`'s `checkTys`), and the callee's entry checks them against its own
   parameters (`initState`), so a run reaching `h` from an indirect call with signature `sig` has
   `AbiParam.tys h.sig.params = AbiParam.tys sig.params` (`LinkSys.IndSigMatch sig h`).
   * Contracts: `IndCallsRefine`/`IndCallsRefineP` (M4) and `XCallsIndOk` (M6) also assume
     `vals.map (·.ty) = AbiParam.tys sig.params` (the M4 rules have it from
     `instOutcome_callIndirect_ok`); `CallPin`'s indirect clause and `CallLg`'s indirect case carry
     it (`StepPin`). The contracts are premises of `backend_correct_final` (`hXI`) and of
     `LinkSys.Ok` (`baseXI`, `baseNI`): one more hypothesis each, so weaker.
   * `Ok.indSig`'s second clause holds only for the `h` with `∃ sig ∈ indSigs g, IndSigMatch sig h`
     (weaker); `xCallsIndOk` and `xni` derive the match from the callee's `ClifEntry.sig` and the
     new hypothesis (or, at a declared callee, from `declSig`).
   * Witness: `k` (9 parameters, the 9th on the stack) gets an address (`symsW`), so the indirect
     caller `v` may reach it (`MayCall fV fK.name`); no indirect call of `v` has `k`'s parameter
     types, and `k` needs more than 8 argument registers (the former `indSig` failed;
     `sigChainB_true`).
   Not covered: a reachable callee (matching types) with an `sret` parameter or stack-passed
   arguments; `blrRegs`/`blrTry` at a genuine indirect call still quantify over every function of
   the site's register arity the caller may reach (Widening 10).
10. *`blr` callees restricted by signature; aliases* (agent/crate-check3). Two blockers of
   `fv-demo` once its checker followed Widening 9:
   * `blrRegs`/`blrTry` quantified over every function the caller may reach (`MayCall`) with the
     site's register arity. A run entering a function `h` of `P` from an indirect call with
     signature `sig` has `IndSigMatch sig h` and returns as many results as `sig` has
     (`Clif.callExternAt` checks the results' types against `sig`, `h`'s run returns values of its
     own result types). `LinkSys.IndTo g h` (`MayCall g h.name`, and `DeclN g h.name` or
     `∃ sig ∈ indSigs g, IndSigMatch sig h ∧ h.sig.returns.length = sig.returns.length`)
     replaces `MayCall` in `BlrTo` (so in `Ok.blrRegs`/`Ok.blrTry`: one more hypothesis, weaker)
     and in `X`'s `blr` branch (`X` is undefined for the other functions: the contract at a `blr`
     entering them is vacuous). `xCallsIndOk` gets the match from the callee's entry and the
     returned values (`hretlen`), `xCallsOk` (a declared callee through the GOT) from `DeclN`.
     `indSig` keeps its hypothesis (`xni` has no result count).
   * `Clif.IndScope` required distinct addresses for all names of `P` and of the base
     environment, but a linker folds identical functions: `core`'s `<u64 as Display>::fmt` and
     `<usize as Display>::fmt` share one address in `fv-demo` (both declared by `fv-demo`
     functions, `func_addr` for `fmt::Argument`). `IndScope.inj` is now about the functions of `P`
     only, and `IndScope.alias`: names of `P` and of `base` sharing an address of no function of
     `P` are the same extern of `base` (true of one copy of code). `runLoop_linkN`'s per-function
     program resolves such an address to another alias than the whole program
     (`callExternAt_alias`: the same result up to the stuck messages, which name the extern; a
     stuck whole-program step contradicts the run's hypothesis); an address of a function of `P`
     resolves to the first function of `P` with it in both (`linkEnvN`'s names start with `P`'s
     functions). Weaker: the former `IndScope` implies the new one. `LinkCheck` derives
     `IndScope.inj` from `symInj`/`symOk` (the global `SymInj` check is gone) and `alias` is a
     base premise (`BaseOk.aliasSyms`, satisfied by `closedBase`).
   * Witness: `y(p, x, z)` calls the pointer `p` (`call_indirect`, signature `(i64, i32) -> i32`,
     arguments in x0/x1); `s(i64 sret, i64)` (x8, x0) gets an address, so `y` may reach it; no
     indirect call of `y` has `s`'s parameter types, so `¬ IndTo fY fS` and the former
     `blrRegs` failed (`blrChainB_true`; `y` is not called by `f`, so `f 41 = 802` is unchanged).
   Not covered: an indirect call whose signature equals the CLIF types of a reachable function
   with an `sret` parameter (CLIF's `call_indirect` checked types, not purposes: `(i64, i64)`
   admitted `(i64 sret, i64)`): Widening 11.
11. *Indirect callees restricted by the parameter purposes* (2026-10-04, agent/sret-purpose).
   Blocker: `fv-demo`'s two `catch_unwind` shims call `func_addr fn1` with the signature
   `(i64, i64)` in their landing pads, and two address-taken vtable methods have the signature
   `(i64 sret, i64)`: same types, so `IndSigMatch` admitted them and `indSig` (an `sret`
   parameter) and `blrRegs` (x8/x0 against the site's x0/x1) failed.
   * Semantics (trusted, a restriction): `Clif.stepCallIndirect` enters a function of the program
     only when `Clif.Signature.abiMatch declared target.sig` (same parameter types **and
     purposes**, same return types; it compared types only), else it is stuck. Cranelift requires
     "the called function must match the specified signature" (`call_indirect`); a purpose
     mismatch is another calling convention (the `sret` pointer in x8, not x0), so the runs
     removed are calls violating that precondition. `docs/contracts/clif-subset.md`, 2026-10-04.
     `Clif.callExternAt` (an extern at the address) is unchanged: an extern's semantics is
     untyped, so there is no callee signature to compare.
   * CLIF linking: `runLoop_linkN` takes the per-function environment `E` as a parameter: any
     environment with `linkEnvN`'s names, its externs outside `P`, and its extern for every
     function `h ≠ f` of `P` that `f` declares or that one of `f`'s indirect calls can enter
     (`syms h.name ≠ none` and `∃ d, IndSig f d ∧ d.abiMatch h.sig`, `IndSig f d`: `d` is the
     call-site signature of an indirect call of `f`). The whole-program run enters no other
     function of `P`: at such an indirect call `stepCallIndirect` is stuck, which contradicts the
     run's hypothesis. The linked machine uses `LinkSys.envR M g` (`linkEnvN` without the
     functions of `P` that `g` may not reach, `MayCall`); `envOf` is `envR` with the
     slot-placement guard (`step_envOf` is now an equality with `envR`, unconditional), and a step
     under `envR` that is not stuck is `linkEnvN`'s (`EnvRestricts`, `step_of_restrict`), which
     transfers `ActInv` and `TrapsExplicit` (`step_envOf_link`). `Thm` is about the run under
     `envR`; `backend_correct_program`'s statement is unchanged (its `TrapsExplicit` premise is
     still about `linkEnvN`).
   * `LinkSys.IndSigMatch sig h := sig.abiMatch h.sig` (purposes and return types too; the former
     type-only relation is `IndTyMatch`). `MayCall g n` for a function of `P` that `g` does not
     declare now also needs `∃ sig ∈ indSigs g, IndSigMatch sig h`: weaker wherever `MayCall` is
     a hypothesis (`raBlr`, `indSig`, `Callee`, so `NeedNI`/`NeedSlots`/`slotFits`/`calleeFrame`,
     and `IndTo`, so `blrRegs`/`blrTry`). `Ok.indSig`'s hypothesis is `(∃ sig ∈ indSigs g,
     IndSigMatch sig h) ∨ (DeclN g h.name ∧ ∃ sig ∈ indSigs g, IndTyMatch sig h)` (weaker: the
     former `∃ sig, IndTyMatch sig h` follows from it): a declared function stays in `envOf` for
     its direct calls, and the per-function run may enter it through a pointer with any
     signature of its parameter types (`callExternAt` sees no purposes). `xCallsIndOk`/`xni` get
     the disjunction from `MayCall` (`indReach`), and `IndTo` from `MayCall` alone (`indTo_of`).
     `LinkSys.Ok` changes only by weakening.
   * Checker: `LinkCheck.indSigB` (the disjunction above) in `indB`; `mayB` is unchanged (an
     over-approximation of `MayCall`); `indToB` follows `IndSigMatch`. `fv-demo`: 551 of 551.
   * Witness: `z(p, x, y)` calls `p` with the signature `(i64, i64)` (arguments in x0/x1); `s`
     (`(i64 sret, i64)`, x8/x0) has an address and the same parameter types and number of results
     (`IndTyMatch`), but not the purposes, so `¬ MayCall fZ fS.name` and `¬ IndTo fZ fS`
     (`zChainB_true`); with the type-only relation, `indSig` (`s`'s `sret`) and `blrRegs` (this
     `blr` site) failed on it. `v` no longer reaches `k` and `y` no longer reaches `s`
     (`¬ MayCall`): no indirect call of theirs matches.
12. *`sret` at indirect calls* (2026-10-07, agent/scope-widen, #89 (a)). `Ok.indSig` required
   every indirect-call signature of `g` and every function of `P` one of them can enter to have
   no `sret` parameter; `xCallsIndOk` used it only for the result count (`sigRets_of_noSret` on
   both sides) — the arguments are in registers either way (`argsAt_iff_of_regs` with at most 8
   parameters places an `sret` pointer in x8, `abiArgIdx`). Now `indSig` asks of such a callee
   `h` its register parameters (`sigParamBytes`, at most 8) and, for every indirect-call
   signature `sig` of `g` with `h`'s parameter types (`IndTyMatch`) and as many declared
   returns, `(sigRets h.sig).length = (sigRets sig).length` (both or neither pass an `sret`
   pointer). The returns are equal in number at a call that returns (`runLoop_returned_tys`, as
   before), so `xCallsIndOk`'s result count follows; `xni` uses only the register parameters.
   `LinkSys.Ok` changes only by weakening (the former field implies the new one: the witness
   derives it, `sigRets_of_noSret`). Checker: `LinkCheck.indRetsB` in `indB` (no `sret`
   condition on the call-site signatures). Effect on `InScopeP` (`lean-link`'s per-cause
   diagnostic): `fv-demo`'s test executable 4 → 1 failing function (the 3 `sret` callers pass),
   the `examples/deps` executable 23 → 15: no function fails `indB`'s `sret` conditions any more
   (also not those with a declared callee matched by types but not purposes: their `sigRets`
   agree, or a call reaching them cannot return); left: `indNoSym` 8, `blrRegs` 4, `blrTry` 3.
13. *`try_call` result counts* (2026-10-07, agent/scope-widen, #89 (d)). `Ok.tryRets` (a
   `try_call` of `h ∈ P` takes at most `h`'s results) and `Ok.blrTry` (the same for every
   function a `blr` `try_call` may enter) are gone, with their checks (`LinkCheck.tryB`,
   `indSiteB`'s `isTry` clause). `csem` now defines the call of a `try_call` only where the
   callee returns at least `ti.rets` results (`Option.filter`), so the continuation reads the
   callee's results; the try clauses of `CallsRefine`/`IndCallsRefine` (and the `P` variants)
   take `ti.rets ≤ (sigRets sig).length`, which the lowering supplies (`tryInfoOf` sets `rets`
   to the call-site signature's ABI returns, `TryRegs.tryInfoOf_rets`), and a call that returns
   in the CLIF run gives `(sigRets sig).length` results. `calleeTry_at`/`calleeTryOkG_of_call`
   lose their result-count hypothesis. `LinkSys.Ok` changes only by weakening. Effect on
   `InScopeP`: `examples/deps` 15 → 12 (`indNoSym` 8, `blrRegs` 4), `fv-demo`'s test
   executable 1 → 1 (`indNoSym`).
14. *Declared callees at indirect calls* (2026-10-07, agent/scope-widen, #89 (c)). `LinkSys.IndTo
   g h` (the functions of `P` a `blr` of `g` may enter: `X`'s `blr` branch, `BlrTo`, so
   `Ok.blrRegs`) held for every declared `h` (`DeclN`): for the GOT call of a declared
   non-colocated function, and because the per-function run's `Clif.callExternAt` checked only
   the argument/result types, so an indirect call could enter a declared `h` of the same types
   but other purposes (deps: `fn0 = colocated %h(i64, i64, i64, i64)` next to a `call_indirect`
   of `(i64 sret, i64, i64, i64)`: x0..x3 against x8, x0..x2, so `blrRegs` failed). Now:
   * Semantics (trusted, default unchanged): `Clif.Env` gains `sigOf : String → Option
     Signature := fun _ => none`, the known signature of an extern; `Clif.callExternAt` is
     stuck unless `(env.sigOf name).all declared.abiMatch` (as `Clif.stepCallIndirect` for a
     function of the program; Cranelift's "the called function must match the specified
     signature"). `Clif.linkEnvN P base M` sets `sigOf n := (P.func? n).map (·.sig)`, so the
     per-function run checks exactly what the whole-program run checks for a function of `P`
     (`runLoop_linkN` takes `E.sigOf = (linkEnvN …).sigOf`; `callExternAt_alias`/`_eq`: a name
     outside `P` has no signature in `linkEnvN`, and the per-function call is the
     whole-program one unless that one is stuck). No environment the tools build sets `sigOf`.
     Checking the caller's colocated declarations instead (the first design) breaks
     `backend_correct_legal_env`: its validator relates no declaration of the legalised `g` to
     `f`'s, so a target run could get stuck where the source run does not.
   * Contracts (weaker): the `IndCallsRefine`/`IndCallsRefineP`/`XCallsIndOk` clauses assume
     `∀ s, env.sigOf n = some s → sig.abiMatch s = true` (from `callExternAt`'s success,
     `instOutcome_callIndirect_ok`); the GOT forms of `CallsRefine`/`CallsRefineP`
     (`dest = .reg r`) and of `XCallsOk`/`XCallsOkRegs` (`d = none`) assume
     `ext.colocated = false`. The lowering supplies it: `rule_lower_2518` (GOT call) runs only
     after `rule_lower_2508` (`bl`, near relocation) failed, and that one matches every call of
     a colocated extern (`match_2508_colocated`, `call_got_not_colocated`, from `CallRuleOk`'s
     earlier-rules hypothesis); the same for `try_call` (`rule_lower_2551` after
     `rule_lower_2542`: `try_got_not_colocated`).
   * Link layer: `GotDecl g n` (`g` declares `n` non-colocated); `IndTo g h := MayCall g h.name ∧
     ((DeclN g h.name ∧ GotDecl g h.name) ∨ ∃ sig ∈ indSigs g, IndSigMatch sig h ∧
     h.sig.returns.length = sig.returns.length)`. `xCallsOk`'s GOT case gets `GotDecl` from the
     contract's `colocated = false`; `xCallsIndOk` gets `IndSigMatch sig h` from `envOf`'s
     `sigOf` (`indTo_of` is gone). `Ok.baseXI` and `LinkCheck.BaseOk.baseXI` state the base's
     contract for `{ L.base with sigOf := fun _ => none }` — the former statement (the linked
     environment ignores `base.sigOf`). `LinkSys.Ok` changes only by weakening (`blrRegs`:
     `BlrTo` is narrower). `Ok.indSig` keeps its `DeclN`/`IndTyMatch` disjunct: `xni`'s pinned
     indirect call (`CallLg`) records only the parameter types.
   * Checker: `LinkCheck.indToB` asks `declB && gotDeclB` (`gotDeclB_of`); `indSiteB`
     (`callScopeB`), `lean-link`'s per-cause diagnostic and `link-check` follow.
   * Effect on `InScopeP`: `examples/deps` 12 → 8 (`indNoSym` 8; `blrRegs` 4 → 0),
     `fv-demo`'s test executable 1 → 1 (`indNoSym`).
15. *Indirect calls of a function to itself* (2026-10-07, agent/scope-widen, #89 (b)).
   `LinkSys.Ok.indNoSym` (a function with indirect calls has no link-time address) is gone, with
   `indB`'s `S g.name == none` and `indFactsR`'s second part. It discharged `TrapsExplicit`'s
   indirect-call clauses for the activation's run of `P.only g`, in which a pointer to `g` would
   enter `g` as a nested frame that no linked-call contract covers. Now:
   * CLIF: after its entry an activation runs in `P.bare` (`Clif.Program.bare`: `P` without
     functions; the frames' provenance stays `LInv (P.only g)`), so both call forms resolve every
     function of `P`, `g` itself included, through the linked environment (`linkEnvN`: the
     callee's whole-program run, atomic). `runLoop_linkN` concludes `runLoop E P.bare`; its
     self-entry branches are gone (the atomic helper covers `f`), it takes `InSubset (P.only f)`'s
     `externCalls`/`tryExterns` (no direct call of `f` itself), and `hEp` covers `f` for indirect
     entry. `step_next_linv` (an auto-param `p.funcs ⊆ P.funcs`), `step_symbols`,
     `step_next_cases`, `LinkSys`'s `step_restrict`/`step_of_restrict` take the stepping program
     apart from the frames' program; `Clif.step_bare_callers`: a step of `P.bare` keeps no caller.
     `callExternAt_eq` is about `P.bare` (`bareNames_iff`; `linkNames_sub`, `only_externNames`,
     `externs_sub` are gone). No CLIF semantics change: since Widening 14 `linkEnvN.sigOf` makes
     `callExternAt` check `abiMatch` against the program function at the address, exactly
     `stepCallIndirect`'s check.
   * Backend: `InSubset` drops `func` (`p.func? f.name = some f`, which no proof used;
     `InSubset.of_regArgs`/`of_indirectFree` lose `hfunc`); `InSubset.retarget` gives
     `InSubset P.bare g` from `Ok.subset`.
   * Arm: `MayCall g n` drops `n ≠ g.name` from its indirect disjunct, so `IndTo`, `X`'s `blr`
     branch, `envR`/`envOf` and `Callee` include `g` itself when `g` has an address and a
     matching indirect call (`X`'s `progX κ M F g` is the induction hypothesis at depth `M - 1`;
     `Budget` then needs `Callee g g`, which `budget_K` meets and `StackBound`'s `edgeB` already
     had). `xCallsOk`'s GOT case gets `IndTo` from either disjunct of `MayCall`. `Thm`/`ThmG` are
     about `runLoop (envR M g) P.bare`; `ActInv` drops its symbols conjunct (it fed only
     `step_callers`, replaced by `Clif.step_bare_callers`); `trapsExplicit_of_returned` is for
     `P.bare`, its indirect clauses vacuous (`reach_symbols` is gone). `LinkSys.Ok` loses
     `indNoSym`; the fields with a `MayCall`/`Callee` antecedent (`raBlr`, `indSig`, `blrRegs`
     through `IndTo`, `calleeFrame`, `slotFits`, `NeedNI`/`NeedSlots`) gain only instances
     `h = g` with `syms g.name ≠ none`, which `indNoSym` excluded: the former `Ok` implies the new
     one.
   * Statements: `backend_correct_program(_budget)`, `backend_correct_program_budgetX`,
     `backend_correct_program_stack(X)`, `LinkCheck.ProgStmt`, `ProgStmtS(X)`, the
     `binary_correct*` theorems and `Link.compileExe_correct` take `TrapsExplicit (linkEnvN P
     base M) P.bare cs` (the activation's run with every program callee atomic: no indirect
     clause left) for `… (P.only f) cs`. The former premise implies the new one, proven:
     `trapsExplicit_bare_of_only` (`FV/E2E/LinkArm.lean`; from `InSubset (P.only f) f`,
     `LinkFree f`, `LInv (P.only f) cs` and the names of `f`'s declarations among the
     environment's) — the two runs take the same steps (`step_bare_eq_only`) until a step entering
     `f`, which no call of `f` is (`InSubset`) and no reached indirect call is (the former
     premise's `indirect`/`tryIndirect` clauses); `LinkSys.trapsExplicit_bare_of_only` under
     `L.Ok` and `ClifEntry` alone (no `indNoSym` needed); `Link.compileExe_trapsExplicit_bare`
     from `compileExe_correct`'s own premises (`compileExe` succeeded, `BaseOk`, `f` in the
     program, `ClifEntry` from `ClifRun`). So each changed theorem implies its former statement.
   * Checker: `LinkCheck.mayB` drops `n != g.name`; `raBlr` for `h = g` follows from the layout
     and `raStarB` (`raOk_self`: a call's return address is within the function's words, which
     fit below an address outside them, so it is not the entry; `raCallB` is unchanged); `indB`
     drops `S g.name == none`; `link-check`'s diagnostic and `lean-link`'s per-cause list lose
     `indNoSym`. The non-vacuity witness follows (its own `raCallB` also checks the
     not-the-entry condition, `raCallB_parts`).
   * Effect on `InScopeP`: `examples/deps` 8 → 0, `fv-demo`'s test executable 1 → 0: `lean-link`
     writes both with `Link.compileExe` (`Link.compileExe_correct`).

**Non-vacuity** (`FV/E2E/NonVacuityLink.lean`, namespace `E2E.LinkWitness`): the closed program
`P = {f, g, h, s, k, r, r__fvself, q, v, a2, w, t, u, m, d, e, y, z}` (`m`, `d`: the vtable dispatch of
Widening 7; `e`: the GOT call of a base extern of Widening 8, not called by `f`; `y`: the indirect
caller of Widening 10, `z` that of Widening 11, neither called by `f`) — the entry `f` (a stack slot, a 16-byte
outgoing area)
passes an `sret` pointer to its slot to `s` (which stores through it and returns the pointer),
calls `k` with 9 arguments (the 9th on the stack), calls `g` by a `try_call` with a result
(`block1(ret0)`, handler `tag0: block2(exn0)`), calls the recursive `r` (`r 3 = 6`, through
its alias `r__fvself`), `v`, `w`, `t` and `u`; `g` calls `h` (a non-leaf program callee; `g` keeps its
argument in x19 across the call); `v` takes `q`'s address (`func_addr`), calls it by
`call_indirect` and calls `q` again through the GOT (a non-`colocated` declaration:
`adrp`/`ldr :got:`/`blr`); `w` passes two `i128` values to `a2 : (i128, i128) -> i128` and splits
its result (`a2` and `w` are the `Opt.Legalize128` outputs the validator accepts: pairs in x0–x3,
the result in x0/x1); `t` has a stack slot (it stores `n + 10` through `stack_addr` and loads it
back: `t n = 2 n + 10`; a 16-byte slot region, `size ≠ frameSize`), placed by the slot-placement
oracle at its compiled frame address; `u` has an outgoing-argument area (it calls `k` with 9
arguments, `n` on the stack: `u n = 1 + n`); `f` passes the address of the vtable `vt` to `d`,
which calls the method `m` it loads from it (`f 41 = 802`); `system_v` — parsed from an embedded source,
legalised and
compiled by the pipeline (`lowerFunction`, `prepare`, the `lean-regalloc` output for this file
embedded as JSON and rebuilt by `parseRAOut`/`buildRFunc`, `checkAlloc`, `lowerRFunc`,
`emitFunc`, `layout`), loaded at `0x70000` (`f`), `0x10000`…`0xF0000`, `0xF4000` (`e`), `0xF6000`
(`y`) and `0xF7000` (`z`),
closed base environment (no extern outside `P` is defined, no TLS), the CLIF image's symbols: `q`
and `m` at their bases and the vtable `vt` at `0xF8000` (`symsW`), depth `M0 = 100`. `t` and `u` make `NeedSlots` and `NeedNI` hold, so the
premises they gate are discharged rather than vacuous (`baseNI`: `Xb.call` is undefined;
`baseTlsNI`: the TLSDESC flags are the world's `pstate`, unmasked; `baseKeepsPlace`/
`baseKeepsAllocs`: no base extern; `calleeFrame`/`slotFits`: checked per function; `hpl`: `cs0`'s
oracle is `⟨[sp0 - 64], framesW⟩`, `framesW = (L F).frames`):

```lean
theorem L_ok (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) : (L F).Ok
theorem backend_correct_program_witness :
    (L F0).Ok ∧ fF ∈ (L F0).P.funcs ∧ fG ∈ (L F0).P.funcs ∧ fH ∈ (L F0).P.funcs ∧
    fQ ∈ (L F0).P.funcs ∧ fV ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fV) ∧
    ¬ Clif.IndFree fV ∧ (∃ info, (A fV).vcp.CallSite info ∧ ∀ n, info.dest ≠ .sym n) ∧
    DeclN fV fQ.name ∧ (L F0).syms fQ.name = some 0x80000 ∧
    (L F0).syms fK.name = some 0x40000 ∧ ¬ (L F0).MayCall fV fK.name ∧
    (∀ sig ∈ indSigs fV, ¬ LinkSys.IndTyMatch sig fK) ∧
    ¬ (∃ bytes, sigParamBytes fK.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
    fA2 ∈ (L F0).P.funcs ∧ fW ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fW) ∧
    (∃ info, (L F0).ProgSite fW info fA2) ∧
    Opt.Legalize128.function128Cert (srcFn 9) = .ok (fA2, certOf 9) ∧
    Opt.Legal.check (srcFn 9) fA2 (certOf 9) = true ∧
    Opt.Legalize128.function128Cert (srcFn 10) = .ok (fW, certOf 10) ∧
    Opt.Legal.check (srcFn 10) fW (certOf 10) = true ∧
    (srcFn 9).sig.params.map (·.ty) = [.i128, .i128] ∧ (srcFn 9).sig.returns.map (·.ty) = [.i128] ∧
    fA2.sig.params.map (·.ty) = [.i64, .i64, .i64, .i64] ∧
    fA2.sig.returns.map (·.ty) = [.i64, .i64] ∧
    fS ∈ (L F0).P.funcs ∧ fK ∈ (L F0).P.funcs ∧
    (∃ info ti, (A fF).vcp.TrySite info ti ∧ (L F0).ProgSite fF info fG) ∧
    (∃ info, (L F0).ProgSite fG info fH) ∧
    (∃ info, (L F0).ProgSite fF info fS) ∧ fS.sig.params.any (·.purpose == .sret) = true ∧
    (∃ info, (L F0).ProgSite fF info fK) ∧ (∃ off, ArgLoc.stack off ∈ locsOf fK.sig) ∧
    (RAFrame.compute (A fF).vcp (A fF).rf).intBase ≠ 0 ∧ fF.slots ≠ [] ∧
    fR ∈ (L F0).P.funcs ∧ fRS ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fR) ∧
    (∃ info, (L F0).ProgSite fR info fRS) ∧ (∃ info, (L F0).ProgSite fRS info fR) ∧
    fRS.name = fR.name ++ "__fvself" ∧ fRS.blocks = fR.blocks ∧ fRS.sig = fR.sig ∧
    (A fRS).base = (A fR).base ∧ (A fRS).fb.words = (A fR).fb.words ∧
    (∃ pc, CallPc (A fR).fa (A fR).base pc ∧
      ∃ k < (A fRS).fb.words.size, pc + 4 = (A fRS).base + BitVec.ofNat 64 (4 * k)) ∧
    (∃ pc, CallPc (A fRS).fa (A fRS).base pc ∧
      ∃ k < (A fR).fb.words.size, pc + 4 = (A fR).base + BitVec.ofNat 64 (4 * k)) ∧
    fT ∈ (L F0).P.funcs ∧ fU ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fT) ∧
    fT.slots ≠ [] ∧ (∃ info, (L F0).ProgSite fF info fU) ∧ (∃ info, (L F0).ProgSite fU info fK) ∧
    (RAFrame.compute (A fU).vcp (A fU).rf).intBase ≠ 0 ∧ (L F0).NeedSlots ∧ (L F0).NeedNI ∧
    (L F0).PlaceAt cs0.mem (spv w0) ∧
    fM ∈ (L F0).P.funcs ∧ fD ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fD) ∧
    ¬ Clif.IndFree fD ∧ fD.externs = [] ∧ ¬ DeclN fD fM.name ∧
    (∃ info, (A fD).vcp.CallSite info ∧ ∀ n, info.dest ≠ .sym n) ∧
    (L F0).syms fM.name = some 0xE0000 ∧ cs0.mem.symbols "vt" = some vtAddr ∧
    vtObj.items.drop 8 = [.addr "m" 0] ∧ (∃ m, vtWrite = .ok m ∧ cs0.mem.bytes = m.bytes) ∧
    fE ∈ (L F0).P.funcs ∧ Clif.IndFree fE ∧ DeclN fE fS.name ∧ (L F0).P.func? "pz" = none ∧
    (sigRets fS.sig).length = 1 ∧
    (∃ info t Lu Ld, (A fE).vcp.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      GotV (A fE).vcp t "pz" ∧ (regLocs fS.sig).length = Lu.length ∧ Lu.map (·.2) ≠ regLocs fS.sig) ∧
    fY ∈ (L F0).P.funcs ∧ ¬ Clif.IndFree fY ∧ (L F0).syms fS.name = some 0x30000 ∧
    ¬ (L F0).MayCall fY fS.name ∧ ¬ (L F0).IndTo fY fS ∧
    (∃ info t Lu Ld, (A fY).vcp.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      (regLocs fS.sig).length = Lu.length ∧ Lu.map (·.2) ≠ regLocs fS.sig) ∧
    fZ ∈ (L F0).P.funcs ∧ ¬ Clif.IndFree fZ ∧
    (∃ sig ∈ indSigs fZ, LinkSys.IndTyMatch sig fS ∧ sig.returns.length = fS.sig.returns.length) ∧
    ¬ (L F0).MayCall fZ fS.name ∧ ¬ (L F0).IndTo fZ fS ∧
    (∃ info t Lu Ld, (A fZ).vcp.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      (regLocs fS.sig).length = Lu.length ∧ Lu.map (·.2) ≠ regLocs fS.sig) ∧
    run0 = .returned [⟨.i64, 802#64⟩] (retMem run0) ∧
    ArmRefines (A fF).fb (A fF).base 8 ((L F0).mach M0 fF) s0 run0
```

Every per-function premise of `LinkSys.Ok` (`compiled`, `covered`, `outFits`,
`argRegs`, `sretRets`, `calleeFrame`, `slotFits`, `callRegs`, `blrRegs`, `raBlr`,
`indSig`, `indScope`'s declarations, `addrSlots`, `declSig`, `entryRegs`, `fits`,
`raCall`, `depth`, `subset`, `free`, the image `imgCode`) is an executable check with a
soundness lemma (`chks`/`Facts`, `siteOk_sound`, `blrOk_sound`,
`retsB_sound`, `outFitsB_sound`, `slotFitsB_sound`, `entryB_sound`, `raCallB_sound`,
`linkFreeB_sound`, `indFacts`, `imgCode_of`), decided by `native_decide` (`okB_true`); `symInj`,
`symOk` and the base contracts (`baseOs`, `basePc`, `baseExt`, `baseX`, `baseXI`, `baseTls`,
`baseTry`, `baseNoAlloc`, `baseNI`, `baseTlsNI` (`xbTls`), `baseKeepsPlace`, `baseKeepsAllocs`,
the base's symbol keeping) are proven (vacuous or immediate for the closed
environment). The second theorem discharges the entry premises too (`AbiEntry`, `StackAvail`,
`hF`, `hgfree`, `himg`, `BodyEntry`, `ArgsIn`, `ClifEntry` with `f`'s slot at its frame address
`sp0 - 32`, `StackArgsAvoid`, `Rel.holds` (the slot's allocation outside `F0`, `SlotRel`,
`OutRel` of the 16-byte outgoing area), `hpl`, the returning CLIF run (with the oracle: `t`'s
slot at its frame address), `native_decide`: `entryFactsB_true`, `callChainB_true`,
`slotChainB_true`, `vtChainB_true`, `gotChainB_true`, `oneCopyB_true`, `sigChainB_true`,
`blrChainB_true`, `zChainB_true`) for `f` on `41` at depth `M0 = 100` and applies
`backend_correct_program_returned`. Axioms: standard plus the `_native` axioms of `names`,
`okB_true`, `entryFactsB_true`, `callChainB_true`, `slotChainB_true`, `vtChainB_true`,
`gotChainB_true`, `oneCopyB_true`, `sigChainB_true`, `blrChainB_true`, `zChainB_true` (and the
backend proofs' fixed ones: before T6 `bv_decide`/`native_decide`, now none). The witness found the former `raCall`
(the return address of every call outside the code of **every** function of `P`, including the
caller's own) unsatisfiable for every program with a call; it is now stated for the callees of
the caller's call sites (`LinkSys.ProgSite`).

### Crate-level instance (2026-10-04, `agent/crate-check`; `agent/crate-check3`; `agent/sret-purpose`)

`backend_correct_program` for a real crate built by `cargo fv`: `LinkSys.Ok` is decided per
crate on the build's own data, by a general checker with a soundness proof
(`FV/E2E/LinkCheck.lean`, namespace `E2E.LinkCheck`), and the generated proof states the
theorem for the crate's functions (the package `crate-proofs/`, `Crates/*.lean`; how to run it:
`docs/USAGE.md`, "Proving a crate").

```lean
structure FnInput where clif : String; ra : String; k : Nat := 0; j : Nat := 0
structure LinkInput where
  funcs : List FnInput            -- the CLIF file lean-backend compiled, lean-regalloc's output
  addrs : List (String × Nat)     -- the link map: the machine's symbol addresses (`Xb.sym`)
  syms : List (String × Nat)      -- the CLIF image's symbols (`L.syms`)
  raStar : Nat
  D : Nat
  aliases : List (String × String) := []   -- historical shared-code aliases (f__fvself, f)
structure BaseEnv where           -- everything outside the program
  env : Clif.Env; call : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState)
  tp : BitVec 64; tlsFlags : String → Arm.ArmState → Arm.PState; hooks : ArmHooks
def LinkSys.ofInput (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys
def okB (I : LinkInput) : Bool
def globalB (I : LinkInput) : Bool                     -- the program's checks
def fnsB (I : LinkInput) (fs : List FnInput) : Bool    -- the per-function checks of a slice
theorem okB_of (hg : globalB I = true) (hf : fnsB I I.funcs = true) : okB I = true
theorem fnsB_append : fnsB I (l₁ ++ l₂) = (fnsB I l₁ && fnsB I l₂)
structure BaseOk (L : LinkSys) : Prop      -- the base environment's premises of `LinkSys.Ok`
theorem okB_sound (hI : okB I = true) (hB : BaseOk (LinkSys.ofInput I B F))
    (hF : ∀ a, (LinkSys.ofInput I B F).Img a → F a) : (LinkSys.ofInput I B F).Ok
def CrateStmt (I : LinkInput) (n : String) : Prop :=
  ∀ B F, BaseOk (LinkSys.ofInput I B F) → (∀ a, (LinkSys.ofInput I B F).Img a → F a) →
    ProgStmt (LinkSys.ofInput I B F) n   -- backend_correct_program for `n`, all premises but `Ok`
theorem crate_correct (hI : okB I = true) (n : String) : CrateStmt I n
theorem baseOk_closed (htls : ∀ g ∈ (progOf I.results).funcs, hasTls g = false) :
    BaseOk (LinkSys.ofInput I closedBase F)
```

**The linked system** (`LinkSys.ofInput`): `P` is the input's functions, parsed and
`i128`-legalised as `lean-backend` does (`FnInput.func`); `A g` is the pipeline run in Lean
on them (`pipe`: `lowerFunction`, `prepare`, `parseRAOut`/`buildRFunc` of the recorded
`lean-regalloc` output, `lowerRFunc`, `emitFunc`, `layout`; `I.results`, looked up by name,
`artOf`), loaded at the function's link-map address (an alias at its function's: `baseOf`), so
`Compiled` follows from the pipeline's result (`pipe_spec`) and is not assumed; `base`,
`Xb.call`, `Xb.tp`, `Xb.tlsFlags`, `Hb` are the base environment's; `Xb.sym n off` is `n`'s
link-map address plus `off` (`0` for a name outside the map); `L.syms` is `I.syms`; the code
image `Img` is the compiled words' addresses and `imgMem` their bytes (`memT`); `raStar`, `D`
from the input.

**Recursion, one copy.** A directly recursive `f` declares and calls `f` under its original
name. Its per-function activation runs in `P.bare`; the linked environment interprets the
self-call as another whole-program activation. `DeclN` and the call-site checks include self
declarations. The return may lie in the callee's own code (`RaOk`); no duplicate function or
fresh alias address is needed. Generic `LinkInput.aliases` remains for existing shared-code
certificates, including the historical `r`/`r__fvself` non-vacuity witness; the compiler and
certificate generator no longer synthesize such aliases.

**The checker** (`okB`, `okR`): per function (`chks = staticChks ++ linkChks`, each check named
by the premise it discharges): the pipeline succeeds, `lowerCheck`, `prepCheck`, `checkAlloc`
(`compiled`), `FormsCovered`, `sretRets`, `outFits`, `argRegs`,
`calleeFrame`/`slotFits`, `callRegs`/`blrRegs` (per call site: a `bl` of a function of `P`
passes its ABI registers; a `bl` of an extern outside `P` needs nothing; a `blr` site, `blrOk`,
for every function it may enter, `LinkSys.BlrTo`: one it declares or that one of its indirect
calls can enter, `indToB` for `IndTo`; at a call through the GOT, `gotOf`/`gotOf_sound` of
agent/link-scope2's `GotFlow`, only the GOT symbol's), `declSig`, `entryRegs`, `fits`,
`raCall`/`raBlr` (`raOkB`: the return address of every call is outside every other function's
code, an interval check, or after a call of that function's own code), `depth`, `free`, `subset`
(clif-subset-v2 E, ABI and indirect-call signatures, in the function-free activation),
`indScope`/`indSig` (`indSig` for the functions one of the caller's indirect calls
can enter, `indSigB`: a matching signature, `IndSigMatch`, or declared with the parameter types,
`IndTyMatch`); for the program (`globalChks`, `globalB`): distinct
names, the image reads back word by word (`imgB`, which also rejects overlapping or misaligned
code), `raStar`, `symInj` (every function's link-map address is nonzero and no other map
entry's), `symOk` (the CLIF image's symbols are at their link-map addresses; with `symInj` they
give `Clif.IndScope.inj`, distinct addresses of the functions of `P`), `addrSlots`. `okB_sound` builds every
field of `LinkSys.Ok` from them (`Facts`, `facts`, the soundness lemmas of the witness's checks,
generalised), except `imgF` (`hF`) and the base fields. `diag`/`diagR` is the diagnostic version
(the failing checks by function; `diagR_nil`: empty implies `okR`). Only standard axioms
(`#print axioms E2E.LinkCheck.okB_sound`, `okB_of`).

**What stays a premise** (`BaseOk`), exactly the fields of `LinkSys.Ok` about the base
environment, gated as there: `baseNoAlloc`, `keepSyms` (`Clif.IndScope.keep`), `aliasSyms`
(`Clif.IndScope.alias`: names sharing an address of no function of `P`, as `core`'s folded
`Display::fmt` of `u64` and `usize`, are one base extern), `baseOs`,
`basePc`, `baseExt`, `baseX`, `baseXI`, `baseTls`, `baseTry`, `baseNI`, `baseTlsNI`,
`baseKeepsPlace`, `baseKeepsAllocs`: the contracts of std (panics, the allocator, formatting),
of other crates' code and cg_clif fallbacks, of the runtime (`memcpy`, …), and of TLS. With `hF`
(the code is outside the world) and the entry premises of `backend_correct_program`, they are the
premises of the crate's theorem. They are satisfiable: `baseOk_closed`, for the closed base
environment `closedBase` (no extern outside the program has a semantics, calls outside it
continue at the next instruction), for every input without `tls_value`; the crate's theorem then
covers the runs that call nothing outside the program.

**Without the checker (L2a, `FV/E2E/LinkScope.lean`).** `okB`'s checks split into input
conditions, facts about the compiler's own output, and facts about the link (docs/TO-PROVE.md,
"L2a classification"). The executable parts are in `FV/E2E/LinkScopeDefs.lean` (in `fvcheck`):

```lean
def pipeT (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art
def LinkInput.resultsT (I : LinkInput) : Res          -- the compiler's pipeline (lowerAllocReady)
def LinkInput.withDepth (I : LinkInput) (R : Res) : LinkInput   -- D := the largest frameDrop
def fnScopeB (g : Clif.Function) : Bool               -- subset, ABI, dominatedB, lowerScopeB,
                                                       -- arityOkB, lowersB (extendsWidenB, spillSizeOkB)
def progScopeB (P : Clif.Program) (S : String → Option Nat) : Bool  -- names, declSig, indB,
                                                       -- callScopeB, outScopeB, addrSlotsInB
                                                       -- (outAreaB: lowerFunction's outgoing area)
def InScopeP (I : LinkInput) : Bool                    -- the input conditions
def linkerOkB (I : LinkInput) : Bool                   -- fits, imgB, raCallB, raStarB, symInjB, symOkB
theorem okT_of_inScope (hD : SpillDefinedHyp) (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) : okR (I.withDepth I.resultsT) I.resultsT = true
def LinkSys.ofInputT (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys :=
  ofRes (I.withDepth I.resultsT) I.resultsT B F
theorem okT_sound (hD) (hin) (hlk) (hB : BaseOk (LinkSys.ofInputT I B F))
    (hF : ∀ a, (LinkSys.ofInputT I B F).Img a → F a) : (LinkSys.ofInputT I B F).Ok
theorem crate_correct_inScope (hD : SpillDefinedHyp) (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) (n : String) : CrateStmtT I n
theorem baseOk_closedT (htls : ∀ g ∈ I.prog.funcs, hasTls g = false) :
    BaseOk (LinkSys.ofInputT I closedBase F)
```

`resultsT` is the compiler's pipeline (`lean-backend`'s: regalloc2's answer only if `checkAlloc`
accepts it and its code is `emitReady`, else the spill allocation), not the checker's `pipe`
(which lowers regalloc2's raw answer). `okR_sound` (`okB_sound` for any results `R` that are
pipeline outputs, `ResOk`) gives `LinkSys.Ok`. The own-output facts are proven: pipeline success
and the validators (`pipeT_ok`: `backend_correct_final_total_emit`, `lowerCheck_complete`,
`prepCheck_complete`, `formsCovered_complete`, `checkAlloc` of the spill allocation by
`spillCheckAlloc` (`FV/E2E/SpillCheckAlloc*.lean`, completeness of `checkAlloc`'s fixpoint
iteration)), `sretRets` (`retsB_of_lower` with the ISLE inversion `iselNoRets`,
`FV/E2E/LinkOwnRetsIsel.lean`), `entryRegs` (`entryB_of_lower`), `callRegs/blrRegs`
(`sites_of_lower`, `FV/E2E/LinkOwnCalls.lean`, from the call inversion
`CallShapeHyp`: `callShapeHyp_of` (`FV/E2E/LinkOwnCallsShape.lean`, the driver part) of
`CallRunHyp` — `callRunHyp_of` of `stmt_noCalls`/`term_noCalls` (`LinkOwnCallsRun.lean`),
`callStmtRunHyp` (`LinkOwnCallsStmt*.lean`), `tryRunHyp` (`LinkOwnCallsTry*.lean`) — and
`GotRunHyp` — `gotRunHyp_of` (`LinkOwnGotRun.lean`) of `segRangeHyp` (`LinkOwnSegRange.lean`)
and `gotLocalHyp` (`LinkOwnGotLocal.lean`)), `outFits` (`outFits_of_lower`),
`calleeFrame/slotFits` (`frame_of_lower`, `FV/E2E/LinkOwnFrames.lean`), `depth` (by
construction). The ISLE facts use leaf-wise kernel checks over the exported rules and
untrusted literal term sets, as the Kill and Cov tables do. Its one program-independent hypothesis, `SpillDefinedHyp` (definite
assignment of the prepared VCode: availability sets with nothing available on entry, from which
`checkAlloc`'s fixpoint, started from no vreg in its home, accepts the spill allocation), for
input whose entry block has the signature's parameters, is proven (`E2E.spillDefinedHyp`, below),
so `crate_correct_inScope_proven` has no open hypothesis.

**The input condition `entryParamsB`; definite assignment reduced to definedness** (2026-10-07,
`FV/E2E/SpillDefined*.lean`, `FV/Backend/Proof/SpillDefined*.lean`,
`FV/Backend/Proof/DefRuns.lean`, `FV/Backend/Proof/EntryParams.lean`). The first statement of
`SpillDefinedHyp` (without `entryParamsB`) was false, so the first `crate_correct_inScope` was
vacuous: `lowerFunction` defines the entry block's parameters from the signature's locations
(`entryParams` zips them), so an entry-block parameter beyond the signature's is never defined,
and nothing in `InSubset`, `Dominated`, `LowerScope`, `ArityOk` or `fnScopeB` excluded it
(Cranelift's verifier does). `function %f() -> i64 { block0(v0: i64): return v0 }` met all of
them and its `return` reads the undefined `v0` (`not_spillDefinedHyp`,
`FV/E2E/SpillDefinedFalse.lean`). `fnScopeB` (so `InScopeP`) now includes `Spill.entryParamsB`
(entry block parameters = signature parameters), and `SpillDefinedHyp` assumes it; `InScopeP`
with it still holds for `a_arith` and `fv-demo` (`InScopeWitness`), and `lean-e2e-check` counts it.

```lean
theorem E2E.not_spillDefinedHyp : ¬ ∀ p f vc vcp, InSubset p f → Spill.ArityOk f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc → prepare vc = .ok vcp →
    ∃ D, Spill.SpillAvail vcp D ∧ ∀ v, D 0 v = false
def Spill.entryParamsB (f : Clif.Function) : Bool   -- entry block params = signature params
structure Spill.DefAvail (vc : VCode) (M : Nat → Nat → Bool) : Prop  -- SpillAvail's shape; every def defines
theorem Spill.spillAvail_and (hK : SpillAvail vc K) (hM : DefAvail vc M) :
    SpillAvail vc (fun b v => K b v && M b v)
theorem Spill.defAvail_prepare (hv : LowOk vc) (hp : prepare vc = .ok vcp) (hM : DefAvail vc M)
    (h0 : ∀ v, M 0 v = false) : ∃ M', DefAvail vcp M' ∧ ∀ v, M' 0 v = false
theorem Spill.defined_of_paths' (hU : UsesDefined vc) (hP : ParamArgs vc) :
    ∃ M, DefAvail vc M ∧ ∀ v, M 0 v = false    -- M := the meet over the CFG paths (pathSets)
theorem Spill.paramArgs_of_lowOk (hv : LowOk vc) : ParamArgs vc
def E2E.LowerDefinedHyp : Prop := ∀ p f vc, InSubset p f → Spill.ArityOk f → Dominated f →
    LowerScope f → Spill.entryParamsB f = true → lowerFunction f = .ok vc →
    ∃ M, Spill.DefAvail vc M ∧ ∀ v, M 0 v = false
theorem E2E.spillDefinedHyp_of_lower (h : LowerDefinedHyp) : SpillDefinedHyp
theorem E2E.LinkCheck.crate_correct_inScope_lower (hM : LowerDefinedHyp) (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) (n : String) : CrateStmtT I n
def DefRun.DefRunsHyp : Prop   -- per ISLE run: uses are reached CLIF values' vregs or fresh vregs
                               -- defined earlier in the run; results likewise (open)
theorem DefRun.lower_defined (hR : DefRunsHyp) (hd : Dominated f) (hs : LowerScope f)
    (ha : AbiSigsOk f) (har : Spill.ArityOk f) (hen : Spill.entryParamsB f = true)
    (hl : lowerFunction f = .ok vc) : ∃ M, Spill.DefAvail vc M ∧ ∀ v, M 0 v = false
theorem E2E.lowerDefinedHyp_of_runs (hR : DefRun.DefRunsHyp) : LowerDefinedHyp
theorem E2E.LinkCheck.crate_correct_inScope_runs (hR : DefRun.DefRunsHyp) (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) (n : String) : CrateStmtT I n
theorem DefRun.defRunsHyp : DefRunsHyp
theorem E2E.lowerDefinedHyp : LowerDefinedHyp
theorem E2E.spillDefinedHyp : SpillDefinedHyp
theorem E2E.LinkCheck.crate_correct_inScope_proven (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) (n : String) : CrateStmtT I n
```

Availability (no use reads a vreg killed without a store) is proven (`spillKillFree`); what
remained was definedness of `lowerFunction`'s VCode (`LowerDefinedHyp`; by `defined_of_paths'` and
`paramArgs_of_lowOk` it is `UsesDefined`: every use is defined on every CFG path from the entry
that reaches it). Neither route avoids it: it does not follow from the semantic contracts
(`LowerInstOk.run` holds for every initial vreg file, and a read of a temporary before its def
whose value does not matter is consistent with it), and the link-level theorems cannot use
`AllocChecked` instead of `checkAlloc` without the same fact (two activations with the same
body-entry world must give one VCode outcome, so the initial vreg file must not matter; the
spill allocation's homes are frame slots, garbage at entry). The driver's assembly of the runs
into `UsesDefined` is proven (`DefRun.lower_defined`, `FV/Backend/Proof/DefAssemble.lean`): along
every CFG path, on entry to CLIF block `bi`'s code the renamed values of `availIn` (and, but for
the entry block, the parameters) are defined, and on entry to an edge block of `bi` what its code
defines at the end (the renamed values available there, a `try_call`'s result vregs); inside a
block, the entry parameters are defined by the argument setup (`entryParamsB`), a statement's
results by its run (`OutDef`, through the alias renaming), and a run's uses are available reached
values or fresh vregs an earlier instruction of the run defines (`RunDef`; the `try_call`'s call
replaced by the `tryCall` keeps it). The ISLE run facts `DefRunsHyp` are proven
(`DefRun.defRunsHyp`, `FV/Backend/Proof/DefRunsProof.lean`). They are a flow-sensitive invariant
(`writable_reg_to_reg` is the identity on ISLE values, so the uniform invariants of
`KillGen`/`IselFlowCheck` cannot tell a temporary before its def from one after), proven by an
abstract interpretation of the rules (`FV/Backend/Proof/DefGen*.lean`): symbolic abstract values
whose meaning depends on the defined vregs `D` (the reached CLIF values' vregs and the defs of the
instructions emitted since the run started) and on the rule's environment — clean values,
pending temporaries, the identity of a let-variable, values that hold once given instructions are
emitted (`ProducesFlags`/`ConsumesFlags`/side effects carry instructions emitted later), call
infos and return lists whose defs cover given variables. `emit` checks the instruction's uses are
defined and marks the variables in its def fields defined. Soundness by fuel induction
(`DefGen.soundAt`, `dRoot`); the extern constructors/extractors, the oracles and the
constructor-tree terms meet their transfers (`DefGen.dModel`, `dOracle`, `dWrap`); every rule of
the 1149 terms the roots reach and every root rule of `lower`/`lower_branch` check
(`DefGen.tabOK`, `rootLower`, `rootBranch`, kernel-checked certificates), but `nop`'s rule 587 (by hand) and
636/637 (never match). Non-vacuity: `E2E.spillAvail_defined_witness`; `crate_correct_proven`/
`crate_correct_fvDemo_proven` (`InScopeWitness`) instantiate `crate_correct_inScope_proven`. Witness of the crate theorem:
`crate-proofs/Crates/InScopeWitness.lean` decides `InScopeP` (with `entryParamsB`) and
`linkerOkB` of `a_arith` (58 functions) and `fv-demo` (551) by `native_decide`.

**The Lean linker (L2b stages 1–2, `FV/Link/`, docs/research/lean-linker.md).** The program
part (the Lean-compiled functions) is placed, relocated and written by Lean; rust-lld links the
outside part around a placeholder of the region:

```lean
structure Link.LinkSpec   -- funcs (placement order), names, sizes, outside, data, symNames, R
def LinkSpec.input (S : LinkSpec) : LinkInput   -- link map = the placement (`offs`: each
                                                -- function, then one zero gap word)
def LinkSpec.placeOkB (S : LinkSpec) : Bool      -- distinct names, positive sizes, region in
                                                -- range, no outside symbol in it
def LinkSpec.namesOkB/sizesOkB (S) (T) : Bool    -- the compiled code has the given names, sizes
def Link.resolveWord (I) (tp) (a : Art) (k : Nat) : BitVec 32   -- bl; adrp+add for both page
                                                -- pairs (the GOT pair too: PairOk.adrpAdd);
                                                -- TLSDESC → movz/movk/nop/nop of tpOff
def Link.relocsOkB (I) (tp) (a : Art) : Bool     -- the linker's shape/range checks
def Link.regionOkB (file : ByteArray) (R n off : Nat) : Bool   -- rust-lld's output: the region
def Link.outsideOkB (I) (D) (file) : Bool         -- rust-lld's output: hdrB, data, symbols
def Link.leanLink (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray
theorem Link.linkerOkB_place (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) :
    linkerOkB S.input = true
theorem Link.leanLink_linkerOk (h : leanLink S file0 = .ok file) : linkerOkB S.input = true
theorem Link.leanLink_code (h : leanLink S file0 = .ok file) :
    ∀ e ∈ tabOf S.input.resultsT, ArtOk S.input file e.2
theorem LinkSpec.input_results : S.input.results = S.input.resultsT  -- `fallback := true`
theorem Link.binOk_leanLink (h : leanLink S file0 = .ok file) : BinOk S.input S.data file
theorem Link.leanLink_static' (h : leanLink S file0 = .ok file) : Static file
theorem Link.binOkT_leanLink (h) (hs : Static file0) (hd : ∀ o ∈ D, DataOk S.input file o)
    (hy : SymsOk S.input file) : BinOk S.input D file        -- stage 1, kept
theorem Link.crate_correct_leanLink (hD : SpillDefinedHyp) (hin : InScopeP S.input = true)
    (h : leanLink S file0 = .ok file) (n : String) : CrateStmtT S.input n
theorem Link.crate_correct_leanLink_lower (hM : LowerDefinedHyp) (hin : InScopeP S.input = true)
    (h : leanLink S file0 = .ok file) (n : String) : CrateStmtT S.input n
theorem Link.crate_correct_leanLink_proven (hin : InScopeP S.input = true)
    (h : leanLink S file0 = .ok file) (n : String) : CrateStmtT S.input n
```

So with the Lean linker the crate theorem has no `linkerOkB` premise and `BinOk` has no
premise: `linkerOkB` and the code are proven by construction; the
facts about the bytes rust-lld wrote — the headers (`Static`), cg_clif's data objects
(`DataOk`), the symbol table (`SymsOk`, which for the program's functions is that rust-lld put
them at their placement) and the region's segment (`regionOkB`) — are `leanLink`'s checks of
rust-lld's output (`regionOkB`, `outsideOkB`), so a failure is a link error. Witness:
`crate-proofs/Crates/LeanLinkWitness.lean` (`a_arith`'s 58 functions, `native_decide`). Tooling:
`cargo fv --lean-link` (`rust/crates/cargo-fv/src/leanlink.rs`, `lake exe lean-link`): the
survey crates, `fv-demo` and `examples/deps`' `deps-demo` exercise this path. Unverified
functions keep cg_clif's code; direct recursion and taking one's own function address are
not fallback reasons.

**The executable compiler (L1, `FV/Link/Compile.lean`, `Exe.lean`, `ExeTotal.lean`).** The
binary chain (`okB`, `BinOk`, `binary_correct_*`, `binary_correct_exec_proven`) is stated for
`LinkInput.results`; the input's `fallback` field selects its pipeline: `false` (the default,
every generated crate input and `link-check`) the checker's `pipe` (regalloc2's answer as given),
`true` the compiler's `pipeT` (`LinkInput.results_fallback : I.fallback = true → I.results =
I.resultsT`, `okB_fallback : okB I = okR I I.resultsT`: the same checks on the compiler's own
output). `LinkSpec.input0` sets it, so every theorem of the chain applies to `leanLink`'s input.

```lean
def Link.compileExe (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  if InScopeP S.input0 then leanLink S file0 else .error "…"
-- leanLink also checks `codeMapB S.input (tabOf S.input.resultsT)` (cheap; alias-free: proven)
theorem Link.okB_leanLink (hin : InScopeP S.input = true) (h : leanLink S file0 = .ok file) :
    okB S.input = true                                  -- okT_of_inScope, spillDefinedHyp
theorem Link.leanLink_gotSlot (h : leanLink S file0 = .ok file) (a) : ¬ GotSlot S.input file a
theorem Link.gotOk_leanLink (h) : GotOk S.input file        -- no GOT slot: adrp+add
theorem Link.compileExe_correct (h : compileExe S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B) (hf : (prog S.input).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f) (M : Nat)
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (roByte S.input S.data) f (StackBound.stackFn S.input f) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs)
theorem Link.compileExe_correct_depth (h : compileExe S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B) (hf : (prog S.input).func? n = some f)
    (M : Nat) (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (roByte S.input S.data) f
      (frameDrop (art S.input f).af + S.input.D * M) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs)
theorem Link.compileExe_correct_peak (h : compileExe S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B) (hf : (prog S.input).func? n = some f)
    (F d : Nat) (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (roByte S.input S.data) f
      (frameDrop (art S.input f).af + S.input.D * d) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.input) d cs)        -- no reached state has > d callers
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (F + 1) cs)
def Link.relocShapeB (a : Art) (r : Reloc) / relocRangeB (I) (tp) (a) (r) : Bool
                                   -- relocOkB = shape (code) ∧ range (addresses): relocOkB_of
theorem Link.relocShapes_of_pipeT (ha : pipeT g k base o = .ok a) : relocShapesB a = true
theorem Link.codeMap_place (hp) (hr) (hn) (hs) :
    codeMapB S.input (tabOf S.input.resultsT) = true
theorem Link.compileExe_total (hin : InScopeIn S.input0 = true)   -- InScopeP before L1g (#228)
    (hp : S.placeOkB = true) (hn : S.names = S.funcs.map (·.func.name)) (hs : S.sizes = S.sizesOf)
    (hrange : ∀ e ∈ tabOf S.input.resultsT, ∀ r ∈ e.2.fb.relocs,
      relocRangeB S.input (tpOff phs) e.2 r = true)
    (hph : phdrs (fileRd file0) = some phs) (hreg : regionOkB file0 S.R (regionOf S (tpOff phs)).size
      (offsetOf phs S.R) = true)
    (hout : outsideOkB S.input S.data (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) = true) :
    compileExe S file0 = .ok (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs)))
-- L1e (FV/Link/ExeInput.lean): the Lean compiler's layout, conditions on the inputs only
def Link.LinkSpec.withSizes (S : LinkSpec) (sz : List Nat) : LinkSpec :=
  { S with names := S.funcs.map (·.func.name), sizes := sz }
def Link.LinkSpec.placed (S : LinkSpec) : LinkSpec := S.withSizes S.sizesOf
def Link.LinkSpec.layoutOkB (P : LinkSpec) : Bool  -- 0 < R, 4 ∣ R, R + P.size < 2^64, clearOfB
def Link.LinkSpec.file0OkB (P : LinkSpec) (file0 : ByteArray) (phs : List Phdr) : Bool :=
  let off := offsetOf phs P.R
  regionOkB file0 P.R P.size off && hdrB [(0, file0)] &&
    dataFastB P.input0 P.data (maskEx file0 off P.size) && symsOkB P.input0 file0 &&
    symFootB file0 (off + P.size) && tlsOkB P phs
def Link.CallPageReach (S : LinkSpec) (phs : List Phdr) : Prop :=   -- remaining output premise
  ∀ e ∈ tabOf S.placed.input.resultsT, ∀ r ∈ e.2.fb.relocs, r.type ≠ .tlsDescAdrPage21 →
    relocRangeB S.placed.input (tpOff phs) e.2 r = true
theorem Link.compileExe_total_input (hin : InScopeIn S.placed.input0 = true)
    (hl : S.placed.layoutOkB = true) (hph : phdrs (fileRd file0) = some phs)
    (hf : S.placed.file0OkB file0 phs = true) (hreach : CallPageReach S phs) :
    compileExe S.placed file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf S.placed (tpOff phs)))
theorem Link.placed_of_compileExe (h : compileExe S file0 = .ok file) : S.placed = S
-- the shipped compiler (FV/Link/ExeInputCleanup.lean): DeadCleanup.placed S := S.withSizes
-- (DeadCleanup.sizesOf S); DeadCleanup.CallPageReach over resultsCleanupT
theorem Link.DeadCleanup.compileExe_total_input (hin : InScopeP (placed S).input0 = true)
    (hl : (placed S).layoutOkB = true) (hph : phdrs (fileRd file0) = some phs)
    (hf : (placed S).file0OkB file0 phs = true) (hreach : CallPageReach S phs) :
    compileExe (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs)))
theorem Link.DeadCleanup.placed_of_compileExe (h : compileExe S file0 = .ok file) : placed S = S
-- L1e, reach on the inputs (FV/Link/ExeInputReach.lean): the CLIF functions' references
def Backend.Proof.RelocProv.RelocOk (f : Clif.Function) (r : Reloc) : Prop :=
  match r.type with
  | .call26 => r.sym ∈ externNames f                        -- names of f.externs
  | .adrGotPage | .adrPrelPgHi21 => r.sym ∈ refNames f ∧ r.addend ∈ refOffs f
  | _ => True                                                -- refNames: externs, symbol gvs
def Link.LinkSpec.callReachB (P : LinkSpec) (t : Nat) : Bool :=  -- refOffs: 0, gv offsets
  t % 4 == 0 && decide (P.R + P.size ≤ t + 2 ^ 27) && decide (t < P.R + 2 ^ 27)
def Link.LinkSpec.pageReachB (P : LinkSpec) (T : Nat) : Bool :=
  decide (pageOf (P.R + P.size) ≤ pageOf T + 2 ^ 20) && decide (pageOf T < pageOf P.R + 2 ^ 20)
def Link.LinkSpec.refsReachB (P : LinkSpec) (f : Clif.Function) : Bool :=
  (externNames f).all (fun n => P.callReachB (P.input0.addrOf n)) &&
  (refNames f).all fun n => (refOffs f).all fun o => P.pageReachB (P.input0.symAddr n o).toNat
def Link.LinkSpec.reachOkB (P : LinkSpec) : Bool := P.funcs.all fun fi => P.refsReachB fi.func
theorem Link.relocOk_tab (hin : InScopeP S.placed.input0 = true) :
    ∀ e ∈ tabOf S.placed.input.resultsT, ∀ r ∈ e.2.fb.relocs, RelocOk e.1 r
theorem Link.callPageReach_of (hin : InScopeP S.placed.input0 = true)
    (hl : S.placed.layoutOkB = true) (hreach : S.placed.reachOkB = true) : CallPageReach S phs
theorem Link.compileExe_total_reach (hin : InScopeIn S.placed.input0 = true)
    (hl : S.placed.layoutOkB = true) (hph : phdrs (fileRd file0) = some phs)
    (hf : S.placed.file0OkB file0 phs = true) (hreach : S.placed.reachOkB = true) :
    compileExe S.placed file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf S.placed (tpOff phs)))
-- the shipped compiler (FV/Link/ExeInputReachCleanup.lean)
theorem Link.DeadCleanup.compileExe_total_reach (hin : InScopeP (placed S).input0 = true)
    (hl : (placed S).layoutOkB = true) (hph : phdrs (fileRd file0) = some phs)
    (hf : (placed S).file0OkB file0 phs = true) (hreach : (placed S).reachOkB = true) :
    compileExe (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs)))
-- the shipped compiler on input conditions decided without compiling (V7,
-- FV/Link/ExeInputReachCleanupIn.lean; `inScopeP_of_input : InScopeIn I = true → InScopeP I = true`)
theorem Link.DeadCleanup.compileExe_total_reach_input (hin : InScopeIn (placed S).input0 = true)
    (hl : (placed S).layoutOkB = true) (hph : phdrs (fileRd file0) = some phs)
    (hf : (placed S).file0OkB file0 phs = true) (hreach : (placed S).reachOkB = true) :
    compileExe (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs)))
```

`compileExe_correct` has no per-program premise and no open hypothesis about the compiler; its
premises are the outside code's contracts and the CLIF-level condition that no call cycle is
reachable from the entered function. `compileExe_total`'s hypotheses are the input conditions,
the driver's data, the addresses (the relocations' reach) and rust-lld's output.
`Link.compileExe` checks the input-only `InScopeIn` (`inScopeInPar`, L1g #228; before, `InScopeP`,
whose `lowersB` runs `lowerFunction`/`prepare`): `compileExe_spec` still gives `InScopeP`
(`inScopeP_of_input`), so the correctness theorems are unchanged; the totality theorems
`compileExe_total{,_input,_reach}` take `InScopeIn` in place of `InScopeP` — a deliberate premise
strengthening forced by the definition change (`compileExe` now rejects inputs outside
`InScopeIn`). The two acceptance sets agree on the corpus (`lean-e2e-check` 1150 / 1150) and on
fv-demo and the survey; the former `Link.compileExe_total_reach_input` coincided with
`compileExe_total_reach` and is removed. `Link.DeadCleanup.compileExe` still checks `InScopeP`.
`compileExe_total_input` (L1e, #216) takes the Lean compiler's layout (`S.placed`; `placeOkB`
from `InScopeP` and `layoutOkB`, compiled code nonempty: `pipeT_words_pos`) and moves rust-lld's
checks from the patched file to `file0` (`outsideOkB_patch`: the region's bytes are read by none
of them when the section headers, symbol and string tables lie after it, `symFootB`); TLS offsets
come from `file0`'s `PT_TLS` (`tlsOkB`). Its one output-dependent premise is `CallPageReach`;
`compileExe_total_reach` replaces it by `reachOkB`, decided on the CLIF functions and the link
map: the compiled code of `f` relocates only against `f`'s declarations (`relocOk_tab`; the ISLE
lowering by an abstract interpretation of the rules, `Backend.Proof.RelocProv.lowerFunction_refs`;
`prepare`, the allocation, emission and layout, `relocs_of_alloc`), and `reachOkB` puts every
declared name (with every declared offset) in `bl`/`adrp` reach of the whole region.
`Link.DeadCleanup.compileExe_total_input`/`_reach`: the same for the shipped compiler. Witnesses:
`total_input_witness`, `total_input_cleanup_witness`, `total_reach_witness`,
`total_reach_cleanup_witness`.
`LinkSpec` is alias-free by construction; #88 removes alias generation and `AliasOut` rather
than assuming or proving renaming invariance of the compiler. Native recursion is admitted
by totality, and since L1d (#204) by executable correctness too (below). Witnesses:
`crate-proofs/Crates/CompileExeWitness.lean` (`a_arith`: `compile_eq`, `correct_closed`,
`total_witness`) and `CompileExeRunWitness.lean` (`compileExe_run_witness`: every premise of
`compileExe_correct` for one concrete outside call into the panic=abort `a_arith` compiled by
`compileExe`; the executable machine returns `5`). `lake exe lean-link` runs
`Link.DeadCleanup.compileExe` by default (`--no-dead-cleanup`: `compileExe`; the theorems of the
cleanup compiler: "The shipped compiler" below); on an input outside `InScopeP` it prints the
failing conditions and links with the bare Lean linker (not covered by `compileExe_correct`),
except under `--verified`, where that is an error.

**The executable on the original source program (S2/S3, `FV/Link/ExeSource.lean`).**
`compileExe_correct` relates the executable to `prog S.input`, the input's functions after the
`i128` legalisation (`compileExe` runs no optimiser). `Link.compileExe_correct_source` relates
it to the **original** parsed program `S.input.srcProg` (`LinkInput.prog_eq : I.prog =
legalProg I.srcProg`): for an input in the decidable source domain `SrcScopeB`, a return of the
original program's whole-program CLIF run of a source function `f` on `args` is the
executable's return of the results split by `f`'s return groups, after an outside call of the
compiled `legalize f` with the ABI-split arguments; a trap is the same trap. It composes
`E2E.LegalProgram.legalProg_refines` with `compileExe_correct`; no checker premise. Statement,
premises and their kinds: `docs/contracts/legalize128.md` ("The executable compiler on the
original source program"). The premises beyond `compileExe_correct`'s: the outside
environment's `HelperOk`/`ExtLegal`/`EnvKeepsBounded` when a source function mentions `i128`,
`sigOf = none` with indirect calls (environment); the source run's memories below `2^64` and,
for traps, its `NoMemTrap` and the target's `TrapsExplicit` (run conditions). Witness:
`crate-proofs/Crates/CompileExeSourceWitness.lean` (`g_u128`'s `wmul_u128` calling
`wrapping_mul` on `i128` values, under `Link.SourceWitness.helperBase`; the executable returns
the split product in x0, x1).

**Recursive programs (L1d, #204, #215).** `compileExe_correct_depth` drops the
call-graph premise `¬ CycleFrom`: the outside caller provides `frameDrop (art S.input f).af +
S.input.D * M` bytes of stack instead of `stackFn` (`S.input.D`: the largest frame of the program,
`LinkSpec.input`/`depthOf`), for the CLIF run of at most `M + 1` steps. The resource condition
that replaced acyclicity is the depth budget of the linking induction itself
(`LinkSys.budget_K`: `frameDrop h + D·M ≤ D·(M+1)` for every call), which needs no call-graph
fact. The chain: `Binary.binary_correct_depthX` (`FV/E2E/BinaryGood.lean`: `binary_correctX` with
the depth budget, read-only data facts allowed), `ExecBytes.runGood_sysS_of` (`ExecGot.lean`:
`RunGoodL` of the system keeping the GOT slots for any `LinkSys.Budget`; `runGood_sysS` with the
static budget, `runGood_sysS_depth` with `D·M`; `sysS` takes the budget `K`),
`ExecBytes.exec_of_runGood` (`ExecProven.lean`: the lockstep, D2 and D4 from the model-level facts,
whatever the budget; `binary_correct_exec_proven` is now its instance too) and
`ExecBytes.binary_correct_exec_depth_proven`. `compileExe_correct` is unchanged (not a corollary:
its `stackFn` is less than `frameDrop + D·M` in general). Axioms of the new theorems: `propext`,
`Classical.choice`, `Quot.sound`. Witness (`crate-proofs/Crates/CompileExeRecWitness.lean`):
`compileExe` compiles the natively self-recursive `direct` (`E2E.LinkWitness.DirectSelf`; its
entry reaches a call cycle, `cyclic`), and `compileExe_rec_witness` applies
`compileExe_correct_depth` to the outside call `direct(3)` (four activations; the CLIF run
returns `6`): the executable machine returns `6` in x0. `stack_needed`: the premise asks for more
than `stackFn` and fails for the same call with `sp = 16`.

**Peak call depth instead of fuel (L1d).** `compileExe_correct_peak` replaces `D·M` by `D·d`,
where `d` bounds the call depth of the source run: `Clif.DepthLe B.env (prog S.input) d cs`
(every state the whole-program run from `cs` reaches, `Clif.Reaches`, has at most `d` callers,
i.e. at most `d + 1` live activations), independent of the run's fuel `F`; decidable along a run
that ends by `Clif.depthB` (`depthLe_of_depthB`). The linking induction (`LinkSys.thm`/`thmG`/
`thmX`) is unchanged; what it reads of the CLIF side is abstracted: a linked system carries the
callee runs `crun M` of its depth-`M` callees (a `LinkSys` field, default the whole-program run
of `M` steps), the per-function environments are `Clif.linkEnvR P base (crun M)`, and
`LinkSys.CrunOk` states what the induction needs of them (a returning run is a whole-program run;
a complete one at depth `M` is a run of `P.bare` under the callee runs at depth `M - 1`). The
default satisfies it (`crunOk_std`, from `Clif.runLoop_linkN`), so the fuel-indexed theorems are
its instance (`LinkSys.std`); so do the runs of a fixed fuel `F` with at most `M - 1` callers of
their own (`Clif.runD`, `Clif.linkEnvD`, `crunOk_peak`, from `Clif.runLoop_linkD`): the induction
runs on the depth with the fuel fixed. `Clif.runLoop_linkR` is the CLIF linking lemma for any
callee runs that are the callee's whole-program run for every callee entered from a state the run
reaches (`runLoop_linkN`, `runLoop_linkD` its instances; `DepthLe.callee`: a callee entered under
`K ≠ []` callers within a run of depth `d` has depth `d - 1`). The machine side does not read the
callee runs (`mach_withCrun`, `runGoodL_withCrun`). The chain: `backend_correct_program_core`/
`coreX` (any `CrunOk`), `backend_correct_program_peak`/`peakX` (`LinkSys.peak F`),
`Binary.binary_correct_peakX`, `ExecBytes.runGood_sysS_peak` (`sysS_entry`: the entry premises
of the system keeping the GOT slots, shared with `runGood_sysS_of`),
`ExecBytes.binary_correct_exec_peak_proven`, `Link.compileExe_correct_peak`; for a returning run
`TrapsExplicit` under `linkEnvD` holds (`Binary.trapsExplicit_of_runD`). Axioms: `propext`,
`Classical.choice`, `Quot.sound`. `compileExe_correct_depth` is kept (its `TrapsExplicit` is under
`linkEnvN`, not `linkEnvD`). Witness (`crate-proofs/Crates/CompileExePeakWitness.lean`): the
executable of `CompileExeRecWitness` (`direct`; `frameDrop` = `D` = 288 bytes, the code at 16 MiB);
outside code calls `direct(3)` with `sp = 0x480`, exactly `288 + 288·3` bytes; the CLIF run's
peak call depth is 3 (`Clif.depthB`: four activations) and it returns `6` within 24 steps;
`compileExe_peak_witness` applies `compileExe_correct_peak` (`d = 3`, fuel 64) and gives the
executable machine returning `6` in x0. `depth_premise_fails`: the run does not return within 23
steps, so `compileExe_correct_depth` needs a fuel `M ≥ 23` to say anything about it, and its stack
premise `frameDrop + D·M ≥ 288·24` fails in that machine state for every such `M`.

*Gap: largest frame.* Each level is charged the largest frame `D` of the program, not the frames
live along the executed call derivation: exact accounting needs a budget indexed by the run, not
`LinkSys.Budget` over every syntactic callee.

**The shipped compiler; recursive programs on the original source (L1f, #217).** What
`lake exe lean-link` and `cargo fv --lean-link` run by default is `Link.DeadCleanup.compileExe`
(the same `InScopeP`, then `Link.DeadCleanup.leanLink`, whose pipeline `pipeCleanupT` removes dead
pure machine instructions, docs/contracts/dead-cleanup.md). Its theorems, matching the baseline
compiler's, composed from the cleanup chain without changing it:

```lean
theorem Link.DeadCleanup.compileExe_correct_peak       -- FV/Link/DeadCleanupExePeak.lean
  -- = Link.compileExe_correct_peak over S.inputCleanup (stack frameDrop + D·d, Clif.DepthLe)
theorem Link.DeadCleanup.compileExe_correct_source     -- FV/Link/DeadCleanupExeSource.lean
  -- = Link.compileExe_correct_source over S.inputCleanup (¬ CycleFrom, stackFn)
theorem Link.DeadCleanup.compileExe_correct_source_peak
  -- = Link.compileExe_correct_source_peak over S.inputCleanup
theorem Link.compileExe_correct_source_peak {S file0 file} (h : compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.input = true) (B) (hB) (hH) (hlegal) (hsig)
    (hf : S.input.srcProg.func? n = some f) (d : Nat) (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (roByte S.input S.data) (legalize f)
      (frameDrop (art S.input (legalize f)).af + S.input.D * d) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs') (hcs : ClifEntry f args cs)
    (hexp) (hsl) (hmem) (hbnd)
    (hd : Clif.DepthLe B.env S.input.srcProg d cs)       -- the SOURCE run's call depth
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', ExpRel (returns groups) vals vals' ∧ ExecRefines … (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      NoMemTrap B.env S.input.srcProg cs → ∀ c, … = .trapped c → ExecRefines … (.trapped c))
```

The cleanup chain's binary/exec layer is a copy of the baseline's with the cleanup input
(`LinkSys.ofInputCleanup`, `okBCleanup`, `DeadCleanupBinCheck.BinOk`), while the linking
induction (`backend_correct_program_peakX`, `LinkSys.budget_K`) is generic in the linked system;
`FV/E2E/DeadCleanupExecPeak.lean` adds the peak wrappers over it (`DeadCleanupBinary.
binary_correct_peakX`; `DeadCleanupExecBytes.sysSK`, the GOT-keeping system with any callee budget
— the cleanup `sysS` fixes `stackFn`'s —, `runGood_sysSK_peak`, `got_of_goodK`,
`exec_of_runGood`, `binary_correct_exec_peak_proven`). `prog S.inputCleanup` is the input's CLIF
functions (`progOf_resultsCleanupT`), hence `legalProg S.inputCleanup.srcProg`
(`Link.DeadCleanup.prog_eq_legal`), so the source theorems compose
`legalProg_refines`/`legalProg_refines_depth` with the cleanup theorems as `ExeSource` does with
the baseline's.

*The legalisation keeps the call depth* (`FV/E2E/LegalDepth.lean`,
`E2E.LegalProgram.legalProg_refines_depth`): if the source run from `h`'s entry has call depth at
most `d` (`Clif.DepthLe`), so has the legalised program's run that matches it. It is
`legalProg_refines`' induction on the fuel at every depth (`RefinesD`): the guarded source
environment `guardEnvD` runs a callee only from a good entry of depth at most `d - 1`
(`DepthCall`; `guard_runD`: the whole program enters each callee under one more caller,
`DepthLe.callee`), the target environment `tgtEnvD` runs a callee of `legalProg P` only from an
entry of depth at most `d - 1` (else stuck), and the induction hypothesis at `d - 1` gives that
for every callee the target run enters (`prog_callD`). `Clif.unlink_depth`
(`Clif.UnlinkD`: the environment's program callees return or trap only from entries of depth
at most `d - 1`) turns the returning or trapping target per-function run into whole-program depth
`d`: per-function states have no callers, a callee's states are below one caller until it
returns (`Clif.Reaches.below_cases`, `Reaches.done_outcome`). The legalised run's
`TrapsExplicit` under `linkEnvD` for a return is `Binary.trapsExplicit_of_runD`. Axioms of all
new theorems: `propext`, `Classical.choice`, `Quot.sound`.

Witnesses (closed, `native_decide` facts as in the other witnesses): `crate-proofs/Crates/
CompileExeSourcePeakWitness.lean` — the self-recursive `i128` `rec128(x, n) = n = 0 ? x :
rec128(x + x, n - 1)` compiled by `compileExe` (`cyclic`: the acyclic theorems do not apply), the
original program's run of `rec128(2^64 + 3, 3)` has call depth 3 and returns `8·2^64 + 24`, and
with `frameDrop + D·3` bytes of stack and the split arguments `3, 1, 3` the executable returns
`24, 8` in x0, x1 (`compileExe_source_peak_witness`); `DeadCleanupExePeakWitness.lean` — the same
program compiled by `Link.DeadCleanup.compileExe`: `cleanup_peak_witness` (the legalised run, depth
3, returns `24, 8`) and `cleanup_source_peak_witness`; `DeadCleanupExeSourceWitness.lean` —
`g_u128`'s `wmul_u128`/`wrapping_mul` compiled by `Link.DeadCleanup.compileExe`
(`cleanup_source_witness`, split product `15, 5`). Their `helperBase` instances:
`Link.SourceWitness.compileExe_correct_source_peak_helper`,
`Link.DeadCleanup.SourceWitness.compileExe_correct_source{,_peak}_helper`.

*Fail closed (`--verified`).* `lake exe lean-link DIR [--dead-cleanup|--no-dead-cleanup] [--opt]
[--verified]` (the layout is the Lean compiler's, `Link.DeadCleanup.placedPar`/
`LinkSpec.placedPar` `= placed`, `FV/Link/PlacedEq.lean`; no sizes are read) prints after writing
the executable the theorems covering it: `coverage:
Link.DeadCleanup.compileExe_correct, Link.DeadCleanup.compileExe_correct_peak` and, for an input
in `SrcScopeB` (decided by the tool: `FV/E2E/SrcScopeDefs.lean`; it reads the parsed functions
only, so `S.input0`'s is the theorems' `S.inputCleanup`'s), `…_source, …_source_peak`; the bare-
linker fallback prints `coverage: none (…)`. With `--verified` an input outside `SrcScopeB`,
outside `fnScopeInB` (the per-function input conditions decided on the CLIF alone, V7: the tool
names the failing conjuncts) or outside `InScopeP` is an error (exit 1, the executable not
written), so every executable it writes is covered by the four theorems and its input is in
`InScopeIn`; its `coverage:` line adds `input in InScopeIn (totality:
Link.DeadCleanup.compileExe_total_reach_input)`. `cargo fv --lean-link --verified` passes it (own
target dir) and records the coverage in the report (`binary.lean_link`).

**The optimising executable compiler (S1, S2; #25, #26).** `Link.compileExeOpt S file0 :=
compileExe S.opt file0` and `Link.DeadCleanup.compileExeOpt` (`FV/Link/OptCompile.lean`; what
`lake exe lean-link --opt` and `cargo fv --lean-link --opt-proven-only` run): parse → `i128`
legalisation → the mid-end `Opt.optimizeExe` with the proven rule sets (`Opt.exeConfig`;
`call_indirect` and `try_call`/`try_call_indirect` included, docs/contracts/midend.md "The
executable compiler's mid-end") → backend. `LinkSpec.opt` prints every optimised function after
its file's header and uses the text only when it parses (and legalises) back to the optimised
function (`FnInput.opt`), else keeps the input (`LinkSpec.optFallbacks`, printed by
`lean-link --opt`: 0 on fv-demo and the survey); it also keeps the input when the mid-end dropped
one of its indirect-call signatures (`keepsIndB`: the source theorems without the memory bound,
`compileExeOpt_correct_source{,_peak}_nobnd`, budget every callee the source run can enter by
the optimised call graph; legalize128.md "The memory bound derived"). Its theorems (`FV/Link/OptExe.lean`,
`FV/Link/DeadCleanupOptExe.lean`) compose `compileExe`'s, about the optimised input `S.opt`,
with the mid-end's whole-program refinement (`OptRel.refines`, which keeps the call depth) and,
for the source theorems, the legalisation's:

```lean
theorem Link.compileExeOpt_correct {S file0 file} (h : compileExeOpt S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)                    -- the mid-end's contract
    (hf : (prog S.input).func? n = some f) (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args cs'.mem)
    (hr : ClifRun S.opt.input B f' r args cs') (hcs : ClifEntry f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : …slots…) (hmem : cs.mem = cs'.mem) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (prog S.input) M cs = .returned vals cm →
      ExecRefines (art S.opt.input f').fb … (.returned vals cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.input) B.env K) (prog S.opt.input).bare cs') →
      ∀ c, Clif.runLoop B.env (prog S.input) M cs = .trapped c → ExecRefines … (.trapped c))
theorem Link.compileExeOpt_correct_peak         -- frameDrop + D·d for the input run's depth d
theorem Link.compileExeOpt_correct_source       -- the original program S.input.srcProg (SrcScopeB)
theorem Link.compileExeOpt_correct_source_peak
theorem Link.compileExeOpt_total_reach_input    -- compileExeOpt (S.withSizes (sizesOf S.opt)) succeeds
-- and Link.DeadCleanup.compileExeOpt_{correct,correct_peak,correct_source,correct_source_peak,
-- total_reach_input} over S.opt.inputCleanup
```

The premises are `compileExe`'s about the optimised input, plus `EnvKeepsSymbols B.env`; the
run is the *unoptimised* input's program's (after legalisation, or the original program for the
source theorems), so a trap needs `TrapsExplicit` at every fuel (the two runs take different
numbers of steps). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Witnesses: `crate-proofs/Crates/CompileExeOptSourceWitness.lean` (`compileExeOpt_source_witness`)
and `DeadCleanupExeOptSourceWitness.lean` (`cleanup_opt_source_witness`): `g_u128`'s
`wmul_u128`/`wrapping_mul` compiled by `compileExeOpt` and `DeadCleanup.compileExeOpt`; the
mid-end changes both legalised functions (`legalize fs ≠ f`), no print/parse fallback, and the
executable returns the split product `15, 5` (via
`Link.{DeadCleanup.}SourceWitness.compileExeOpt_correct_source_helper`,
`FV/Link/NonVacuityOptExeSource.lean`). `CompileExeOptPeakWitness.lean`
(`compileExeOpt_peak_witness`) and `DeadCleanupExeOptPeakWitness.lean`
(`cleanup_opt_peak_witness`): `compileExeOpt_correct_peak` on the self-recursive `rec128`, which
the mid-end changes (`f0 ≠ f`) and whose optimised entry reaches a call cycle; the unoptimised
legalised run on `3, 1, 3` has call depth `3` and the executable returns `24, 8` with
`frameDrop + D·3` bytes of stack. `CompileExeOptReachWitness.lean` (`total_reach_opt_witness`,
`total_reach_opt_cleanup_witness`): every hypothesis of `compileExeOpt_total_reach_input` holds
on `a_arith`'s 58 functions, all changed by the mid-end. The per-function theorems
`E2E.backend_correct_opt_exe` and `backend_correct_legal_opt{,_env}` (and their `_cleanup`
versions) have the contract
premises of `backend_correct_final` for the optimised function (`final_contracts_witness` at
`f := Opt.optimizeExe f cfg`, as for `backend_correct_opt_proven`); the mid-end refinement
`Opt.optimizeProgramExe_refines`: `Opt.PipelineXWitness.optimizeProgramExe_witness`
(`FV/Opt/Proof/PipelineXWitness.lean`).

Measured (`cargo fv test --lean-link --verified`, debug, `--opt-proven-only` against the
default): identical test results (fv-demo 20 passed; survey 53 passed), the same verified counts
(fv-demo 1346 of 1352, survey 3179 of 3179), every executable written by `compileExeOpt`, no
print/parse fallback, region bytes fv-demo 193628 → 189036 (−2.4%), survey 564512 → 547428
(−3.0%). The binary check (`cargo fv link-proof` + `link-check`) recompiles the bundle's
unoptimised CLIF with the regalloc2 output of the optimised code, so under `--opt-proven-only`
it reports `not verified` (`checkAlloc`), as it did before without `--lean-link`; the
guarantee of these executables is `compileExeOpt`'s.

**Tooling.** `cargo fv build|test --keep-temps` keeps per codegen unit `fv-link.json`: per
Lean-compiled function the CLIF file `lean-backend` compiled (with the self-call alias, or the
optimised dump of the missing-data retry), the register allocator's answers for it (`lean-backend`
writes them to `$FV_RA_OUT` in `lean-regalloc`'s schema, `FVTest/Backend/AllocChoice.lean`),
the merge's names (each CLIF name → the symbol it is linked as; under `--lean-link` also every
name the compiled CLIF declares, its local symbols renamed too, so `Front.assemble` can rename
the dump even when `--opt-proven-only`'s mid-end removed the code using a name) and the object's
local symbols; and per executable the lld link map (`link-<tag>.map`, `link-<tag>.json`).
`cargo fv link-proof`
writes the frontend bundle `bundle.json` (docs/contracts/frontend.md): the files and addresses,
unchanged; `Front.assemble` (T7d) renames the CLIF to the linked symbols (local symbols renamed by
the merge, other local symbols as `sym@<unit>`), finds the data objects the functions reach, and
looks up the other referenced names in the executable's symbol table, with proofs
(`Front.buildSpec_spec`). `lake exe link-check`
completes the input (`syms`: every `symbol` global value and `func_addr` target; `D`: the
largest frame; `raStar = 8`; the self-call aliases), prints the failing checks per function and
premise with details, prunes (`--prune`: the failing functions and, transitively, their
callers, so the rest is closed under calls and no function of the crate becomes a base extern),
runs the binary checks on the executable ("Binary level (M9)": they replace the former
comparison of each function's bytes outside relocated fields), and with `--lean` writes the
proof: the input as string literals (`fnK`, `sliceK`: 32 functions each, `input`),
`sliceK_ok : fnsB input sliceK = true` and `globalB_input` by `native_decide`, `okB_input` from
them (`okB_of`, `fnsB_append`), `link_ok`, `noTls`/`base_closed` (without `tls_value`),
`entries_present`, `correct_i : CrateStmt input "<name>"` per entry, and `bin_ok`. Up to 32
functions it is one file, beyond that `NAME/Input.lean`, one module per slice
(`NAME/SliceK.lean`) and `NAME.lean` importing them.

**Running the checker as compiled code.** `native_decide` (Lean 4.34: `evalConst` of an
auxiliary definition, then an axiom `…_native.native_decide.ax_1_1`) runs a definition natively
when its module's compiled code is loaded, else in the IR interpreter. `precompileModules` on
the crate library would load the shared library of the whole `FV` library, which cannot be built
(the `bv_decide` proof modules of `FV.Opt.Proof` produced C files of up to 3.5 GB, more than
Clang accepts; T6 replaced their `bv_decide` by `kbv`, the C sizes were not re-measured), and Lake's per-module shared libraries are not linked against their imports
on Linux, so loading `FV.E2E.LinkCheck`'s alone fails. So the proofs live in a separate Lake
package, `crate-proofs/` (`require fv from ".."`), whose custom target `fvcheck` links the
object files of the checker modules (`checkRoots`: `FV.E2E.StackBound`, which imports `FV.E2E.LinkCheck`, and `FV.E2E.BinCheck`) and
of the modules they import (about 300; 151 MB of C, already compiled for `link-check`) into one
shared library, and whose library `Crates` loads it while
elaborating (`dynlibs`); Lake rebuilds it when any of those modules changes. Within one file the
`native_decide` theorems run one after another (`nativeEqTrue` compiles and evaluates with
`Elab.async` off), so a large crate's checks are split into slice modules that Lake builds in
parallel.

**Timing** (this machine, 32 cores; `link-check --prune` including the image comparison; `lake
build` of `crate-proofs` from a clean `Crates` build, the FV oleans present):

| | before | after |
| --- | --- | --- |
| `link-check --prune`, nine survey crates | 0.5–17 s each | 0.2–1.1 s each |
| `link-check --prune`, `fv-demo` (550 functions) | 21 min | 7.4 s (crate-check3: 4.8 s) |
| `GU128` proof (19 functions, one file), one `lean` | 17.4 s (interpreted) | 1.6 s |
| one slice of `fv-demo` (32 functions), one `lean` | 60.5 s (interpreted) | 4.2 s |
| `fv-demo` proof (496 functions) | 379 functions did not finish in 40 min (interpreted, one `native_decide`) | 16 slices and the main module, 6–11 s each |
| `fv-demo` proof (545 functions, crate-check3) | — | 18 slices and the main module, 3.0–4.6 s each |
| all ten proofs, `lake build` in `crate-proofs` | — | 18.7 s wall (crate-check3, `fv-demo` with 545 functions: 12.9 s; sret-purpose, 551 functions: 13.3 s) |
| `link-check --prune`, `fv-demo` (551 functions, sret-purpose) | — | 4.4 s |

Most of the old checker time was not the validators: `memT` (a `let` before a `fun`) compiles to
a function of the address that rebuilt the word map on every byte read, so `imgB` was quadratic in
the code size (10.6 s for `d_loops_iters`' 4424 words, minutes for `fv-demo`'s 24000); `imgB`
now builds the map once (`memOfMap`), 10 ms.

**Delivered** (`crate-proofs/Crates/`, from `examples/survey`'s `tests/values.rs` executables
and `examples/fv-demo`'s binary): every Lean-compiled function of the nine survey crates —
`AArith` (58), `BSlices` (59), `CStructsEnums` (27), `DLoopsIters` (117), `EOptionResult` (48),
`FCrypto` (40), `GU128` (19; its `i128` functions are the `Opt.Legalize128` legalisations, so the
theorem is about the legalised program, as in "Widening" 6), `HDynGeneric` (43: `dyn` dispatch
through vtables, `fn` pointers, closures), `IAlloc` (49) — and `FvDemo`: all 550 of `fv-demo`'s
functions plus its recursive function's alias (551; 544 + alias before agent/sret-purpose). Axioms of `link_ok`:
standard plus `globalB_input._native.native_decide.ax_1_1` and one `sliceK_ok._native…` per
slice; of `correct_i`: those (every fixed backend lemma is kernel-checked, T6); `okB_sound`,
`okB_of`: standard.

**Survey** (`link-check --prune`, each crate's codegen unit in its `values` test executable;
`fv-demo`: its binary, two units), after agent/link-scope (`MayCall`, program-wide indirect
resolution, call-result clauses restricted to the site's defs) and after agent/link-scope2
(`BlrTo`: a call through the GOT constrains only its symbol's function; one-copy recursion), and
after agent/crate-check3 (`indSig` and `blrRegs`/`blrTry` for the callees an indirect call's
signature admits, `IndSigMatch`/`IndTo`; aliases outside `P`, Widening 10), and after
agent/sret-purpose (the parameter purposes in `IndSigMatch` and `MayCall`, Widening 11):

| crate | functions | pass (link-scope) | pass (link-scope2) | pass (crate-check3) | pass (sret-purpose) | failing (functions) |
| --- | --- | --- | --- | --- | --- | --- |
| a_arith | 58 | 58 | 58 | 58 | 58 | — |
| b_slices | 59 | 59 | 59 | 59 | 59 | — |
| c_structs_enums | 27 | 27 | 27 | 27 | 27 | — |
| d_loops_iters | 117 | 117 | 117 | 117 | 117 | — |
| e_option_result | 48 | 48 | 48 | 48 | 48 | — |
| f_crypto | 40 | 40 | 40 | 40 | 40 | — |
| g_u128 | 19 | 19 | 19 | 19 | 19 | — |
| h_dyn_generic | 43 | 43 | 43 | 43 | 43 | — |
| i_alloc | 49 | 48 | 49 | 49 | 49 | — |
| fv-demo | 550 | 482 | 495 (+ the alias) | 544 (+ the alias) | 550 (+ the alias) | — |

(The survey crates' proofs were not regenerated: their inputs are unchanged, and `lake build` of
`crate-proofs` re-runs the new checker on them.)

With agent/link-scope2's checker, `fv-demo` failed `indSig` 13, `blrRegs` 3, `blrTry` 3 (+42
callers). Once `indSig` checked only the callees matching a signature, its indirect callers
stayed in the program and the program check `Clif.SymInj` of every name with an address failed
(`core`'s `<u64 as Display>::fmt` and `<usize as Display>::fmt`, folded to one address, both
declared by `fv-demo` functions; vacuous before, every indirect caller having been dropped), and
`blrRegs`/`blrTry` still failed at 6 sites; Widening 10 removes both.

**Blockers on real code**: none on the surveyed crates after agent/sret-purpose. Before it
(after agent/crate-check3):

1. *An indirect call whose signature admits an `sret` callee* (`fv-demo` 2: `Hct6dxdt7Dqo`,
   `HgJo4HgiHAMF`, `catch_unwind` shims). Each has `try_call_indirect` of `func_addr fn0` and, in
   the landing pad, `call_indirect` with signature `(i64, i64)` of `func_addr fn1`. The vtable
   methods `H17D8ApAaVlK` and `H9ubzNsn65EQ` (`(i64 sret, i64)`) have an address (`data_syms`),
   and CLIF's `call_indirect` checks types, not purposes, so `IndSigMatch` admits them: `indSig`
   (an `sret` parameter) and `blrRegs` (x8, x0 against the site's x0, x1) fail. The callee values
   are constants: `func_addr` of a declared function, defined in `block1`, which dominates the
   landing pad. Fix: a CLIF value-flow fact (an SSA invariant of the activation's run: the result
   of `func_addr fnN` holds `fnN`'s address at every use it dominates) restricting `MayCall` at
   such sites to the declared function, with the machine-side counterpart for the vreg's origin
   (as `GotV` does for GOT loads); or CLIF semantics checking the `sret` purpose at
   `call_indirect` (a trusted-semantics change). Done the second way (Widening 11):
   `Clif.stepCallIndirect` compares the parameter purposes, so `MayCall` excludes the two
   methods at the shims' calls; the shims and their 4 callers pass.
2. *Callers of failing functions* (4): dropped by `--prune` so that the rest is closed under calls.

Before agent/link-scope, `blrRegs` at GOT calls of base externs (panics without results next to
a declared program function of the same arity with results) failed in 8 of the 9 survey crates,
and `Clif.IndDecl` failed for every indirect caller of `fn` pointers and vtables (vtable methods
were not CLIF image symbols; the program functions held by the data objects the program
reaches are now among them: `data_syms` of `cargo fv link-proof`, since T7d `Front.assemble`'s
`symNames`, `Front.buildSpec_spec`).

Not blocking: `try_call` between program functions and to base externs (95 `fv-demo` functions
and every survey crate's landing-pad code pass), `sret` (121 `fv-demo` functions), indirect calls
of `fn` pointers and vtable slots whose signature admits only register-only, non-`sret` callees,
folded aliases outside the program (`BaseOk.aliasSyms`), data objects
(`symbol_value`: in `syms`, their contents are entry premises: the CLIF entry memory), std calls
(base premises), stack-passed and `i128` arguments, direct recursion (one copy, above).

**Trusted** in addition to `backend_correct_program`'s: that `cargo fv` records the file it
passed to `lean-backend` and the allocator answers that run wrote (a different
allocation would only make `checkAlloc` or the binary check fail), the merge's renaming;
`imgMem` is the unrelocated encoding (`bl`, `adrp`, GOT and `lo12` fields are zero), while the
process image has the relocated words: since M9 the crate proofs also prove the executable's
bytes, relocations resolved, and its symbol table against the link map (`bin_ok`, "Binary
level (M9)" below); `native_decide` (Lean's compiler, now also its C backend and the `fvcheck`
shared library Lake links from the same sources, instead of the IR interpreter).

Not done: an entry-level instance for a crate function (the entry premises of `ProgStmt` for
concrete arguments, as `backend_correct_program_witness` does for `f 41`); the witness
(`NonVacuityLink.lean`) keeps its own copy of the checks.

### Binary level (M9)

PLAN.md §4 "M9": a guarantee about the executable file `cargo fv` produces. Each item has its
subsection.

#### Code bytes, data objects, GOT and symbols (items 1–2; 2026-10-05, `agent/bin-bytes`)

**The ELF reader** (`FV/E2E/Elf.lean`, namespace `E2E.Elf`). `cargo fv`'s executables are
static, non-PIE little-endian AArch64 ELF64 files linked by lld against musl (`ET_EXEC`, no
`PT_DYNAMIC`/`PT_INTERP`, no dynamic relocations, a statically filled `.got`). The reader parses
the ELF header (`ehdr`: magic, class, data encoding and entry sizes checked), the program
headers (`phdrs`), section headers (`shdr`) and symbol-table entries (`symEntry`: defined
symbols, name offset in `sh_link`'s string table, value). `loadMem file : BitVec 64 → Option
(BitVec 8)` is the loaded image: the byte of the first `PT_LOAD` segment containing the address
(`p_offset + (a − p_vaddr)` inside `p_filesz`, `0` up to `p_memsz`); `ro file a` (in a segment
without `PF_W`), `relro file a` (in `PT_GNU_RELRO`), `Static file` (`ET_EXEC`, `EM_AARCH64`, no
`PT_DYNAMIC`/`PT_INTERP`, `PT_LOAD` segments in disjoint 64 KiB pages, `p_filesz ≤ p_memsz`),
`SymHas file n v`. Every reader works on a byte source `Rd` and is monotone in it (`*_ext`): a
check evaluated on an **excerpt** `ex` (file ranges; `exRd`) holds for every file with `Agrees
file ex` (its bytes there are the excerpt's), so a proof embeds only the ranges it reads.

**The statements** (`FV/E2E/BinCheck.lean`, namespace `E2E.BinCheck`), for a crate's input `I`,
its data objects `D` and a file:

* `ArtOk I file a`, per compiled function `a` of `tabOf I.results`: every byte of its code is
  `ro`; every word without a relocation is the compiled word (`plain`, as `Arm.read_mem_bytes`
  reads it: `readN (loadMem file) 4`); every relocation is resolved (`RelocOk`): a `bl` is
  `blW (T − P)` (in range) with `T = I.baseOf sym` (an alias's function); an
  `adrp`/`add :lo12:` pair and an `adrp :got:`/`ldr :got_lo12:` pair (consecutive words, the
  compiled words `adrp rd, 0` and `add rd, rd, 0` / `ldr rd, [rd, 0]`) put `T = I.symAddr sym
  addend` into `rd` as the compiled pair with resolved immediates (`PairOk`): `adrp`+`add`, or
  for the GOT `adrp`+`ldr` of a slot `G` whose 8 bytes in `loadMem` are `T` (since
  agent/bin-boundary `cargo fv` links with `--no-relax`, and lld's relaxed `nop`+`adr` is no
  longer accepted: the executable's code is the compiled words); a
  TLSDESC sequence (`adrp`, `ldr`, `add`, `blr`) is lld's local-exec relaxation `movz x0, #hi,
  lsl 16`, `movk x0, #lo`, `nop`, `nop` of the symbol's thread-pointer offset (`TpOff`: its
  `st_value` after the 16-byte TCB aligned to `PT_TLS`'s alignment);
* `DataOk I file o`, per data object: it has a link-map address, `loadMem` holds its resolved
  bytes there (`objBytes`: `%sym+off` items as the 8 little-endian bytes of `I.addrOf sym +
  off`, as `Clif.Image.writeItems` writes them), and a read-only object is `ro` or `relro`;
* `SymsOk I file`: every link-map entry `(n, v)` but the self-call aliases' fresh addresses is a
  defined symbol `symName n` of value `v` (a data object the merge left local, the assembler's
  `.LdataN`, which repeats across codegen units, is named `.LdataN@<unit>`);
* **`BinOk I D file`**: `Static`, `ArtOk` for every function, `DataOk` for every object,
  `SymsOk`.

Consequences for the boundary theorem: `img_bytes` (with `okB I`: every code address of the
image, `ImgT`, is `ro` and holds the image's byte `memT (tabOf I.results) a` unless it is a byte
of a relocated word, `RelocAt I a`, whose form `RelocOk` gives), `roByte_sound`/`dataByte_sound`
(the resolved byte of a read-only / any data object, `roByte I D a` / `dataByte I D a`, is the
loaded byte; read-only ones are `ro` or `relro`). The GOT and symbol-address facts the per-run
premises use (`hsym`, `symOk`: `I.symAddr`) are the link map, which `SymsOk` ties to the file's
symbol table and `PairOk` to what the code computes.

**Checkers** (on an excerpt): `hdrB` (`Static`), `codeB I ex fs` (`ArtOk` for the functions
`fs`, one slice), `dataB`, `symsB I ex cert` (`cert`: each name's symbol-table section and
entry); soundness `hdrB_sound`, `codeB_sound`, `dataB_sound`, `symsB_sound`, assembled by
`binOk_of` (`artsOk_append` over the slices).

**Tooling.** `Front.assemble` (T7d, from `cargo fv link-proof`'s `bundle.json`) gives the data
objects the functions reach (`clif-data-export`'s `; data:` lines of each unit, renamed to the
linked symbols, local ones as `.LdataN@<unit>` with their address from the link map's entry under
the unit's object file; `Front.data_complete`: none reachable is left out) and the addresses of
every name they refer to. `lake exe link-check` reads the executable (`exe`), evaluates the binary checks on the
(pruned) program and the data objects its functions reach, prints what differs (`BIN code`: the
word, the executable's and compiled words, the target; `BIN data`: the byte; `BIN symbol`), the
relocation forms found and a verdict `binary: ok (…)` / `binary: FAIL code=… data=… syms=…
hdr=…`; exit status 0 iff `okB` and the binary checks pass. With `--lean` the generated proof
embeds the excerpts (hexadecimal; ranges within 64 bytes merged): the headers (`exHdr`), per
slice the code and the GOT slots its pairs load (`exK`, `sliceK_bin : codeB input (exHdr ++ exK)
sliceK = true` in the slice's module), the data objects (`exData`), the symbol entries and
names (`exSyms`, `symCert`), and proves `hdr_bin`, `data_bin`, `syms_bin` by `native_decide` and
**`bin_ok (file) (h : Elf.Agrees file exAll) : BinOk input dataObjs file`**. The proof files
state no file name: `link-check` cut the excerpts from the executable named in the header
comment.

**Typed checker** (S11e6, #615). A typed `--verified` executable (`lean-link`'s
`Link.DeadCleanup.compileExeT`) holds functions with float parameters, returns or data movement,
which the integer validators (`staticChksSemanticNI`) reject. With `--dead-cleanup`, when some
functions fail them, `link-check` evaluates the typed validators (`staticChksWithT
DeadCleanup.prune`, those of `okBCleanupT`, which accepts integer functions too) on those
functions' cleanup results (`pipeCleanupOf`); if any passes, the whole program is checked with
the typed checker on `I.resultsCleanup` (`chksWithT`: the typed validators, `linkChks`,
`calleeInt`) and the same binary checks, and it prints `checker: typed (okBCleanupT)`; the
theorem is `E2E.DeadCleanupExecBytes.binary_correct_exec_provenT`
(`binary_correct_exec_peak_provenT` for functions whose calls reach a call cycle), which `cargo
fv`'s verdict names. The integer results are dropped before the typed ones are computed. `--lean`
generates integer crate proofs only. fv-demo, `cargo fv test --lean-link --verified --build-std`
then `link-check --dead-cleanup --prune` on the two test executables' `bin-check` directories:
both pass (27,936 and 28,584 functions, `binary: ok`; 30 each fail the integer validators and pass
the typed ones), where the integer checker alone failed both (`cargo fv`: 0 of 2 verified).

**Typed checker on the Stock route** (#722). When `lean-link --verified` writes a typed
executable with `Link.SemanticCompilerWith.attemptT` (the units hold Stock code, see "The typed
scope" below), the results are the Stock route's (`R0I`, `I.resultsProductionWith lower true`),
not `I.resultsCleanup`. `link-check` then evaluates `staticChksWithTS` (the per-function checks
of `okRWithTS`, `FV/E2E/SemanticPipelineCheckT.lean`): per function either the Stock validator
(`Compile.functionE`, no `sret`, `SemanticNI.check`) or the typed validators on `lowerFunction`'s
output (`lowersToB`: `lowerFunction g = .ok vc` decided; `lowerCheckT`/`lowerCheckTCF`); an `sret`
function is in subset E with `lowerCheck`, or every return of its code is in x0.. (`retsXB`,
`RetsX`). It is used when these accept every function the integer validators reject and the
executable holds `R0I`'s code (`artB`, or `lowersToB` where the Stock lowering fails), and prints
`checker: typed Stock (okRWithTS)`; the theorem is
`E2E.SemanticExecBytes.binary_correct_exec_provenTS` (`…_peak_provenTS` for functions whose calls
reach a call cycle; `FV/E2E/SemanticExecTS.lean`), conclusion `ExecBytes.ExecRefinesT`, which
`cargo fv`'s verdict names. The soundness is `okRWithTS_soundT : PreparedResults → okRWithTS →
OkT` (no lowering equation), with the link contract's artifact field widened in place to
`CompiledAnyTS` (`CompiledAnyT`, or `CompiledStockT`: an integer function without `sret` and the
Stock artifact contract `CompiledSemanticNI`; `FV/E2E/CompiledAnyTS.lean`) and `OkT.sretE` to
"subset E with the integer contract, or `RetsX`". Its link checks are the class-aware
`linkChksTS` (#742, "Program calls by class" below; no "calleeInt" check). `examples/deps`,
`cargo fv test --lean-link --verified` (agent/float-stock1 ab76e3f0): 4 of 4 executables written
by `attemptT` and verified by this checker (15,224, 16,724, 17,130 and 19,901 functions).

**Results** (the ten crates of `crate-proofs/`, rebuilt: survey `cargo fv test --keep-temps`,
`fv-demo` `cargo fv build --keep-temps`; all pass, no difference):

| crate | functions | words | data objects | symbols | `bl` | address pairs | TLSDESC |
| --- | --- | --- | --- | --- | --- | --- | --- |
| AArith | 58 | 1375 | 54 | 126 | 31 | 71 | 0 |
| BSlices | 59 | 2551 | 65 | 137 | 55 | 112 | 0 |
| CStructsEnums | 27 | 854 | 14 | 45 | 17 | 17 | 0 |
| DLoopsIters | 117 | 4424 | 83 | 211 | 130 | 119 | 0 |
| EOptionResult | 48 | 2236 | 26 | 85 | 48 | 32 | 0 |
| FCrypto | 40 | 3509 | 123 | 176 | 80 | 225 | 0 |
| GU128 | 19 | 865 | 38 | 68 | 6 | 68 | 0 |
| HDynGeneric | 43 | 1104 | 21 | 71 | 37 | 32 | 0 |
| IAlloc | 49 | 3082 | 57 | 123 | 56 | 96 | 0 |
| FvDemo | 551 | 24063 | 376 | 996 | 651 | 653 | 2 |

`lake build` of all ten proofs: about 12 s. With `--panic-abort` (the v1 configuration;
`cargo fv link-proof --mode plain-abort`) `g_u128` and `a_arith` pass as well (865 and 1351
words, 38 and 54 data objects). Findings:

1. **lld relaxes every address pair** (without `--no-relax`): all 1425 `adrp`/`add` and GOT
   `adrp`/`ldr` pairs of the ten executables were `nop` + `adr` (target within ±1 MiB), and the
   two TLSDESC sequences are local-exec `movz`/`movk`/`nop`/`nop`. *Since agent/bin-boundary*
   `cargo fv` links with `--no-relax`: every pair is then the compiled GOT `adrp`+`ldr` with
   resolved immediates (1425 pairs, all GOT loads: the backend addresses symbols through the
   GOT), the TLSDESC sequences stay lld's local-exec form (a static executable needs it), and
   `PairOk` accepts only the unrelaxed forms. (Before, with every pair relaxed, the GOT form
   was exercised on a patched copy of GU128's executable: the `.got` slot holding the target
   accepted, the slot altered rejected.) The model's hooks (`ArmStepX`) give `rd` the address at
   the pair's first word, the executable's `adrp`+`ldr` at its second (the boundary's trusted
   hook semantics, "Entry boundary" below).
2. **Data objects without a symbol of their own**: the file-name strings the panic `Location`s
   point to are left local by the merge (`.LdataN`, the same names in every codegen unit; 8
   unresolved names in GU128 alone); now named `.LdataN@<unit>` and resolved per object file.
3. **Self-call alias of a renamed function**: in `fv-demo`'s test executable a recursive
   closure renamed by the merge (`__fv_<tag>_…`) called its alias under the old name
   (`…__fvself`), so `link-check` did not pair them and the self-call was a base call to a
   name without an address (allowed by `okB`; the former image comparison skipped `bl`s to names
   without an address). The binary check reported `bl` to `0x0`; `cargo fv link-proof` now
   renames the alias with its function (0 differences after).
4. Otherwise no mismatch: every word, data byte and symbol agrees; the read-only data objects
   are in `.rodata` (`ro`) or `.data.rel.ro` (`relro`: a `PF_W` segment under `PT_GNU_RELRO`,
   which static musl does not `mprotect`, so "read-only" there is the CLIF semantics', not the
   MMU's).

**Trusted** (here): the OS loads a `Static` file as `loadMem` describes (each `PT_LOAD` at
`p_vaddr`, zero fill), and the excerpts embedded in a proof are the executable's bytes (cut by
`link-check`; a proof about another file needs that file to agree with them); `native_decide`.
The linker, `cargo fv`'s object merge and the link map are no longer trusted for the program's
code, its data objects and symbol addresses.

**Not done here**: the boundary statement that consumes `BinOk` (item 3); data reachable only
from outside code (std's own data) is not checked; the executable's entry point and startup
code are std/musl's.

#### Stack bound (item 4; 2026-10-05, `agent/bin-stack`, `FV/E2E/StackBound.lean`)

`backend_correct_program` gives the entry activation the callees' stack `L.K M = L.D * M`, with
`M` the fuel of the whole-program run, i.e. its **step count**: no fixed stack satisfies
`StackAvail (L.K M)` for every `M`, so at the binary level that premise was unusable. Fix, in two
layers:

1. **The linking induction with a per-function budget** (`FV/E2E/LinkArm.lean`, mechanical): the
   callees' stack of an activation of `g` at depth `M` is `κ M g` for any `κ` with

   ```lean
   def LinkSys.Budget (κ : Nat → Clif.Function → Nat) : Prop :=
     ∀ M, ∀ g ∈ L.P.funcs, ∀ h, L.Callee g h → frameDrop (L.A h).af + κ M h ≤ κ (M + 1) g
   ```

   (the internal `Cond`/`progX`/`X`/`MachEntry`/`WorldEntry`/`Thm` take `κ`; the two uses of
   `K_succ` + `Ok.depth` became `budget_step`). `backend_correct_program_budget` is
   `backend_correct_program` with `κ M f` for `L.K M`; `backend_correct_program` and `_returned`
   are unchanged (`κ := fun M _ => L.K M`, `budget_K`).
2. **A fixed bound where the call graph allows one**: `LinkSys.hybrid c C` (a depth-independent
   budget `c g = some b` for the functions whose calls never reach a call cycle, `L.K M + C` for
   the others) is a budget when the bounded functions call only bounded functions that fit
   (`budget_hybrid`). `backend_correct_program_stack`: for an entry `f` whose budget is `b` at
   every depth, the stack premises become `frameDrop f + b ≤ sp` and "none of those bytes is
   code" (`StackRoom` follows, via `AbiEntry.program` and `Ok.imgAddr`), with `F = frameWG b …`,
   **for every fuel `M`**.

**The budgets** (crate level, namespace `E2E.StackBound`): the call graph `edgeB` over-approximates
`LinkSys.Callee` under `okB` (`edgeB_of_callee`: the functions `g` declares, and when `g` has
indirect calls every function with a CLIF-image address whose signature one of them matches).
`budMap` iterates `B(g) = max over callees h of frameDrop h + B(h)` from "no budget" for as many
rounds as there are functions (`budArr`, stopping early at a fixed point). The proof uses the
budget condition `budOkW` (a function with a budget calls only functions with a budget, whose
frame and budget fit in its own; `budget_of`), which is **proven** for `budMap`'s output, not
checked (L4, 2026-10-06, `agent/stack-complete`; `FV/E2E/StackBound.lean`, "Completeness"):

```lean
def Calls (I : LinkInput) (R : Res) (g h : Clif.Function) : Prop :=   -- the call graph
  h ∈ (progOf R).funcs ∧ edgeB (fun n => I.syms.lookup n) g h = true
def CycleFrom (E : α → α → Prop) (x : α) : Prop :=   -- a cycle is reachable from x
  ∃ h, (h = x ∨ Relation.TransGen E x h) ∧ Relation.TransGen E h h
def budC (I : LinkInput) (R : Res) (g : Clif.Function) : Option Nat := (budMap I R).get? g.name

theorem budOkW_budMap (hn : ((progOf R).funcs.map (·.name)).Nodup) : budOkW I R (budC I R) = true
theorem budC_isSome_iff (hn : …Nodup) (hg : g ∈ (progOf R).funcs) :
    (budC I R g).isSome = true ↔ ¬ CycleFrom (Calls I R) g
theorem goodN_iff (hI : okB I = true) :
    goodN I n = true ↔ ∃ f, (progOf I.results).func? n = some f ∧ ¬ CycleFrom (Calls I I.results) f
theorem stackB_isSome_iff (hI : okB I = true) :
    (stackB I).isSome = true ↔ ∀ f ∈ (progOf I.results).funcs, ¬ CycleFrom (Calls I I.results) f
```

The proof: every round `budPow k` of the iteration meets `budOkW` (a budget computed in round `k`
stays in every later round, `budPow_mono`, and comes from callees that had theirs, `budPow_ok`),
so the early stop does not matter; position `i` has a budget after `k` rounds iff no walk of `k`
calls starts at `i` (`budPow_walk`, `budPow_of_walk`); a reachable cycle gives walks of every
length (`walkN_of_cycle`), and a walk of as many calls as there are functions repeats one
(`cycle_of_walkN`, by `pigeon`). Distinct names (a global check of `okB`, `okB_names`) make the
by-name map agree with the positions (`budC_get`). Frames need not be positive: a function on a
cycle never gets a budget, even when the cycle's frames are 0. `stackR` (the budgets behind a
run-time `budOkW` check) is gone: `budO I g = budC I I.results g`.

```lean
def stackFn (I : LinkInput) (f : Clif.Function) : Nat   -- frameDrop f + bud I f
def stackB (I : LinkInput) : Option Nat                  -- max stackFn; none if recursive
def StackStmt (I : LinkInput) (n : String) : Prop        -- ProgStmt with: stackFn I f ≤ sp, no
                                                          -- code in those bytes, F = frameWG (bud I f) …
theorem crate_correct_stack (hI : okB I = true) (hS : stackB I = some S) (n : String) : StackStmt I n
theorem crate_correct_stackN (hI : okB I = true) (hn : goodN I n = true) : StackStmt I n
theorem stackFn_le (hS : stackB I = some S) (hf : f ∈ (progOf I.results).funcs) : stackFn I f ≤ S
-- from the input condition
theorem crate_correct_stack_acyclic (hI : okB I = true) (hf : (progOf I.results).func? n = some f)
    (hc : ¬ CycleFrom (Calls I I.results) f) : StackStmt I n
theorem crate_correct_stack_all (hI : okB I = true)
    (hc : ∀ f ∈ (progOf I.results).funcs, ¬ CycleFrom (Calls I I.results) f) :
    ∃ S, stackB I = some S ∧ ∀ n, StackStmt I n
```

So the stack premise of the crate and binary theorems is an input condition, not a validator:
the program reaches no call cycle from the entry (`E2E.Binary.binary_correct_of_checks_acyclic`
takes it in place of `goodN`). Recursive functions (a cycle reachable) keep the depth-indexed
theorems (`binary_correct_depth`); that is the scope.

`lake exe link-check` prints the bound (the largest, per entry: the functions no function of the
program calls; or the functions whose calls reach a cycle) and the generated crate proofs evaluate
it (`stack_ok : stackB input = some S`, or for a recursive program `stack_entriesK`) and state
`correct_stack_i : StackStmt input "…"` for the entries (the shared library `fvcheck` of
`crate-proofs` is now built from `FV.E2E.StackBound` and `FV.E2E.BinCheck`, `checkRoots`). Since
L4 these `native_decide` facts check no untrusted output: `stack_ok` holds iff the program has no
reachable call cycle (`stackB_isSome_iff`) and states the number `S`; `stack_entriesK` holds iff no
cycle is reachable from those entries (`goodN_iff`). Both are input conditions that only a
recursive program fails; `decide` cannot replace them (the kernel would have to evaluate the
crate's call graph over its CLIF and, for `S`, the compiler pipeline for the frame sizes).
`link-check` and the generator are unchanged apart from reading `budMap` directly (no "budget
check fails" outcome); the generated files are unchanged (`link-check` on `g_u128` and `a_arith`
reports 160 and 224 bytes as before). The ten crates:

| crate | functions | stack bound (bytes) | largest entries |
| --- | --- | --- | --- |
| AArith | 58 | 224 | `pow_u32` 224, `minmax` 80 |
| BSlices | 59 | 480 | `split_sum` 480, `insertion_sort` 432 |
| CStructsEnums | 27 | 80 | `point_add` 80, `big_make` 64 |
| DLoopsIters | 117 | 576 | `chunks_xor` 576, `dot` 544 |
| EOptionResult | 48 | 352 | `parse_u32` 352, `opt_and_then` 272 |
| FCrypto | 40 | 1120 | `sha256_compress` 1120, `chacha20_block` 592 |
| FvDemo | 551 | recursive (a self-recursive function, `cargo fv`'s `__fvself` alias): the calls of 26 functions reach a cycle; the other 525 have a bound (`correct_stack_*` for them) | |
| GU128 | 19 | 160 | `mac_limbs` 160, `checked_mul_u128` 80 |
| HDynGeneric | 43 | 336 | `total_area` 336, `dyn_pick` 192 |
| IAlloc | 49 | 1696 | `vec_squares` 1696, `boxed` 480 |

The bound is the program's own stack (frames, fp/lr, outgoing areas); calls of code outside the
program (std, the runtime) use stack by their contracts (`BaseOk`), not counted here.

#### Entry boundary (item 3; 2026-10-05, `agent/bin-boundary`, `FV/E2E/Binary.lean`)

The per-run premises of `crate_correct` are restated as a contract on the **real machine state**
`r` in which code outside the program (std's `lang_start`, a fallback function, a callback)
enters a function `f` of the program, plus the choice of the reference CLIF run; every premise the
binary determines is discharged, from the checks of items 1, 2 and 4.

```lean
-- E2E.Binary; prog I / art I f / img I / imgMem I: LinkSys.ofInput's P / A f / Img / imgMem;
-- sys I B := LinkSys.ofInput I B (fun _ => False) (its machine and `P` do not depend on `F`)
noncomputable def modelOf (I) (f) (r) : Arm.ArmState  -- r, program := f's compiled words,
                                                      -- mem on img I := imgMem I
structure OutsideCall (I) (roB : BitVec 64 → Option (BitVec 8)) (f) (N : Nat) (r) (args) (cm) where
  pc : Arm.r .PC r = (art I f).base                    -- f's link-map address
  err : Arm.r .ERR r = .None
  ra : ¬ img I (xreg 30 r)                             -- the caller is outside the program's code
  spAligned : (spv r).toNat % 16 = 0
  stack : N ≤ (spv r).toNat                            -- N bytes of stack below sp
  stackFree : ∀ a, img I a → ¬ StackBelow N (spv r) a  -- none of them is code
  args : ArgsOut (img I) f.sig args r                  -- AAPCS64 locations; stack args not code
  bytes : ∀ a b, cm.valid a 1 → cm.bytes a = some b → roB a = none → read_mem a r = b
  image : ∀ a b b', cm.valid a 1 → cm.bytes a = some b → roB a = some b' → b = b'
  valid : ∀ a n, cm.valid a n → a + n ≤ 2^64 ∧ ∀ k < n, ¬ img I (a+k) ∧
    (StackBelow N (spv r) (a+k) → SlotArea (art I f).af r (a+k))
  symbols : cm.symbols = fun n => I.syms.lookup n
structure ClifRun (I) (B) (f) (r) (args) (cs) where    -- the reference CLIF run (a choice)
  entry : ClifEntry f args cs
  slots : SlotRel f ((spBody af r).toNat + af.slotBase) cs.frame.slots
  place : (sys I B).NeedSlots → (sys I B).PlaceAt cs.mem (spBody af r)

structure Image where mem : BitVec 64 → Option (BitVec 8); kept : BitVec 64 → Prop
def Image.Intact (X : Image) (r) : Prop := ∀ a b, X.kept a → X.mem a = some b → r.mem a = b
def imageOf (file : ByteArray) : Image := ⟨Elf.loadMem file, fun a => Elf.ro file a ∨ Elf.relro file a⟩
structure BinFacts (I) (X : Image) (R : BitVec 64 → Prop) (roB) where
  ok : okB I = true
  code : ∀ a, img I a → X.kept a ∧ (X.mem a = some (imgMem I a) ∨ R a)
  data : ∀ a b, roB a = some b → X.kept a ∧ X.mem a = some b
theorem binFacts_of_checks (hI : okB I = true) (hB : BinCheck.BinOk I D file) :
    BinFacts I (imageOf file) (BinCheck.RelocAt I) (BinCheck.roByte I D)

theorem binary_correct_of_checks (hI : okB I = true) (hbin : BinCheck.BinOk I D file)
    (B) (hB : BaseOk (sys I B)) (hn : StackBound.goodN I n = true)
    (hf : (prog I).func? n = some f) (M : Nat) (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → BinCheck.RelocAt I a
-- the same over abstract facts, and its variants:
theorem binary_correct (hbin : BinFacts I X R roB) (B) (hB) (hn : StackBound.goodN I n = true)
    (hf) (M) (hX : X.Intact r) (ho : OutsideCall I roB f (StackBound.stackFn I f) r args cs.mem)
    (hr) (htr) : ArmRefines … (modelOf I f r) (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
      ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a
theorem binary_correct_bound (hbin : BinFacts I X R roB) (hS : StackBound.stackB I = some S) …
    (ho : OutsideCall I roB f S r args cs.mem) …     -- every function of a non-recursive program
theorem binary_correct_depth (hI : okB I = true) (B) (hB) (hf) (M : Nat)
    (ho : OutsideCall I (fun _ => none) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr) (htr) : ArmRefines … (modelOf I f r) (Clif.runLoop B.env (prog I) (M + 1) cs)
theorem trapsExplicit_of_run (hL : L.Ok) (hf : f ∈ L.P.funcs) (hcs : ClifEntry f args cs)
    (hsym : cs.mem.symbols = L.syms)
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only f) cs
```

In words: for an executable file that passes the binary checks against a crate input that passes
the crate checker, whenever outside code calls a Lean-compiled function `f` of it whose calls
reach no call cycle, meeting the boundary contract with `stackFn I f` bytes of stack, in a machine
state that holds the file's read-only bytes, the linked machine (at every depth `M`) from that
state refines the whole-program CLIF run of at most `M + 1` steps — returning to the caller's
return address with the CLIF results and memory, or stopping at the CLIF trap's site — and the
state the machine runs from differs from the real one only at the bytes of relocated
instructions. `binary_correct` goes through `StackBound.crate_correct_stackN`;
`binary_correct_depth` through `crate_correct` (the stack grows with the depth: the statement for
functions on call cycles, as in CompCert). A returning run needs no `TrapsExplicit`
(`trapsExplicit_of_run`).

**The model state.** The model machine (`L.mach M f`, `ArmStepX`) fetches instructions from
`s.program` and runs `bl`, `blr`, the address pairs (`adrp`+`add`, the GOT `adrp`+`ldr`) and the
TLSDESC sequence through hooks: a pair puts the symbol's link-map address (`Xb.sym`) into `rd`.
The compiled image (`imgMem`, `fb.words`) holds those instructions with zero relocation fields.
`modelOf I f r` is `r` with the program `f`'s words and the program's code bytes the compiled
image. The second conjunct: it differs from `r` only at the relocated instruction bytes
(`RelocAt`), and there the executable holds the compiled instruction with its immediates resolved
(`BinCheck.RelocOk`: `bl` to the callee's address; `adrp`+`ldr` of a GOT slot holding the symbol's
address, `adrp`+`add` of the address; `cargo fv` links with lld's `--no-relax`, which keeps the
pairs as emitted, and `PairOk` accepts no other form) — except TLSDESC sequences, which lld
rewrites to local-exec `movz`/`movk`/`nop`/`nop` in a static executable.

**Each premise of `backend_correct_program`:**

| Premise | Status | By |
| --- | --- | --- |
| `L.Ok` | discharged | `okB I = true` (`okB_sound`) except `BaseOk` |
| `BaseOk` (contracts of std, other crates, the runtime) | **premise** | not about the program |
| `AbiEntry.program`, `.code`, `.fits` | discharged | `modelOf` (program, code bytes), `Ok.imgCode`, `Ok.fits`; the file's code bytes: `BinFacts.code` |
| `AbiEntry.pc`, `.err`, `.spAligned` | `OutsideCall` | the call (AAPCS64) |
| `AbiEntry.lr` | discharged | `ra := xreg 30 r` |
| `AbiEntry.raOutside` | `OutsideCall.ra` (weaker form) | the return address is outside the program's code |
| `StackAvail`, `hgfree` | `OutsideCall.stack`/`stackFree` with `N` | `N = stackFn I f` (`binary_correct`, `goodN`; `binary_correct_of_checks_acyclic`: the input condition "no call cycle reachable from `f`", `StackBound.goodN_iff`), `S` (`binary_correct_bound`), `frameDrop + D·M` (`binary_correct_depth`; with read-only data and `RunGoodL`: `binary_correct_depthX`, up to the executable `compileExe_correct_depth`), `frameDrop + D·d` for the run's peak call depth `d` (`binary_correct_peakX`, up to `compileExe_correct_peak`) |
| `hF` (addresses outside the world) | discharged | `F := worldF I f K r` (`K = bud I f` / `D·M`) |
| `himg` | discharged | `modelOf`; `RelocAt` relates it to the file |
| `BodyEntry` | discharged | the body-entry world is `bodyOf af s` |
| `ArgsIn`, `StackArgsAvoid` | `OutsideCall.args` | stated on `r`; `noCode` from "not program code" |
| `ClifEntry` | `ClifRun.entry` | the reference run |
| `Rel.holds`: `MemRel.bytes` | `OutsideCall.bytes` + `.image` | the read-only CLIF data objects' bytes: `BinFacts.data` + `Image.Intact` (the caller only states that its CLIF memory holds the image there, a CLIF-level fact) |
| `Rel.holds`: `MemRel.valid` | `OutsideCall.valid` | live CLIF bytes not code, in the free stack only in `f`'s slot region |
| `Rel.holds`: `MemRel.symbols` | `OutsideCall.symbols` | the CLIF image's symbol table (`SymsOk` ties the link map to the file's symbols) |
| `Rel.holds`: `SlotRel` | `ClifRun.slots` | CLIF leaves slot addresses unspecified |
| `Rel.holds`: `OutRel` | discharged | the outgoing area is free stack below the slot region |
| `hpl` | `ClifRun.place` | as `SlotRel` (vacuous without slotted program callees) |
| `TrapsExplicit` | **premise** | about the CLIF run (no memory-access traps); none for returning runs |

**Trusted for the binary statement** (besides the M8 list and items 1–2's ELF loading):

* the loader premise `Image.Intact`: the machine state holds the file's bytes at the read-only
  segments and the relocation-read-only data (`PT_GNU_RELRO`, which static musl does not
  `mprotect`: outside code must not write it);
* the hook semantics of the model machine (`ArmStepX`), now applied to checked inputs: a GOT
  `adrp`+`ldr` pair with resolved immediates loads the symbol's address, provided the GOT slot
  (checked in the file: `PairOk`) is unchanged during the run — Lean code stores only into
  writable CLIF allocations and its frames, so no writable CLIF allocation may contain a GOT slot
  and outside code must not write one; the address is in `rd` one instruction later than in the
  model, and no branch target lies between a pair's words (the compiled code branches to labels
  only, and the emitter puts each pair in two consecutive instruction lines, which `PairOk` reads
  at `P` and `P + 4`); the TLSDESC hook (`TlsOk`, a `BaseOk` contract) covers lld's local-exec
  rewrite (on the executable, `binary_correct_exec_proven_tls` runs the rewritten words instead,
  see "`tls_value`");
* `--panic-abort` for the v1 configuration (no unwinding through Lean frames).

**Non-vacuity** (`crate-proofs/Crates/BinaryWitness.lean`): on the `a_arith` test executable
built with `cargo fv test -p a_arith --panic-abort` (proof `Crates.AArithAbort`, 58 functions,
binary ok, stack 224 bytes), `binary_witness`: some file holds the proof's excerpts
(`agrees_fileOf`), and for every such file (the executable is one) the machine state whose
memory is the file's loaded image, in which outside code calls the Lean-compiled
`core::num::<i32>::wrapping_add` with `2`, `3` and `stackFn` bytes of stack, meets every premise
of `binary_correct_of_checks_acyclic` (`bin_ok`, `okB_input`, the stack condition `acyclic`: no
call cycle reachable from the entry, from `goodN` by `goodN_iff`; `Image.Intact`, `OutsideCall`,
`ClifRun`, `BaseOk` of the closed base, `TrapsExplicit` from the returning run); the CLIF run
returns `5` and the theorem gives the machine's return to the caller with `5` in x0.
`binary_depth_witness`: the same for `binary_correct_depth`.

**`cargo fv build`/`test`** (`rust/crates/cargo-fv/src/bincheck.rs`): after the build, every
linked executable with Lean-compiled code goes through `cargo fv link-proof` (into
`target/fv/<mode>/bin-check/`) and `link-check --prune`, and the verdict is printed: `verified:
E2E.Binary.binary_correct holds for its N Lean-compiled functions; stack: …` (with
`binary_correct_depth` for functions on call cycles), or `not verified: …` with the failing check
(the binary check's `FAIL` line and first detail, or the first function failing `LinkSys.Ok`).
The build keeps link-proof's inputs for it (objects removed); `--no-binary-check` turns it off.
The 18 executables of `examples/survey` and `fv-demo`'s are verified (fv-demo: 26 functions on
call cycles).

#### The executable's own words (item 1b, TO-PROVE L3; 2026-10-06, `agent/exec-bytes`, `FV/E2E/ExecBytes.lean`, `FV/E2E/ExecWords.lean`)

`binary_correct_of_checks` is about the hooked model machine `(sys I B).mach M f` run from
`modelOf I f r`. **`E2E.ExecBytes.binary_correct_exec`** (and `binary_correct_exec_of_good`, the
`goodN` form) moves the conclusion to the **executable machine** `step I B file` run from the
machine state `r` itself:

* `step` fetches the 32-bit word at the pc **from the executable file** (`fileWord`: `readN
  (Elf.loadMem file) 4 pc`, the read-only text), decodes it with the Arm model's decoder and runs it
  (`realStep`, `Arm.exec_inst`). This covers every word of the program, including the resolved
  `adrp`+`add`, the GOT `adrp`+`ldr` and `bl`/`blr` of functions of the program: the callee's words
  run in the same machine. Calls of code **outside the program** (`bl` of a name that is no function
  of the program, `blr` whose target is none) and the TLSDESC site (its `adrp`, then `Hb.tls` at its
  `ldr`) use the base environment's hooks, as in the model: code outside the program is given by
  its contract. `siteAt` only decides these cases: the kind of site at the pc (`Site`, `siteOf`
  of the program's instruction there: a real word, a call of the program, a call outside it, a
  `blr`, the TLSDESC `adrp` or `ldr`), so that code two functions share (`cargo fv`'s self-call
  alias) has one kind at each word. `step` never reads the state's program field.
* Conclusion `ExecRefines … (step I B file) r (RelocAt I)`: `ArmRefines` (return to `x30` with
  `ArmRet`, results in their registers; or `TrapAt` the trap site), with the live CLIF bytes
  compared outside the relocated instruction bytes `RelocAt I` (code bytes).
* **Word adequacy** (`ExecWords`, proven against the decoder): `adrpW_exec` (`rd := page(pc) +
  dp·4096`), `addW_exec`, `ldrW_exec`, `blW_exec` (`x30 := pc + 4`, `pc := pc + d`), `blr_exec`;
  `adrp_add_val` / `adrp_ldr_addr`: the words `BinCheck.PairOk` accepts put `T` (resp. the slot
  address `G`) in the register. `BinCheck.RelocOk`'s pair case now also checks the register is not
  31 (`rd < 31`; `xzr`/`sp` would change the meaning of the words).
* **Simulation** (`Sim`: the same registers, pc, flags and error, the same bytes outside
  `RelocAt I`; the program field is not compared). `pair_step`: the model's two steps at a pair
  (register `T` after the `adrp`, nothing at the second word) against the executable's two words
  (`page(T)`/`page(G)` after the first, `T` after the second); `plain_step`: a word without
  relocation is the compiled word (`fileWord_plain`, `ArtOk.plain`), the same `exec_inst` on both
  sides; `call_enter`: the real `bl` (`R_AARCH64_CALL26`, target `I.baseOf`) / `blr` enters the
  callee in `enterAt`'s state; `hook_step`: outside calls and TLS. `act_sim` (induction on the
  depth, inside on the run length; `act_core`): every state of a model activation before its
  return that is not a pair's second word is simulated by a state of the executable's run; a
  linked call is the callee's activation up to its first return (`RetOf`, `firstNat`).
* **Static control flow, proven for every input** (no per-crate check): `not_second_base` (an
  entry is no second word), `first_not_second`, `second_of_lo12` (an `add`/`ldr` of a pair is at a
  second word), `adrp_lands` (the model's `adrp` step lands on the second word), `ret_not_second`
  (the return address of a call is no second word of the callee: its first word would be the call's
  word).
* **The hypothesis `RunOk I B file M f (modelOf I f r)`**: `StepOk` at every state of the model's
  run before its return, nested into the linked calls (`Reach`). `StepOk M g m` holds per state:
  `err` (no error), `program` (the program field is `g`'s), `site` (the pc is at an instruction of
  `g`, `siteAt` gives its kind, not inside the TLS sequence past its `ldr`), `cf` (D1: a step landing on a
  pair's second word starts at its first word), `insn`/`call`/`tls` (D2: the instruction, outside
  call or TLS hook at `m` reads no relocated instruction byte and not the program field: `Sim`
  before gives `Sim` after), `got` (D4: at the `ldr` of a GOT pair the slot's 8 bytes are the
  file's and no relocated byte), `blr` (a `blr` to the program: not `xzr`, the model reads the
  file's word, the callee's link-map address is its load address), `plain` (an instruction word
  without relocation is no relocated byte of another function). The M6 proof establishes these
  of its runs (`RL.Good` for every intermediate state, `StRel.code`, `StRel.gkeep`, `StRel.prog`);
  `binary_correct_exec_proven` (below) exports them: no per-state hypothesis remains (TO-PROVE L3).
* Trusted-hook items of PLAN.md M9 "One gap remains": (1) the hooked GOT pair computes what the
  real words compute — **proven** (`pair_step`; the slot's value at the `ldr`, `RunOk.got`, D4,
  is proven in `binary_correct_exec_proven` from the check `gotB` and the contract
  `OutsideAvoids`); (2) the register written one word later — **proven** (`Sim` after the pair,
  the intermediate state is never compared); (3) no branch between a pair's words — reduced to
  the per-state `RunOk.cf` (D1; entries and return addresses are proven), **proven** in
  `binary_correct_exec_of_reads` (`GoodX.next`, `emitFunc_pairsClosed`); (4) the TLS local-exec
  rewrite — the hook in `step` (the TLS site by `Hb.tls`); **proven** for the hook-free machine
  `stepT` (`binary_correct_exec_proven_tls`, T1: the six local-exec words on the processor, under
  the loader's thread-pointer contract `TlsLoader`; see "`tls_value`").
* Axioms (`#print axioms E2E.ExecBytes.binary_correct_exec`): `propext`, `Classical.choice`,
  `Quot.sound` (every fixed backend lemma is kernel-checked, T6). `act_sim` and the `ExecWords`
  lemmas: only the first three.
* **Non-vacuity** (`crate-proofs/Crates/BinaryExecWitness.lean`,
  `Crates.BinaryExecWitness.binary_correct_exec_witness`): on the `a_arith` executable of
  `binary_witness`, for every file holding the proof's excerpts (one exists), the call of the
  Lean-compiled `core::num::<i32>::wrapping_add` with `2` and `3` meets every premise of
  `binary_correct_exec`, **`RunOk` included**, and the executable machine returns to the caller
  with `5` in x0. `RunOk` is proven by computing the model's run (`stp x29, x30, [sp, #-16]!`;
  `mov x29, sp`; `add w0, w0, w1`; `ldp x29, x30, [sp], #16`; `ret`: states `S1`…`S5`, the
  activation returns at `S5`, `returned_S5`) and `StepOk` at each state before the return
  (`run_facts`, `runOk_entry`, at every depth and base environment): no call, no relocation in
  the entry, the word at the pc is the encoded word (`stepOk_plain`, any input: an unhooked
  instruction of a function without relocations), and each instruction preserves `Sim`
  (`sim_stp`/`sim_mov`/`sim_add`/`sim_ldp`/`sim_ret`; the `ldp` reads the stack above `2^32`, every
  relocated byte of the program is below it and away from the entry's code: `codeB`, decided on the
  executable's data like the other per-crate facts). Axioms: the three and generated `_native`
  certificates (the crate's `native_decide` evaluations, as `binary_witness`).
* **The static part of `RunOk`** (`FV/E2E/ExecStatic.lean`, `binary_correct_exec_static`): the
  facts of `StepOk` that do not depend on the run are proven for every input: the site lookup's
  agreement (`siteAt_static`) and `plain` (`plain_static`) from the per-program check `codeMapB`
  (`FV/E2E/CodeMap.lean`; a premise, not part of `okB`; `codeMap_sound`, `line_overlap`: two
  functions' overlapping words are alike lines, so they have one kind of site and the same
  relocation status) and the layout (a relocation sits at its own instruction line); `call` and
  `tls` from the **outside-code contract
  `HooksSim I B`** (next to `BaseOk`: the hooks for calls outside the program and for the TLS
  sequence give `Sim`-related results on `Sim`-related states, i.e. they read no relocated
  instruction byte and not the program field; `hooksSim_closed`). What remains per state is
  `RunOkD`/`StepOkD`: no error, the program field, the pc at an instruction (not past a TLSDESC
  `ldr`), D1 `cf`, D2 `insn`, D4 `got`, and at a `blr` to the program the register (not `xzr`),
  the model's read of its word and the callee's link-map address (`StepOk.d`: `StepOk` gives it). `binary_correct_exec_static` is
  `binary_correct_exec` under `codeMapB`, `HooksSim` and `RunOkD`; non-vacuity (`codeMap_ok` by
  `native_decide`):
  `Crates.BinaryExecWitness.binary_correct_exec_static_witness`.
* **D2 from the memory reads** (`FV/E2E/ExecFrame.lean`, `FV/E2E/ExecFrameSim.lean`,
  `agent/exec-frame`): `exec_sim a h hR : Sim I (exec_inst a m) (exec_inst a e)` for every decoded
  instruction `a`, given `Sim I m e` and that the byte ranges `MemReads a m` avoid `RelocAt I`.
  `MemReads` lists the bytes a load reads (single-register loads in every addressing mode, GPR and
  SIMD&FP, `ldp`, the exclusive / acquire loads); it is empty for every other instruction, stores
  included. Proven over any byte set (`ExecFrame.exec_simR`) from the semantics alone, so it
  covers every `Insn` the backend emits and the relocated words. `insn_of_memReads` gives
  `StepOkD.insn` from "the reads of the word at the pc avoid `RelocAt I`"; the M6 export proves
  that fact (`insn_of_good`, below).
* **`RunOkD` from the M6 proof** (TO-PROVE L3 (c) stage 3b; 2026-10-06, `agent/exec-good`;
  `FV/E2E/RegLevelGoodX.lean`, `FV/E2E/PairLines.lean`, `FV/E2E/LinkWorldX.lean`,
  `FV/E2E/LinkGood.lean`, `FV/E2E/BinaryGood.lean`, `FV/E2E/ExecRunN.lean`,
  `FV/E2E/ExecGoodRun.lean`, `FV/E2E/ExecReads.lean`, `FV/E2E/RegLevelOpReads.lean`,
  `FV/E2E/MoveReads.lean`, `FV/E2E/ExecGoodReads.lean`, `FV/E2E/ExecGot.lean`,
  `FV/E2E/ExecProven.lean`):
  - `RL.GoodX R u`, proven at every state of an activation's run before its return: `Good`, no
    error, the program, the pc at an instruction line not past a TLSDESC `ldr` (`Insn.tlsTail`),
    D1 `next` (`RL.NextOk`: the next state errs, or its pc is the entry's `x30`, or pc + 4, or a
    line not after an `adrp` pair's first word), `got` (at a GOT `ldr` the kept addresses `R.G`
    hold the entry's bytes), `blr` (not `xzr` when the VCode's register calls are through int
    vregs, `VCode.DestsInt`; the code words readable), `call` (`RL.CallPre`: the callee
    contract's premise at a `bl`/`blr`), `reads` (D2, `RL.ReadsAt`: every `MemReads` byte of the
    line's instruction at `u` is outside `R.G` or in a `.word` line of the function, `RL.ReadOk`).
    Every `realizes_*` case proves it for its segment
    (`RegLevelMove` via the `GoodX` file, Op, Branch, Goto, Next, Call, Tls, Try, JT, Atomic,
    Trap, Frame); the entry state in `q_init`, the `ret` state in `ret_machine`; at a trap the
    trace, and the machine errs for ever after the `udf`. `regLevelCorrect_world_atX` /
    `regLevelCorrect_worldX` export it (`actGoodX`).
  - `emitFunc_pairsClosed`: in the emitted lines every second word of an `adrp` pair
    immediately follows its first word (`PairsClosed`).
  - Export through the linking proof: `backend_correct_worldX`, `backend_correct_world_niX`;
    `RetL`, `LinkSys.ReachL` (the states of the activation and of the nested activations entered
    through calls whose step ends without error), `LinkSys.GoodAt`, `LinkSys.RunGoodL`,
    `LinkSys.ThmG`/`ThmX`/`thmX` (induction on the depth; a nested activation through
    `LinkSys.callGood`: `CallPre` at a call state gives the callee's `RunGoodL`),
    `backend_correct_program_budgetX` (`ArmRefines` ∧ `RunGoodL` for a returning or trapping
    run), `backend_correct_program_stackX`, `StackBound.crate_correct_stackNX`,
    `Binary.binary_correctX`, `Binary.binary_correct_of_checksX`.
  - `ReachN`/`RunOkN`: `StepOkD` only at the states whose step ends without error, nested
    activations only through calls whose step ends without error (`act_coreN`,
    `exec_of_modelN`, `binary_correct_exec_staticN`; `RunOkD.n : RunOkD → RunOkN`).
    `StepOkR` holds `StepOkD`'s `insn` (D2) and `got` (D4); `RunReadsN` is `StepOkR` at the
    states of `ReachN` whose step ends without error. `runOkN_of_good`: `RunGoodL` +
    `RunReadsN` + the checks + `codeMapB` + `x30` outside the code ⇒ `RunOkN` (the site from `line`; `cf`
    from `next`, `PairsClosed` and the entry's `x30` being no second word: `raOutside` at the
    top, the call's address when nested; `blr` from `GoodX`, `LinkSys.Ok.blrRegs` and, for the
    callee's link-map address, `GoodAt`'s `BlrAt` with `codeMapB`).
  - Intermediate: **`E2E.ExecBytes.binary_correct_exec_of_reads`**: `binary_correct_exec_static`'s
    premises (those of `binary_correct_of_checks_acyclic`, `codeMapB`, `HooksSim`) with only
    `RunReadsN` in place of `RunOkD`; witness
    `Crates.BinaryExecWitness.binary_correct_exec_of_reads_witness`.
  - **D2** (`StepOkR.insn`): `GoodX.reads` in every case: Op loads via `formOk_reads` (csem's
    `AccessOk`, per addressing mode, through `memFinalize`'s x16), spill moves via
    `moveInsts_reads` (the frame's slot area, which `G` avoids: `RL.G_not_slot`), the JT `ldrsw`
    (data words), atomics (`Avoids F`), the epilogue `ldp` (fp/lr slot, `gfree`);
    `Insn.memReads_nil` for the non-loads. At the link level `insn_of_good`: `RelocAt ⊆ Img ⊆ G`
    (`relocAt_img`) and data words carry no relocation (`word_static`), so `insn_of_memReads`
    applies. `binary_correct_exec_of_got`: only the D4 hypothesis `RunGotN` left.
  - **D4** (`StepOkR.got`): `GotSlot I file` (the 8 bytes of the slot each GOT pair's file words
    address, in the checked pair form: `rd < 31`, `G` aligned, the page in range), checked by
    `gotB` (on an excerpt; `gotB_sound` → `GotOk`: loaded, `ro`/`relro`, not `RelocAt`). Every
    activation keeps the slots: `LinkSys.extImg` extends the code image by them (the same
    machine); `GoodAt` carries `Img ⊆ G` and the entry's image bytes. The outside caller's
    premise **`OutsideAvoids`**: the slots are outside its free stack, the stack arguments and
    the live CLIF memory (what `OutsideCall` states for the code image). `got_of_good` gives the
    clause (`GoodX.got`, `GotOk`, `img_bytes`, `Image.Intact`). `StepOk`/`StepOkD`/`StepOkR.got`
    now assume the checked pair form: for every `G` the clause was unprovable (the `adrp`
    immediate aliases `G + k·2^33`). `binary_correct_exec_of_insn`: only the D2 hypothesis
    `RunInsnN` left.
  - **`E2E.ExecBytes.binary_correct_exec_proven`** (`FV/E2E/ExecProven.lean`): under the premises
    of `binary_correct_of_checks_acyclic`, `codeMapB`, `HooksSim`, `GotOk I file` (decidable:
    `gotB`) and `OutsideAvoids (GotSlot I file) …`, with **no per-state hypothesis**, `ExecRefines
    … (step I B file) r (RelocAt I) (Clif.runLoop …)`. Axioms: `propext`, `Classical.choice`,
    `Quot.sound` (T6). Non-vacuity:
    `Crates.BinaryExecWitness.binary_correct_exec_proven_witness` (`a_arith`'s `wrapping_add`;
    no GOT pair, `noGotPair`, so no slot).
  - **Aliases** (TO-PROVE L3 item 6; 2026-10-06, `agent/exec-alias`): `cargo fv`'s self-call
    alias `f__fvself` is a function of the program on `f`'s code (the same load address; `f`'s
    self-call is `bl f__fvself`, the alias's `bl f`) with a fresh link-map address. `codeMapB`
    (`FV/E2E/CodeMap.lean`) now accepts it: (i) two functions' code ranges are disjoint **or** they
    have the same load address and lines alike line by line (`linesAlikeB`: equal instructions,
    or `bl`s of functions of the program; data words; labels), so at every word of code the kind
    of site (`siteOf`) and the relocation status are those of every function there
    (`line_overlap`); (ii) a function's link-map address is its load address **or** no `blr` of
    the program enters it (`noBlrB`: the name is no CLIF image symbol, and every function
    declaring it calls through registers only through the GOT entries of other symbols,
    `blrGotB`/`gotOf`). For (ii) `LinkSys.GoodAt` carries `BlrAt` (at a `blr` the callee is one
    `g` may enter through the call's register, `BlrTo`; `blrTo_of_pre`, from `RL.CallPre`'s call
    through `L.X`), and `symAddr_of_blrTo` gives the callee's link-map address = load address;
    that fact moved from `codeMap_sound` into `StepOkD.blr` (`stepOkD_of_good`).
    `ret_not_second(N)`/`raNotSecond_enter` compare kinds of site (a call is `progCall`/`blr`, a
    pair's first word `real`, `siteOf_pairFirst`). `binary_correct_exec_proven` is unchanged.
    `fv-demo` (`crate-proofs/Crates/FvDemoExec.lean`): `codeMap_ok`, `gotB_ok` by `native_decide`
    (`codeMapB` in `fvcheck`), and `Crates.FvDemo.binary_correct_exec`: the theorem for every
    file agreeing with the excerpts, only the base environment's and the outside caller's
    premises left. `link-check` prints the code map check (`code map: ok`).


### Non-vacuity (2026-10-02, `agent/callee-fix`, `FV/E2E/NonVacuity.lean`)

A premise set that cannot hold makes a theorem say nothing. The contract premises on the
machine's hooks and the external semantics are the ones that cannot be checked per function, so
they are witnessed by a concrete, realistic callee:

* `framed g body` — `bl g` and the function at `g` as the Arm model runs it: our backend's frame
  code for an empty frame, `prologueLines 0` (`stp x29, x30, [sp, #-16]!; mov x29, sp`), `body`,
  `epilogueLines 0` (`ldp x29, x30, [sp], #16; ret`), each instruction executed by
  `Arm.exec_inst` of its encoding. `framed_spec`: with a body of stack budget `K` (`KeepsBut K`:
  every field but the pc and x30, the program and the memory outside the `K` bytes below `sp`
  kept) it has budget `K + 16`, returns to `pc + 4`, and leaves `pc + 4` and the caller's fp in
  the 16 bytes below `sp`.
* `witnessHooks g h sym tp`: every call runs `witnessCall g h := framed g (framed h id)` (a
  function that calls a leaf; two frames pushed), the TLSDESC hook is the static resolver's
  effect. `witness_saves_lr`: `read_mem_bytes 16 (sp - 16) (witnessCall g h s) = (pc + 4) ++ x29`
  — exactly the callee the former contract excluded.
* `witnessX sym tp`: every callee returns nothing and keeps the world.

```lean
theorem calleeOk_witness (F : BitVec 64 → Prop) {K : Nat} (hK : 32 ≤ K) (S : CallInfo → Prop)
    (g h : BitVec 64) (sym : String → Int → BitVec 64) (tp : BitVec 64) :
    CalleeOk F K (witnessX sym tp) (witnessHooks g h sym tp) S
theorem final_contracts_witness … (hK : 32 ≤ K) (g h tp : BitVec 64)
    (hsig : ∀ ext ∈ f.externs.map (·.2), sigRets ext.sig = [] ∧ ext.sig.returns = [])
    (hisig : ∀ sig ∈ indSigs f, sigRets sig = [] ∧ sig.returns = [])
    (hnoop : ∀ ext ∈ f.externs.map (·.2), ∀ G, env.extern ext.name = some G →
      ∀ vals cm rvals cm', G vals cm = .returned rvals cm' → cm' = cm)
    (hnoopI : ∀ sig ∈ indSigs f, ∀ n G, env.extern n = some G → ∀ vals cm rvals cm',
      G vals cm = .returned rvals cm' → cm' = cm) :
    (∀ s, CalleeOk (FF s) K X H vcp.CallSite) ∧ (∀ s, TlsOk (FF s) K X H) ∧
    (∀ s, XCallsOk env (f.externs.map (·.2)) (Rel.holds ⟨FF s, syms, slotOff, OB⟩ f) X) ∧
    (∀ s, XCallsIndOk env (indSigs f) (Rel.holds ⟨FF s, syms, slotOff, OB⟩ f) X) ∧
    (∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
  -- X := witnessX (witnessSym syms) tp, H := witnessHooks g h (witnessSym syms) tp
theorem backend_correct_final_witness (hsub) (hc) (hK : 32 ≤ K) (g h tp) (hcov)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false) (hsig) (hisig) (hnoop) (hnoopI) (hslot)
    (hent) (hres : StackAvail K af s) (hbe) (hargs) (hcs) (hrel) (htr) (fuel) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)
```

Witnesses per top-level theorem (the run premises `AbiEntry`, `StackAvail K`, `BodyEntry`,
`ArgsIn`, `ClifEntry`, `Rel.holds`, `TrapsExplicit` are facts of a concrete run; they were
satisfiable before and only gained "no live CLIF byte and no code in the `K` bytes below the
body's `sp`"):

| Theorem | Contract premises | Witness |
| --- | --- | --- |
| `backend_correct_final` | `hC`, `hCT`, `hTls`, `hX`, `hXI`, `hsym` | `final_contracts_witness` (`hC`, `hTls`, `hX`, `hXI`, `hsym`, for a function whose externs and indirect-call signatures return nothing, in an environment whose externs keep the memory when they return (those `f` declares; all of them if it has an indirect call); `CalleeOk` itself holds for every set of call sites); `final_contracts_id` (callees returning a value, call sites `IdSite`); `hCT`: vacuous without `try_call`, `calleeTryOk_witness` at `try_call` sites whose callee returns nothing; `backend_correct_final_witness`/`backend_correct_final_id`/`backend_correct_final_try_witness` are the theorem with all of them discharged |
| `backend_correct_opt_proven` | `hC`, `hTls`, `hX`, `hsym` (for the optimised function; `try_call` and `call_indirect` excluded by premises) | `final_contracts_witness` at `f := Opt.optimize f cfg` |
| `backend_correct_legal` | `hC`, `hCT`, `hTls`, `hX`, `hXI`, `hsym` (for the legalised `g`, environment `Clif.Rust.env`) | `final_contracts_witness` at `f := g`, `env := Clif.Rust.env`, for functions without indirect calls whose externs are the diverging panic entry points (they never return, so `hnoop` holds) |
| `backend_correct_linked` | `hC`, `hCT`, `hTls`, `hX` (environment `Clif.linkEnv P base`); `hXI` discharged by `Linkable` | `final_contracts_witness` at `env := Clif.linkEnv P base`, when the program callees and the base externs return nothing and keep the memory |
| `backend_correct_program` | `L.Ok` (program, compilation, layout, base environment) and the entry premises | `E2E.LinkWitness.backend_correct_program_witness` (`FV/E2E/NonVacuityLink.lean`): `P = {f, g, h, s, k, r, r__fvself, q, v, a2, w, t, u, m, d, e, y}` (`m`, `d`: the vtable dispatch of Widening 7; `e`: the GOT call of Widening 8; `y`: the indirect caller of Widening 10) compiled by the pipeline (a `try_call` f→g, an `sret` call f→s into `f`'s stack slot, a stack-passed argument f→k, a non-leaf callee g→h, recursion r↔r__fvself, `call_indirect` of `func_addr` and a GOT call v→q, `i128` pairs w→a2 of the legalised `i128` functions, a called function with a stack slot f→t placed by the slot-placement oracle, a called function passing a stack argument f→u→k), all premises discharged (`NeedSlots` and `NeedNI` hold, their premises proven), `f 41` returns `802` |

**Callees that return values** (`idX sym tp idf`: a callee `n` with `idf n` returns its first
argument — a `bl n` or a `blr` to `sym n 0` —, every other callee returns nothing; the hooks are
the same witness, which keeps x0): `calleeOk_id` gives `CalleeOk F K (idX …) (witnessHooks …)
(IdSite idf)` for every `F` and `K ≥ 32`, where `IdSite idf` are the call-site shapes the
compiler emits for a `(i64) -> i64` callee (`⟨.sym n, [(vreg u, x0)], [(x0, vreg d)]⟩`, and the
GOT form `⟨.reg (vreg t), [(vreg u, x0)], [(x0, vreg d)]⟩`) and for callees without results;
`xCallsOk_id` the external contract for an environment whose `idf` externs return their argument;
`final_contracts_id`/**`backend_correct_final_id`**: `backend_correct_final` with every contract
premise discharged for a function without `try_call` and indirect calls whose call sites are
`IdSite idf` (`hsites : ∀ info, vcp.CallSite info → IdSite idf info`, a decidable fact of the
compiled code). Smoke check: the pipeline (`lowerFunction`, `prepare`) on

```
function %caller(i64) -> i64 {
    fn0 = colocated %id(i64) -> i64
    fn1 = %id2(i64) -> i64
    fn2 = colocated %sink(i64)
block0(v0: i64):
    v1 = call fn0(v0)
    v2 = call fn1(v1)
    call fn2(v2)
    return v2
}
```

emits exactly the three `IdSite` shapes (`bl id`; GOT `blr` of `id2`, argument and result in x0;
`bl sink` without defs). This is why the contract is restricted to the call sites: over every
`CallInfo` no callee returning a value meets it (a call with the same callee and arguments whose
def is x19 forces the callee to overwrite x19, which a call without defs requires it to keep).

**Functions with `try_call`s** (agent/trycall-contract): `calleeTryOk_witness` gives
`CalleeTryOk F X H vcp.TrySite` for every `F`, `X`, `H` when the `try_call` sites of `vcp` have no
results (`hrets : ∀ info ti, vcp.TrySite info ti → ti.rets = 0`, a decidable fact of the compiled
code; it holds when the `try_call` callees return nothing, as `hsig` says of every extern), and
**`backend_correct_final_try_witness`** is `backend_correct_final` with every contract premise
discharged (`hCT` included) for such a function, with the witness callee, which leaves x0/x1 as
the caller had them — the callee the former `CalleeTryOk` excluded. Smoke check: the pipeline
(`lowerFunction`, `prepare`, regalloc2, `checkAlloc`) on

```
function %tc(i64) -> i64 system_v {
    sig0 = (i64) system_v
    fn0 = %sink(i64) system_v
block0(v0: i64):
    try_call fn0(v0), sig0, block1, [ tag0: block2(exn0, exn1) ]
block1:
    return v0
block2(v1: i64, v2: i64):
    v3 = iadd v1, v2
    return v3
}
```

emits one `tryCall` with `ti.rets = 0` whose defs are the payload vregs in x0 and x1, the handler
edge block passes both payloads to `block2`, and regalloc2's allocation passes `checkAlloc`.

**Not witnessed** (stated, not proven to be satisfiable): nothing among the contract premises.

## The theorem (`FV/E2E/Main.lean`)

```lean
theorem backend_correct {p f k vc vcp rf af fa fb}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F syms slotOff out K astep env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w))
    (htries : ∀ s, TryCalls f (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p)
    (htryInds : ∀ s, TryIndCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p (indSigs f))
    -- M6 + M5
    (hM6 : RegLevelCorrect sem F K astep vcp af fb)
    -- the shared VCode semantics of each activation (M6's `csem (F s)`)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    -- the callee contract (M6, from `CalleeSound`)
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the indirect-call contract (M6, from `XCallsIndOk`)
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    -- the outgoing stack-argument area of the relation holds every call's stack arguments
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra s w₀ args cs}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs)
```

`backend_correct_of_rules`: the same with `hterms` replaced by M4's terminator statements
`LowerTermRulesCorrect`, `TermUnmatchable`, `BranchRulesCorrect`, `BranchExcludedUnmatchable`,
`htries` by the `try_call` statements `TryRulesCorrect`, `TryUnmatchable`, and `htryInds` by
the `try_call_indirect` statements `TryIndRulesCorrect`, `TryIndUnmatchable` (of
`Isle.Aarch64.program`; `backend_correct_m4` discharges them by `tryRulesCorrect`,
`tryUnmatchable`, `FV/Backend/Proof/IselCtlTry.lean`, and `tryIndRulesCorrect`,
`tryIndUnmatchable`, `FV/Backend/Proof/IselCtlTryInd.lean`; `hindRules` by `indRulesCorrect`).

`ArmRefines fb base ra astep s o`:

* `o = .returned vals cm` ⇒ `∃ n, ArmRet ra s (runX astep n s) ∧ (∀ j v, vals[j]? = some v →
  XHolds v (xreg j (runX astep n s))) ∧ MemAgree cm (runX astep n s)`;
* `o = .trapped c` ⇒ `∃ n, TrapAt fb base c (runX astep n s)`;
* `stuck`, `outOfFuel`: no claim.

## Definitions (`FV/E2E/Statement.lean`)

* **Width convention**: `VHolds v x := x.setWidth v.ty.width = v.bits` (M4's; low bits, upper
  bits unspecified); `XHolds v x := VHolds v (ofX x)` for a 64-bit register (= low bits for
  widths ≤ 64, `XHolds_iff`).
* **Subset** `InSubset p f`: `p.func? f.name = some f`, `Compile.functionE f` (clif-subset-v2
  E), every `call` targets an extern (not a function of `p`), the extern of every `try_call`
  takes at most 8 parameters (`tryRegArgs`: no stack-passed arguments of a `try_call`; the
  compiler flags such functions unverified, `Backend.regArgCalls`; parameters and `call`
  arguments beyond the registers are passed on the stack, agent/stack-tls-proof), and the
  signatures of `f` and its externs pass `sigAbiOk` (`abiSigs`: `normal` plus at most one
  `sret`; `Backend.abiSigs`), every `try_call` calls an extern (`tryExterns`), and the
  indirect calls' signatures take at most 8 parameters and pass `sigAbiOk` (`indSigs`,
  `Backend.indSigsOk`). `br_table`
  indices of at most 32 bits are enforced by `lowerCheck` (`brIdxOk`, contract change #6):
  an `i64` index is a compile error, as in Cranelift's verifier; so is a jump table with `2^32`
  or more entries (contract change #9).
* **Compiled code** `Compiled f k vc vcp rf af fa fb`: `lowerFunction f = ok vc`,
  `lowerCheck f vc = true`, `prepare vc = ok vcp`, `prepCheck vc vcp = true`, `checkAlloc vcp rf =
  ok ()`, `lowerRFunc vcp rf = ok af`, `emitFunc k af = ok fa`, `fa.layout = ok fb` (`rf` =
  whatever the untrusted regalloc2 returned). The pipeline (`compileFileWith`, the regalloc2
  allocator) runs both validators on every function inside the theorem and rejects the function
  when one returns `false`.
* **CLIF entry** `ClifEntry f args cs`: no callers, frame of `f` at its entry block, parameters
  bound to `args` (types checked), slot ids of `f`. Slot addresses and memory are free: CLIF
  leaves stack-slot addresses unspecified; `Clif.run`'s bump allocator picks one choice
  (`clifEntry_initState`), the Arm frame another. The theorem is about `Clif.runLoop` from the
  entry state whose slots are at the Arm frame's slot region (`SlotRel`).
* **Memory** `MemRel F syms cm s`: initialised bytes of live CLIF allocations are the Arm bytes
  at the same addresses; every live CLIF address is below 2⁶⁴ and outside the addresses `F`
  outside the world (the allocator-private part of the frame: spill/save slots, fp/lr; since
  agent/callee-fix also the callees' dead stack, `frameW`); `cm.symbols = syms` (link-time
  `symbol_value` addresses).
* **Slots** `Rel.holds Γ f slots cm w := MemRel Γ.F Γ.syms cm w ∧ SlotRel f (Γ.slotReg w)
  slots ∧ OutRel Γ.F Γ.out cm w`, `Γ.slotReg w = sp(w) + Γ.slotOff`; `OutRel`: the outgoing
  stack-argument area `[sp(w), sp(w) + Γ.out)` fits the address space, avoids `F` and holds no
  byte of a live CLIF allocation (vacuous for `Γ.out = 0`: `Rel.holds_zero`); `SlotRel`: slot `id` is at `base + off(id)` with
  `off` from `slotLayout f.slots`. This is M4's `MR` (`MRStable`, `mrStable_holds`).
* **Traps** `TrapsExplicit env p cs`: every trap of the CLIF run from `cs` comes from a `trap`
  terminator or a `div` (explicit check + `udf`/`trapIf` in the code; `stmt`), and the step of a
  `try_call` terminator of the entered function does not trap (`tryCall`). Memory-access traps
  and traps inside externs are excluded: the Arm model has no memory faults, callees are outside
  the theorem (for DSL output traps are unreachable, PLAN.md §3.2).
* **ABI entry** `AbiEntry fb base ra s`: code words of `fb` loaded at `base`
  (`s.program = fb.program base`), pc = base, no model error, x30 = ra outside the code, sp
  16-aligned, code fits the address space. `ArgsIn f.sig args s`: the argument at a register
  location of `locsOf f.sig` in that register (low bits; x0.. in order, an `sret` parameter in
  x8), the argument at a stack location `off` in the caller's outgoing area (`StackArgAt`: its
  bytes at `sp(s) + off`, inside the address space, not code). `StackArgsAvoid` (internal to
  `backend_correct`, discharged by `stackArgsAvoid_frameW`): those bytes avoid the frame and the
  callees' dead stack.
* **Resource precondition** `StackAvail K af s` (`StackRoom (af.frameSize + 16 + K) s`): the
  frame (`af.frameSize` + fp/lr) and the callees' stack budget `K` fit below sp without wrapping
  and hold no code. The callees use the `K` bytes below the body's `sp` (`CalleeOk`).
* **Body entry** `BodyEntry af s w₀` (M6Rest2's definition): the world the function body starts
  in after the prologue: sp lowered by `frameDrop af`, x29 the frame pointer, x0–x7 and v0–v7, memory,
  program and every unmasked field other than x29/sp as in `s`. The VCode runs (and the CLIF
  slot relation `hrel`) are relative to `w₀`; the arguments transfer (`argsIn_body`).
* **Per-activation semantics** `sem s` (M6's `csem (F s)`, `F s` the activation's frame
  addresses): `hRef`, `hds`, `hterms` and `PrepareCorrect` are stated for every `s`.
* **Exit** `ArmRet ra s s'`: pc = ra, no error, sp, x19–x29 and the low 64 bits of v8–v15 as at
  entry. `MemAgree cm s'`: live CLIF bytes = Arm bytes. **Trap** `TrapAt fb base c s'`: no error,
  pc at a trap site `t ∈ fb.traps` with `t.code = c`.
* **VCode observables** `VReturns`/`VTraps` = `VRetFrom`/`VTrapFrom` from `VConf.init`: the
  run reaches `rets us` (values = its use values) / an instruction whose semantics halts and
  whose `trapCode?` is `c`.

## Hypotheses and owners

| Hypothesis | Owner | Status |
| --- | --- | --- |
| `LowerRulesCorrect program`, `ExcludedUnmatchable program` (every closure root rule of `lower` other than the call rules 1031/1032 is correct on statements; the others never match) | M4 (`IselContract.lean`) | `LowerRulesCorrect`: stated, rules proven family by family (M4AluA/B, M4Cmp, M4Ctl); `ExcludedUnmatchable program`: **proven** (`excludedUnmatchable`, M4Excl, `backend-proof.md` "Excluded root rules") |
| `CallRulesCorrect program` (call rules 1031 `bl`, 1032 GOT + `blr`, under `CallsRefine`, for `CallRegArgs f`) | M4 (M4Ctl) | stated (contract change #5) |
| `CallsRefine (F s) env exts MR (sem s)` (callee contract at the VCode level: `loadExtNameGot` loads `sym n`; a call of a declared extern `ext ∈ exts` with ≤ 8 arguments and one def per `sigRets ext.sig` returns one value per def, the first ones its results, and a world related to the extern's memory) | M6 (`csem` from `CalleeSound` + `ExtSem.sym`) | **proven** for `csem` from `XCallsOk` (`callsRefine_csem`) |
| `TermCalls (sem s) MR` (every terminator call `lowerFunction` makes satisfies `LowerTermOk`) | M4, via `termCalls_of_rules` | **proven** from `LowerTermRulesCorrect` (rules 964 `trap`, 1037 `return` of `lower`: `LowerTermRuleOk`), `TermUnmatchable` (other `lower` rules never match a `return`/`trap`), `BranchRulesCorrect` (`BranchRuleOk`, now with `CtxInv`/`ValsBelow`/first-match premises), `BranchExcludedUnmatchable`; these four are M4's open obligations (`backend_correct_of_rules`) |
| `RegLevelCorrect sem F astep vcp af fb` (VCode returns/traps from the body-entry world ⇒ Arm returns/traps, forward) | M6 + M5 (`M6Rest2`) | placeholder with the agreed content (`BodyEntry`, per-activation `sem`) |
| `Refines (F s) (sem s)` (the VCode semantics refines M4's `ispec`, every control) | M6 (`csem` characterization lemmas) | **proven** for `csem` (`refines_csem`, M6Refines) |
| `DriverSem (sem s)` (`Args` reads the argument registers, `jump` → `goto 0`, invariance under class-preserving vreg renamings, **invariance under branch retargeting** `setTargets`) | M6 (`csem`) | agreed (retarget: M6Rest2 2026-09-27), open (M6) |
| `LoweringObligations f vc` | M7 | **discharged** by `lowerCheck` (`Compiled.lowerOk`) |
| `PrepareCorrect (sem s) vc vcp` | M7 | **discharged** by `prepCheck` (`Compiled.prepOk`) + `DriverSem`; `Compiled.prepOk` itself follows from `PrepDomain vc` (`Compiled.of_prepDomain`) |

M6's own premises (`CalleeSound`, jump tables readable, relocation hooks `ArmStepX ext`) are
premises of its instantiation of `RegLevelCorrect`, so they become premises of the
instantiated `backend_correct`; `astep` is M6's `ArmStepX ext` (`stepi` except at calls and
relocated address computations, which run the external hooks).

## The driver lemma (`FV/Backend/Proof/LowerSim.lean`)

```lean
theorem driver_correct (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (hB0 : f.blocks[0]? = some B0)
    (hcall hfunc hslots hbody hterm hregs hty) (hmr : MR slots cs.mem w₀)
    (hargs : ∀ i v, args[i]? = some v → VHolds v (regVal w₀ (.x i)))
    (htr : TrapsExplicit-condition) (fuel) :
    RunOk vc sem MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs)
```

`DriverHyp`: `LowerShape` (structure of `lowerFunction`'s VCode), `Cert` (SSA availability
certificate), `DriverSem`, `InstCalls`/`TermCalls` (M4 contracts at the `runTerm` level),
extern-only calls, no `return_call`, `VCode.cfg` succeeds.

Simulation relation `Match s vs`: the CLIF state is at statement `j` of block `bi`, the VCode
state at that statement's segment (`pos bi j`); every value tracked by the certificate
(`A bi j`) is held (low bits) by its **resolved** vreg `gn x` (alias resolution
`MInst.mapRegs (resolve …)`); the frame restricted to the tracked values is DFG-consistent;
`FrameTyped`: every tracked value has its context type (results: `instOutcome_types` +
`Cert.resTy`; block parameters: `enterBlock`'s type check + `Cert.paramTy`; entry: the
`ClifEntry` argument types); memory related by `MR`. `ValsBelow ctx st` for every `lower`
call: `LowerShape.valsBelow` + `st0.nextVreg ≤ st.nextVreg`. Key steps:

* `seqRun_rename` + `operands_mapRegs` (all `MInst`s): the renamed segment run simulates M4's
  run of the un-renamed code from `ρ ∘ gn`, because every register the code reads is either
  written by it or not clobbered by it (certificate + M4's `UsesOk`/`defs`).
* `stmt_step`: statement ↦ segment (results via the rule outputs and the alias map; tracked
  values keep their registers; DFG consistency re-established; explicit traps reach the halting
  instruction).
* `term_step`: `return` (the `rets` instruction and its values), `trap`, `jump` (branch
  arguments as `VStep`'s parallel copy), `brif`/`br_table` (edge blocks: goto, `jump` via
  `DriverSem`, parallel copy), using `succOf_eq` (successors from the last instruction's targets
  with labels = indices).
* `entry_step`: `Args` defines the parameters from x0.. (`operands_args`).
* `term_step_try`: a `try_call` (the call and the pending jump, two CLIF steps) ↦ the
  terminator's code up to the `tryCall`, the normal-return edge block and its `jump`.
* `sim_run`: strong induction on fuel.

## The validators (M7, translation validation)

**`lowerCheck f vc`** (`DriverCheck.lean`): runs `buildCtx f`, re-runs the ISLE calls the way
`lowerFunction` makes them (`lowBlocks`: statement calls from the previous state with nothing
emitted, terminator calls in the terminator context, the same edge-block labels), computes the
alias resolution `gn` (`gnTable`/`gnAt`, identity on temporaries) and its class-preserving
renaming `renOf gn`, the available values `A` by a must-dataflow (`inFix`/`availOf`; a value
stays available at a block entry only if the operands of its definition are available there
too, so a block without a path from the entry, e.g. cg_clif's dead cleanup blocks, does not
claim values computed from its own results — an untrusted worklist over (block, value) pairs,
the certificate is checked), and decides every
field of `LowerShape` and `Cert` that is not true by construction: `CtxInv` (incl. `defClif`,
and `resTysE`/`valTyE`: result and value types `i8..i64`, M4Excl),
`ValsBelow` (`valReg.size ≤ nextVreg`), the VCode blocks are exactly the renamed recorded code,
labels, block parameters, branch arguments, edge blocks, the terminator slot placeholder, and
the certificate (operands available, results fresh and uniquely defined, no available value's
register written by a statement's lowering, closure under definitions, edges, result and
parameter types for `FrameTyped`). The certificate check is near-linear: membership in
`availOf f In bi j` is decided in constant time (`Avail.mem`: a hash set of the block's entry
values, a value's defining statement from `ctx.defInst?`, exact once the check has seen that
every statement's results are defined by its instruction, `DefsAt`/`mem_avail`), and the
conditions on the values available before the statements of a block are checked once per
value, at the first statement it is available before (the clobber condition through the
increasing fresh-vreg ranges of the statements, `chain_mono`). Soundness: `lowering_of_check`
(construction lemmas `lowStmts_spec`/`lowBlocks_spec` + one lemma per check; `cert_of_ok`
holds for any entry values `In`, so the dataflow is not part of it).

**`prepCheck vc vcp`** (`PrepareCheck.lean`): every live block of `vc` (`liveOf`: reachable
from the entry, as `prepare` computes; untrusted, the check requires the entry to be live and
live blocks' successors to be live) has a counterpart in `vcp` (same label) with the same
parameters, branch arguments and instructions except a possibly retargeted last instruction;
the entry is its own counterpart; successors are reached directly or through an edge block
(`jump`, no parameters/arguments) from a block without branch arguments. Dead blocks are not
checked (`prepare` drops them, and its edge blocks may reuse their labels). Soundness:
`prep_sound` (simulation over live blocks; a split edge takes one extra `jump` step).

**Validator completeness: `prepare` is correct without `prepCheck`** (2026-10-02,
`FV/Backend/Proof/PrepareComplete.lean`, `PrepareDirect.lean`, `FV/E2E/PrepDirect.lean`):

```lean
structure PrepDomain (vc : VCode) : Prop where
  nonempty : 0 < vc.blocks.size
  labels : Lbls vc.blocks          -- (vc.blocks.toList.map VBlock.label).Nodup
  args : ∀ b vb t, vc.blocks[b]? = some vb → vb.insts.back? = some t →
    2 ≤ t.targets.length → vb.branchArgs = #[]

theorem Prep.prepCheck_complete {vc vcp : VCode} (h : prepare vc = .ok vcp)
    (hd : PrepDomain vc) : prepCheck vc vcp = true
theorem Prep.prepare_correct (hds : DriverSem sem) (h : prepare vc = .ok vcp)
    (hd : PrepDomain vc) (ρ₀ w₀) : (returns of vc ⇒ returns of vcp) ∧ (traps ⇒ traps)
theorem E2E.prepareCorrect_of_domain (hds : DriverSem sem) (h : prepare vc = .ok vcp)
    (hd : PrepDomain vc) : PrepareCorrect sem vc vcp
theorem E2E.Compiled.of_prepDomain (hl : lowerFunction f = .ok vc) (hlo : lowerCheck f vc = true)
    (hp : prepare vc = .ok vcp) (hd : PrepDomain vc) (hch : checkAlloc vcp rf = .ok ())
    (ha : lowerRFunc vcp rf = .ok af) (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    Compiled f k vc vcp rf af fa fb
```

Every end-to-end theorem that takes `hc : Compiled …` (`backend_correct_final`,
`backend_correct_opt_proven`, `backend_correct_legal`, …) therefore holds with
`Compiled.of_prepDomain …` in place of `hc`, without the `prepCheck` premise. The existing
theorems are unchanged. `PrepDomain` is what `lowerFunction` produces: labels are block indices
(`lowerCheck`'s `shapeOk`), and only a `jump` block or an edge block carries branch arguments.
`prepDomainB` decides it (`prepDomain_of`). On the corpus and the runtests, every
`lowerFunction` result (1067 functions) is in `PrepDomain`, and `prepCheck` accepts every
`prepare` output. The compiler keeps running `prepCheck` (`allocateRegalloc2`) as a runtime
double-check.

**Validator completeness: the lowering validator `lowerCheck` (V1, V2)** (2026-10-05,
`FV/Backend/Proof/Lower{Spec,Fix,Loop*,Alias,ShapeOk*,Cert*,Decide,Complete}.lean`,
`IselFlow*.lean`, `IselTermFacts*.lean`, `FV/E2E/LowerDirect.lean`):

```lean
theorem Backend.Proof.Driver.lowerCheck_complete {f : Clif.Function} {vc : VCode}
    (hd : Dominated f) (hs : LowerScope f) (h : lowerFunction f = .ok vc) : lowerCheck f vc = true
theorem Backend.Proof.Driver.prepDomain_of_lower (hs : LowerScope f) (h : lowerFunction f = .ok vc)
    (hne : f.blocks ≠ []) : Prep.PrepDomain vc
theorem E2E.Compiled.of_lower (hd : Dominated f) (hs : LowerScope f) (hl : lowerFunction f = .ok vc)
    (hp : prepare vc = .ok vcp) (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) : Compiled f k vc vcp rf af fa fb
theorem dominated_of (h : dominatedB f = true) : Dominated f
theorem lowerScope_of (h : lowerScopeB f = true) : LowerScope f
```

Every end-to-end theorem taking `hc : Compiled …` holds with `Compiled.of_lower …` in place of
`hc`: neither `lowerCheck` nor `prepCheck` is a premise any more. Both premises are decidable
conditions on the CLIF input alone (`dominatedB`, `lowerScopeB` run `buildCtx` and the
input-only availability `availIn f ctx = inFix f ctx id`, never the lowering):

* `Dominated f`: SSA (`valueDefs f` pairwise distinct), every operand of a statement or
  terminator (`abiTerm`) available at its position (`availOf f (availIn f ctx)`, Cranelift's
  dominance in the certificate's form; unreachable blocks are constrained by the same
  must-dataflow), and no value available at a block's entry and not redefined there computed
  directly from that block's parameters (true on reachable blocks of SSA input).
* `LowerScope f`: subset E (`functionE`), at least one block, no branch to the entry block,
  `br_table` indices of at most 32 bits (`brIdxOk`), atomic accesses at `i64` addresses, a
  `try_call`'s normal-return `retN` below the callee's declared returns, well-formed
  stack-argument layouts of the callees (`stackLayoutOk`).

`lean-e2e-check` reports them: all 1148 in-scope corpus/runtest functions satisfy both. Proof
structure: `inFix` is the greatest solution of its constraints (`inFix_fixOk`, `inFix_greatest`;
V1a made it a fuel-bounded worklist); the rules' facts are decided once over the exported rule
data (`IselFlow*`: `runTerm_mono`, `stmt_flow` — a statement's result registers are fresh vregs
of the call or registers of values its instruction reaches through its operands (`Prov`) —,
`stmt_noTls`/`termCall_noTls`/`tryCall_noTls`; `IselTermFacts*`: `term_emits`, `branch_last`,
`call_outgoing`, `try_outgoing`); `lowerFunction`'s loop computes `vcBlocksOf f bl` for the
recorded lowering `lowBlocks` (`lowerFunction_run`, V1d) and its VCode is in `PrepDomain` (V2);
the alias chains are well founded (`alias_facts`), so `lowerFunction`'s array chase is the
validator's `renOf gn` (`resolve_eq`) and `shapeOk` holds (`shapeOk_complete`); the
renaming-dependent `inFix` agrees with `availIn` outside each block's own definitions and the
certificate holds (`certOk_complete`). Non-vacuity: `E2E.lowerCheck_complete_witness` (a loop
with block parameters and an edge block). A branch without arguments to a block with
parameters is accepted by `lowerFunction` and `lowerCheck` alike; CLIF is stuck there
(`enterBlock`: "block arity"), so the theorems claim nothing about such a run. The compiler
keeps running `lowerCheck` as a runtime double-check.

**Validator completeness: form coverage `formsCoveredB` (V3)** (2026-10-05,
`FV/Backend/Proof/IselCov{Dom,Sem,Form,Le,Check,Fns,Sound,Data,Ext,Ctor,Model,Clean,Tab,Driver}.lean`,
`LowerCover.lean`, `FormsCoverComplete.lean`, `FV/E2E/FinalDirect.lean`; generator
`FVTest/Backend/IselCovGen.lean`):

```lean
theorem Backend.Proof.Driver.formsCovered_complete {f : Clif.Function}
    {vc vcp : VCode} (hs : LowerScope f) (hl : lowerFunction f = .ok vc)
    (hp : prepare vc = .ok vcp) (cx : FnCtx) : FormsCovered cx vcp
theorem E2E.backend_correct_final_of_lower (hsub : InSubset p f)
    (hd : dominatedB f = true) (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc)
    (hp : prepare vc = .ok vcp) (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb)
    -- backend_correct_final's contract, link-time and run premises (hC … htr), unchanged
    : ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)
```

`backend_correct_final_of_lower` is `backend_correct_final` without `hc : Compiled …` and
`hcov : FormsCovered …`: of the compiler's checks only `checkAlloc` (V4) remains a premise.
`LogicImmComplete` (`IselCovSem.lean`: every logical immediate `ImmLogic.ofNat?` accepts is
encoded, `logicImmOk`), used by the ISLE-level lemmas, is proven by `logicImmComplete`
(`LogicImmComplete.lean`: kernel `decide` over the 5334 (e, c, r) triples, 16 chunks). Proof: an abstract interpretation of the exported ISLE rules,
decided once (no per-program check). Abstract values `AW` (`γ`: register kinds, enum variants,
types, immediates with their range facts, "every `MInst` inside is covered") and the abstract
`FormOk` `covOk` (`covOk_sound`); `aRule` evaluates a rule disjunctively (patterns split
abstract values, prune impossible variants/constants and the exclusion checker's `fails`),
internal calls go to the summary table `covTab` (704 entries over the terms reachable from the
closure roots of `lower` and from `lower_branch`, computed by the untrusted generator at V3; the
generator has given 707 entries since V6c's `.num` leaves, both pass, the 704-entry one is kept,
`FVTest/Backend/IselCovGen.lean`) or the
`operand_size` oracle, extern helpers to transfer functions whose soundness is `ext_sound`
(`Clean ctx`: the context's instruction data hold no registers or instructions) and
`ctor_sound` (every `emit`ted instruction covered: `CovSince`); `soundAt` (induction on the
interpreter's fuel) makes every run of a checked term land in its abstract output. `chkTab`
and the root checks use leaf-wise `decide +kernel` (8 table chunks + 4 roots, IselCovTab.lean). Driver:
`stmt_cov` (emitted code covered; result registers of an instruction with results are int
vregs, so `lowerFunction` adds no result `mov`), `termCall_cov`, `tryCall_cov`; the final
alias renaming keeps register classes (`resolve_vrenaming`, `covered_mapRegs`), the entry's
`Args`/parameter loads and the edge `jump`s are covered, a `try_call`'s fixup only inserts a
`tryCall`, and `prepare` only retargets control instructions (`formsCovered_of_prepare`).
Non-vacuity: `E2E.formsCovered_complete_witness` (`lowerWitness`). The compiler keeps running
`formsCoveredB` (`lean-e2e-check`) as a double check.

**The control shapes of the ISLE runs (V4 (a), `IselCtlHyp`)** (2026-10-05,
`FV/Backend/Proof/IselShp{Fns,Base,Root,Tab,Total,Ctor,Oracle,Call,Try,BrTable,Driver}.lean`,
generator `FVTest/Backend/IselShpGen.lean`): `Backend.Proof.Driver.iselCtlHyp : IselCtlHyp`
(SpillCtlPipe.lean; its `try_call` clause takes `∃ B ∈ f.blocks, B.term = t`). V3's
`CovModel`/`soundAt` are parametric in `actor`/`apre`/`aOracle`; the control-shape model
`shpModel` uses `apreS` (an `emit`ted control form is a `CondBr`/`TrapIf` on a condition or an
int vreg, a `TestBitAndBranch` on an int vreg, `Udf`/`EmitIsland`/`Jump`; `gen_return` returns
int vregs) and `aOracleS` (the helpers emitting `loadExtNameGot/Near`, the LL/SC loops and
`ElfTlsGetAddr` with fresh distinct defs, `oracle_ctl`), state invariant `ShpIs N s0`
(`CtlSince N s0 ∧ N ≤ nextVreg`). Table `shpTab`: 641 entries, 8 chunks + 3 roots by
leaf-wise `decide +kernel`. Hand-checked root rules (`root_hand`, `HandOk`): calls 1031–1033
(`handOk_call`), `try_call`s 1034–1036 (`handOk_try`), `br_table` 1140 (`handOk_brTable`, its
`imm`/`put_in_reg_zext32` sub-runs from the table via `SubOk`). `totality`: a non-`partial` term
never returns `none` (`totalProg_program`). Corollary `E2E.ctlSpillHyp` (under `InSubset`);
witness `E2E.ctlSpillHyp_of_witness`.

**Register allocation without the `checkAlloc` premise: the spill fallback (V4 (a))** (2026-10-05,
`FV/Backend/SpillAlloc.lean`, `FV/Backend/Regalloc.lean` `lowerAlloc`, `FV/E2E/AllocDirect.lean`):

```lean
def Backend.allocResult (vc : VCode) (ra : Except String RFunc) : RFunc  -- ra if checkAlloc accepts it and lowerRFunc lowers it, else spillAlloc vc (V5)
theorem Backend.lowerAlloc_eq_lowerRFunc (vcp : VCode) (ra : Except String RFunc) :
    lowerAlloc vcp ra = lowerRFunc vcp (allocResult vcp ra)
theorem Backend.lowerAlloc_eq (h : lowerAlloc vcp ra = .ok af) :
    lowerRFunc vcp (allocResult vcp ra) = .ok af
```

The backend lowers `allocResult vcp ra` (`lowerAlloc`, `lowerAlloc_eq`): regalloc2's answer if
`checkAlloc` accepts it (and, since V5, `lowerRFunc` lowers it), else the spill allocation
`spillAlloc` (a total Lean function; every value in its own stack slot,
`docs/contracts/regalloc.md` "Fallback"). A rejection or a missing answer of regalloc2 is no
longer a compile error, and `backend_correct_final_alloc` (below) holds for every answer `ra` of
the untrusted allocator: its correctness never depends on regalloc2. `lean-e2e-check` decides
`checkAlloc`'s acceptance of the spill allocation on every in-scope function (**1148 of 1148**,
"spill fallback" line; the compiler's runtime double-check `lowerSpill` was removed with V5, since
the acceptance is proven).

**V4 restated: verified in-states, `ρ₀` chosen by the register-level theorem** (2026-10-05,
`FV/Backend/Proof/RegallocSound.lean`, `FV/Backend/Proof/SpillInvariant.lean`,
`FV/E2E/AllocDirect.lean`). The first statement (PR #54: `checkAlloc vcp (spillAlloc vcp) = .ok ()`
under `Dominated`/`LowerScope` only) was false (`E2E.not_ctlSpillHyp`: two `sret` parameters) and
asked more than the proofs use (the checker's fixpoint iteration; an entry state without vregs,
i.e. every use defined on every path); it has been replaced by:

```lean
structure Backend.Proof.CheckedAt (vc rf c ins) (a0 : AState) : Prop  -- `Checked`, entry in-state a0 unconstrained
def Backend.Proof.EntryOk (a0 : AState) : Prop    -- entry r only in reg r (callee-saved); each vreg in ≤ 1 location
def Backend.Proof.AllocChecked (vc : VCode) (rf : RFunc) : Prop :=
  ∃ c ins a0, CheckedAt vc rf c ins a0 ∧ EntryOk a0
theorem Backend.Proof.allocChecked_of_checkAlloc : checkAlloc vc rf = .ok () → AllocChecked vc rf
theorem Backend.Proof.checkedAt_sound (hc : CheckedAt vc rf c ins a0) (m₀ ρ₀ w₀)
    (hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r))) : ∃ R, IsSimulation vc rf sem keep R ∧ …
theorem Backend.Proof.allocChecked_sound (h : AllocChecked vc rf) (m₀ w₀) : ∃ ρ₀ R, …  -- ρ₀ := entryRho a0 m₀
def E2E.RegLevelCorrectEx … := ∀ base ra s, AbiEntry … → StackAvail … → ∀ w₀, BodyEntry af s w₀ →
    ∃ ρ₀ : Nat → CV, (returns as in RegLevelCorrect) ∧ (traps as in RegLevelCorrect)
theorem Backend.Proof.regLevelCorrect_backend_ex (hcheck : AllocChecked vcp rf) … : RegLevelCorrectEx …
theorem E2E.backend_correct_final_ex (hc : CompiledA f k vc vcp rf af fa fb) …  -- CompiledA: check : AllocChecked
def E2E.SpillAccepted : Prop := ∀ p f vc vcp, InSubset p f → Spill.ArityOk f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc → Backend.prepare vc = .ok vcp → AllocChecked vcp (spillAlloc vcp)
theorem E2E.spillAccepted_of_step4 (h4 : Spill.SpillStep4) (hav : SpillAvailable) : SpillAccepted
theorem Spill.spillStep4 : Spill.SpillStep4  -- ∀ vc D, (∃ succs preds, vc.cfg = .ok (succs, preds)) → SpillLocalOk vc → SpillAvail vc D → AllocChecked vc (spillAlloc vc)
theorem E2E.spillAccepted_of_avail (hav : SpillAvailable) : SpillAccepted
theorem E2E.backend_correct_final_alloc (hsa : SpillAccepted) (hsub : InSubset p f)
    (hd : dominatedB f = true) (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true) (hl …) (hp …) (hrf : rf = allocResult vcp ra) (ha …) (he …) (hla …)
    -- backend_correct_final's contract, link-time and run premises (hC … htr), unchanged
    : ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)
```

`IselSim` and `PrepareCorrect` hold for every initial vreg file, so the composition
(`backend_correct_of_layers_ex`) instantiates them with the one the register-level theorem picks
from the activation's initial frame (`entryRho`: the value of the location the entry state places a
vreg in). The spill allocation may therefore start with every home holding its vreg; what remains
is availability (`Spill.SpillAvail`), not definedness. The old statements (`checkAlloc_sound`,
`regLevelCorrect_world`, `backend_correct_of_layers`, `backend_correct`, `backend_correct_of_rules`)
are corollaries; `Compiled` keeps `checkAlloc` because the link-level theorems (`LinkWorld`,
`PairDriver`) fix one VCode outcome for all activations, which needs every `ρ₀`. Open, as an explicit
hypothesis: `E2E.SpillAvailable` (`docs/TO-PROVE.md` V4 step 4); step 3 is `E2E.spillLocalAll`, the
step-4 invariant proof `Spill.spillStep4` (2026-10-05; `SpillStep4` takes a CFG premise, which the
pipeline's output meets, `Spill.cfg_ok_of_prepare`). Non-vacuity: `E2E.backend_correct_final_alloc_witness`.

**`SpillKillFree` and `SpillAccepted` proven; the allocation is no longer a premise (V4 (a))**
(2026-10-05, `FV/Backend/Proof/Kill{Base,Gen,OfV,Ctor,Tab,Oracle,Driver,TryDefs,Assemble,Prep}.lean`,
`FV/E2E/SpillKillFree.lean`):

```lean
def Backend.Proof.Kill.KillRunsHyp : Prop  -- every ISLE run of the driver: RunKill (+ OutKill, try defs)
theorem Backend.Proof.Kill.killRunsHyp : KillRunsHyp
theorem Backend.Proof.Kill.tryDefsExact : TryDefsExact  -- a try_call's call defs = its result vregs, in order
theorem Backend.Proof.Kill.killFreeB_lower (hK : KillRunsHyp) (hX : TryDefsExact) (hd : Dominated f)
    (hs : LowerScope f) (ha : AbiSigsOk f) (har : ArityOk f) (hl : lowerFunction f = .ok vc) : killFreeB vc = true
theorem Backend.Proof.Spill.killFreeB_prepare (hv : LowOk vc) (hk : killFreeB vc = true)
    (hp : prepare vc = .ok vcp) : killFreeB vcp = true
theorem E2E.spillKillFree : SpillKillFree
theorem E2E.spillAccepted : SpillAccepted := spillAccepted_of_killFree Spill.spillStep4 spillKillFree
theorem E2E.backend_correct_final_alloc_proven (hsub : InSubset p f) (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true) (hl …) (hp …) (hrf : rf = allocResult vcp ra) (ha …) (he …) (hla …)
    -- backend_correct_final's contract, link-time and run premises (hC … htr), unchanged
    : ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)
```

The ISLE part is a uniform invariant of the interpreter, with no abstract domain
(`Isle.Interp.UModel`, `uSound`, `uRoot`, `KillGen.lean`): in a run started at `s0` with fresh vregs
from `lo`, every value holds no `AtomicRMWLoop`/`AtomicCASLoop`/`JTSequence` data and its registers
outside a call's defs are CLIF values' vregs or vregs of the run not killed so far (`KP`,
state-dependent, monotone along the run relation `RsK`: what a sub-run kills is fresh); in a
`try_call`'s context the vregs of call defs are its result vregs; every emitted use is allowed
(`IsK`). The killing forms are built only inside `atomic_rmw_loop`, `atomic_cas_loop` and
`br_table_impl` (oracles, `KillOracle.lean`); the term tables `killTabS` (from `lower`'s rules but
587, 636, 637) and `killTabB` (from `lower_branch`'s) are closed and contain no killing variant and
no `invalid_reg` (`TermSetData.lean`, kernel-certified by `KillTab.lean`); `nop` (587) is a hand rule with no results,
the I128 rules 636/637 never match. `kp_ctor` (`KillCtor.lean`): every extern constructor but
`invalid_reg` keeps the invariant (`MInst.ofV`'s uses are among the value's registers outside call
defs, `ofV_kill`). The driver assembly (`KillAssemble.lean`) uses the runs' disjoint vreg ranges,
the alias resolution (`gn x` is `x` or a statement's result register) and the `try_call` edge blocks
(single predecessor; `termEdgeDefs` keeps the result vregs on the normal edge, all defs on handler
edges, `tryDefsExact`); `prepare` keeps `killFreeB` (`KillPrep.lean`). Non-vacuity:
`E2E.backend_correct_final_alloc_proven_witness` (`backend_correct_final_alloc_witness` and
`spillKillFree_witness`, an LL/SC loop with killed vregs).

**Totality of allocation and lowering (V5)** (2026-10-05, `FV/E2E/SpillLower.lean`,
`FV/E2E/SpillCtlCheck.lean`, `FV/Backend/Proof/AssignOk.lean`, `FV/E2E/AllocTotal.lean`):

```lean
theorem E2E.lowerRFunc_of (hck : ctlCheck vc rf = true)
    (hit : ∀ b vb items, vc.blocks[b]? = some vb → rf.blocks[b]? = some items →
      ∀ it ∈ items.toList, ∃ c, itemCode (RAFrame.compute vc rf) vb it = .ok c) :
    ∃ af, lowerRFunc vc rf = .ok af               -- the converse of lowerRFunc_ok
theorem Backend.Proof.assign_ok_of_operands (h : i.operands = .ok ops) (hs : regs.size = ops.size) :
    ∃ i', i.assign regs = .ok i'
theorem E2E.ctlInsts_pipeline (hsub : InSubset p f) (hd : Dominated f) (hs : LowerScope f) (hl …) (hp …) :
    (∀ b vb k i, vcp.blocks[b]? = some vb → vb.insts[k]? = some i → ctlInstOk b k i = true) ∧
    ∃ vb0 ds, vcp.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) ∧ 1 < vb0.insts.size
theorem E2E.ctlCheck_spill (hcfg : vc.cfg = .ok (ss, ps)) (hloc : SpillLocalOk vc) (hins …) (h0 …) :
    ctlCheck vc (spillAlloc vc) = true
theorem E2E.lowerRFunc_spill_of (hcfg …) (hloc : SpillLocalOk vc) (hins …) (h0 …) :
    ∃ af, lowerRFunc vc (spillAlloc vc) = .ok af
theorem E2E.lowerRFunc_spillAlloc (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hl …) (hp …) : ∃ af, lowerRFunc vcp (spillAlloc vcp) = .ok af
theorem E2E.lowerAlloc_total (…same…) (ra : Except String RFunc) : ∃ af, lowerAlloc vcp ra = .ok af
theorem E2E.backend_correct_final_total (hsub : InSubset p f) (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true) (hl …) (hp …)
    (ra : Except String RFunc) :
    ∃ af, lowerAlloc vcp ra = .ok af ∧ ∀ {fa fb}, emitFunc k af = .ok fa → fa.layout = .ok fb →
      -- backend_correct_final's contract, link-time and run premises (hC … htr) with rf := allocResult vcp ra
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)
```

`lowerRFunc` could reject an allocation (allocator frame ≥ 32 KiB, `ctlCheck`, an operand not in
a register, a missing instruction, `MInst.assign` or `RAFrame.moveInsts` failing), so
`backend_correct_final_alloc_proven` took `ha : lowerRFunc vcp rf = .ok af` as a premise. Now
there is no frame-size limit (slots at 32 KiB or more are addressed through x16:
`slotStoreAt`/`slotLoadAt`, `RegallocSlotsFar.lean`; `lowerRFunc_ok` has no size conjunct), and
`allocResult` also falls back to the spill allocation when `lowerRFunc` rejects regalloc2's, and
the spill allocation is proven lowerable: every item is a move between a register and a register,
a spill slot or a callee-save slot (all laid out by `RAFrame.compute`: `saveOff_spill`), or an
instruction whose locations are `spillLocs` (registers, one per operand); `ctlCheck`'s block-0
part holds by construction (the saves, then `Args`, which has only defs so no loads precede it,
then no `op 0`; `EdgesOk.entry`: no edge enters block 0), and its instruction part on the
pipeline's output (`ctlInsts_pipeline`). `backend_correct_final_total` thus has no allocation or
lowering premise: lowering after allocation is total for in-scope input; the compile-success
premises left are emission/layout (`emitFunc`, `layout`: branch ranges, V6). `lean-e2e-check`
decides the spill lowering ("spill lowering" line: `lowerRFunc` lowers 1149, rejects 0; a
rejection contradicts `lowerRFunc_spillAlloc` and fails the run). Non-vacuity:
`E2E.backend_correct_final_total_witness`.

**Emission and layout: branch relaxation (V6)** (2026-10-06, `FV/Backend/Asm.lean` `relaxLine`/
`relaxOf`/`emitFunc`, `FV/Backend/Proof/RelaxLayout.lean`, `RelaxReady.lean`, `FV/E2E/RegLevelRelax.lean`,
`FV/E2E/RelaxTotal.lean`; policy: `docs/contracts/encoder.md` "Branch-range policy"). `emitFunc` is
`emitPre` (blocks, `fallthrough`, trap section) followed by branch relaxation: a conditional branch
to a far block/trap label becomes `b.!c .+8; b T` (`Lbl.skip` = `pc + 8`). The simulation relation
`Q` now places the remaining items' lines as `relaxLines R.far (ftList …)` (`RL.far = emitFar`);
`reach_rcb` runs a conditional branch in either form (1 or 2 steps), `step_skip` the inverted
branch, `reach_cb`/`reach_b`/`jt_machine`/the `trapIf` proofs are restated on it; `Line.plain`
now excludes every conditional branch (so plain lines are not relaxed, `relaxLines_plain`).
*Since #553* `emitPre` is the emission plan's lines (`emitPlan`: Cranelift's block order and
`MachBuffer`'s branch simplification, `encoder.md`), and in `Q = Qs ∨ QE` `Qs` places the
remaining lines via the block's segment of the plan (`segX`): `relaxLines R.far (X ++ x.2.1)` (the items'
lines but the last instruction's, then the segment's final lines), then the lines from the one
after the segment on; `ftList`, `reach_cb`/`reach_b` are gone (`reach_jumpX`/`reach_condX`).

```lean
theorem Backend.relaxOf_fixpoint (pre : List Line) : farTargets (relaxLines (relaxOf pre) pre) = []
theorem Backend.emitFunc_layout_total (he : emitFunc k af = .ok fa)
    (hlab : ∃ m, labelOffsets fa.lines = .ok m)
    (hdef : ∀ ln ∈ fa.lines.toList, ∀ l ∈ ln.labelsUsed, Line.label l ∈ fa.lines.toList)
    (henc : ∀ i t, Line.ins i t ∈ fa.lines.toList → i.encodable = true)
    (hnear : NearOk fa.lines.toList) (hsz : fa.size < 2 ^ 27) : ∃ fb, fa.layout = .ok fb
theorem Backend.emitFunc_layout_ready (he : emitFunc k af = .ok fa) (h : fa.layoutReadyB = true) :
    ∃ fb, fa.layout = .ok fb
theorem Backend.emitFunc_of_emitPre (h : emitPre k af = .ok pre) : ∃ fa, emitFunc k af = .ok fa
theorem Backend.emitFunc_size_le (he : emitFunc k af = .ok fa) (hp : emitPre k af = .ok pre) :
    fa.size ≤ 2 * (pre.toList.map Line.size).sum
theorem E2E.backend_correct_final_total_relaxed (hsub : InSubset p f) (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true) (hl …) (hp …) (ra : Except String RFunc) :
    ∃ af, lowerAlloc vcp ra = .ok af ∧
      ((∃ pre, emitPre k af = .ok pre) → (∀ fa, emitFunc k af = .ok fa → fa.layoutReadyB = true) →
        ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb ∧
          ∀ … (hC … htr) fuel, ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs))
```

`backend_correct_final_total_relaxed` is V5's `backend_correct_final_total` without its emission and
layout premises (`emitFunc k af = .ok fa`, `fa.layout = .ok fb`; `fa`, `fb` are now existential): branch
range is discharged (relaxable branches by the fixpoint, `b` by the size bound, `.+8` trivially).
Left: `hpre` (instruction expansion, `MInst.lines`' rejections) and `layoutReadyB`'s conditions
(labels unique and defined, operand encodability, the local atomic-loop/jump-table forms in reach,
size < 128 MiB), all decidable on the emitted code but not yet proven from the emitter
(`docs/TO-PROVE.md` V6). Non-vacuity: `E2E.backend_correct_final_total_relaxed_witness` (`lowerWitness`:
`lowerAlloc` succeeds, `emitPre` succeeds and the code passes `layoutReadyB`, `native_decide`) with
`backend_correct_final_total_witness` for the input conditions.

**Emission totality (V6b)** (2026-10-06, `FV/Backend/AllocReady.lean`, `FV/E2E/EmitTotal.lean`,
`EmitPreOk.lean`, `EmitEnc.lean`, `EmitLabels.lean`, `EmitNear.lean`, `EmitSize.lean`, `EmitReady.lean`).
The two premises of `backend_correct_final_total_relaxed` cannot be proven for every allocator
answer `ra`: `checkAlloc` accepts any number of redundant moves (on `lowerWitness`, the spill
allocation padded with `n` copies of `move x19 → save(x19)` is accepted and kept by `lowerAlloc`;
the code is 296 + 4n bytes, so for n = 2^25 it fails `layoutReadyB`). **Compiler change:** the
backend now lowers `lowerAllocReady vcp ra` — `lowerAlloc vcp ra` if its code is `emitReady`
(`emitFunc 0` + `layoutReadyB`; the function index only names labels, `emitFunc_index`), else
the spill allocation (`allocateRegalloc2` moved to `AllocReady.lean`).
`lowerAllocReady_eq : lowerAllocReady vcp ra = lowerAlloc vcp (readyAnswer vcp ra)`, so every
`lowerAlloc` theorem applies. Encoded output is unchanged on the corpus (encode-check: 0 differ).

For the spill allocation's code (`lowerRFunc vcp (spillAlloc vcp) = .ok af`):
`emitPre_spill_ok` (`emitPre` succeeds: covered forms by `formOk_sound`, control forms by
`ctlInstOk` + `spillLocs`: the LL/SC loops get x24–x28, TLS gets x0/x1), `emitFunc_spill_labels`
(labels defined once — block labels distinct from `prepare`, trap/jt/loop counters — and every
used label defined), `emitFunc_spill_encodable` (registers from `spillAccepted`'s checker facts;
immediates from `immsOkB`), `emitFunc_spill_near` (`NearOk`: the atomic loops and jump tables are
blocks of ≤ 8 lines that the branch simplification — it only touches branches to block labels —
and relaxation keep together), `emitFunc_spill_size`
(`fa.size ≤ 8 · rfWords`), combined by `FnAsm.layoutReadyB_of` (the converse of
`layoutReadyB_sound`) into `emitReady_spill`.

```lean
def E2E.emitCondsB (vcp : VCode) : Bool :=
  spillSizeOkB vcp && immsOkB vcp && vcp.noAlwaysB && branchTargetsOkB vcp
theorem E2E.backend_correct_final_total_emit (hsub : InSubset p f) (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true) (hl …) (hp …)
    (hem : emitCondsB vcp = true) (ra : Except String RFunc) :
    ∃ af, lowerAllocReady vcp ra = .ok af ∧ ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb ∧
      ∀ … (hC … htr) fuel, ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)
```

(frame of `allocResult vcp (readyAnswer vcp ra)`). New conditions, all decidable on the prepared
VCode and counted by `lean-e2e-check` (1149 of 1149 pass each): `spillSizeOkB` (the size input
condition, genuinely needed: a big enough function exceeds `b`'s 128 MiB; word bound < 2^24,
largest corpus bound 279479), and three facts about instruction selection's output that are not
yet proven from the ISLE rule data: `immsOkB` (immediates in the encoder's ranges; an indirect
call target is an int vreg), `noAlwaysB` (no `condBr`/`trapIf` on `al`/`nv`, which relaxation
does not handle), `branchTargetsOkB` (every branch target is a block label; `VCode.cfg` checks
only block-final instructions). `lean-e2e-check` also emits the spill code of every in-scope
function and decides `layoutReadyB` ("spill emission" line). Non-vacuity:
`E2E.backend_correct_final_total_emit_witness`.

**Emission conditions from the input (V6c)** (2026-10-06, `FV/Backend/EmitOk.lean`,
`FV/Backend/Proof/IselEmit*.lean`, `FV/E2E/EmitCondsLower.lean`, `FV/E2E/EmitTotalIn.lean`). The
three isel facts of `emitCondsB` are proven from the ISLE rule data. `MInst.emitOk` (`immOkB` and
`noAlways`) is the per-instruction condition. `Driver.iselEmit : LowerScope f → extendsWidenB f =
true → IselEmit f`: every statement's `lower` run emits only `emitOk` instructions without branch
targets (`EmSince`), every terminator's (and `try_call`'s) run only `emitOk` instructions with
branch targets only on the last (`EmLast`). Method: V3's abstract interpreter with emission
transfer functions (`aextE`/`actorE`: numeric leaves `AW.num k b` for immediates, shift amounts,
move-wide constants, call infos; `apreE`: an `emit`ted instruction passes `emChk`), table
`emitTab` (740 entries, 13 kernel-checked chunks, `FVTest/Backend/IselEmitGen.lean`); branch
rules end in their branch (`aRuleLast`/`aLast_sound`, `root_last`: the final `emit_side_effect`'s
last instruction may be a branch); the `uextend`/`sextend` rules (808, 819) and the `extr` rules
(862, 863) by hand (`hand_emit`). `emitConds_lower` follows `lowerFunction`'s assembly and
`prepare` (renaming keeps `emitOk`; branch targets only on block-final instructions, which
`VCode.cfg` resolves to block labels) to `immsOkB ∧ noAlwaysB ∧ branchTargetsOkB` of the
prepared VCode.

New input condition `extendsWidenB f` (`Driver.ExtendsWiden`, decided on `buildCtx f`): every
`uextend`/`sextend` widens. It is CLIF's verifier rule (the run semantics checks it only at run
time) and genuinely needed: `uextend.i32` of an `i64` value selects `Extend` from 64 bits, which
has no encoding. `lean-e2e-check` counts it ("extendsWidenB" line).

```lean
theorem E2E.backend_correct_final_total_emit_in (hsub : InSubset p f) (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true) (hw : extendsWidenB f = true)
    (hl …) (hp …) (hsz : spillSizeOkB vcp = true) (ra : Except String RFunc) :
    -- the conclusion of backend_correct_final_total_emit
```

Non-vacuity: `E2E.backend_correct_final_total_emit_in_witness`.

**The size bound from the input (V6c)** (2026-10-07, `FV/Backend/Proof/IselSz*.lean`,
`FV/E2E/SizeDefs.lean`, `FV/E2E/SizeVC.lean`, `FV/E2E/SizeLower.lean`, `FV/E2E/SizeIn.lean`).
`spillSizeOkB vcp` is proven from the decidable input condition `sizeOkB f`: a word bound
`sizeBoundIn f` (`SizeDefs`) below `2 ^ 24`. The route:

* **Weights.** `szInstW m = szWords m + 20 · regCount m + |m.targets|` (+ the callee-saved restores
  of a `Rets`): `szWords` is `instWords`, `regCount` bounds `MInst.operands` (5, or the list
  lengths of `call`/`tryCall`/`args`/`rets`), so `szInstW` covers the instruction's spill-allocated
  code (a slot load/store of at most 20 words per operand) and the edge block `prepare` may create
  per target. `wtA`/`tgA`: weight and targets of an instruction array.
* **ISLE runs (`Driver.iselSz : LowerScope f → IselSz f`).** A cost analysis on V3's abstract
  interpreter (value table `covTab`): `cExpr`/`cIfLets`/`cRule` (`IselSzDefs`) bound the growth of
  any measure `W` of the lowering state, with a cost table per internal term and abstract inputs
  and extern costs `aw`; `costAt` (`IselSzSound`, by induction on the fuel; failed match phases
  restore the state) is sound given `ExtW` (extern constructors) and `OracleW`. Two
  instantiations (`IselSzExt`, tables `szCTab`/`tgCTab` in `IselSzTab`, 699/701 entries, generated
  by `FVTest/Backend/IselSzGen.lean`, checked by leaf-wise `decide +kernel`): weights (`actorW`: an `emit`ted
  instruction of a variant other than `Call`/`CallInd`/`JTSequence` weighs at most `emitK = 107`,
  `load_constant_full` 4 of them, `gen_return` a `Rets` of at most 8 registers) and branch targets
  (`actorT`: per variant, none for `JTSequence`). By hand (`IselSzCall`, `IselSzBrTable`): the call
  rules 1031–1033 and `try_call` rules 1034–1036 (stores of the stack arguments, a GOT load, the
  call: at most `323 + 125 n` for `n` arguments, `szCallB n = 1200 + 125 n`) and `br_table` 1140
  (`JTSequence`: a word and a target per entry; sub-runs from the table). Contract: a statement's
  run at most `stmtSzB` (`szStmtK = 1200`; the table's maximum is 1070), a terminator's at most
  `termSzB` (`szTermK = 600`, a `br_table` `1500 + 2 (1 + |table|)`) and `termTgB` targets (2, a
  `br_table` `2 + |table|`); rule 1140 never matches another terminator (`br1140_unmatch`, its root
  format).
* **`lowerFunction` (`size_lower`).** Summing the runs over the blocks, with the entry `Args` and
  parameter loads, the result `mov`s, the `tryCall` replacing a `try_call`'s call (one word more,
  a target per successor) and the edge blocks: `maxRC vc ≤ mIn f`, `vcW (mIn f) vc ≤ vcIn (mIn f) f`,
  `vcTg vc ≤ tgIn f`. `vcW M` charges per block a prologue, the callee-saved saves, `10 M` entry
  stores and 40 words per branch argument.
* **`prepare` and the spill allocation (`SizeVC`).** `vcW_prepare`: at most one edge block
  (`jumpBW M`) per branch target; `spillWordBound_le`: `spillWordBound vcp ≤ vcW (maxRC vcp) vcp`.

```lean
theorem E2E.spillSizeOkB_of_sizeOkB (hs : lowerScopeB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) :
    spillSizeOkB vcp = true
theorem E2E.backend_correct_final_total_emit_input (hsub : InSubset p f) (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true) (hw : extendsWidenB f = true)
    (hsz : sizeOkB f = true) (hl …) (hp …) (ra : Except String RFunc) :
    -- the conclusion of backend_correct_final_total_emit
```

Every premise on the code is now an input condition. Non-vacuity:
`E2E.backend_correct_final_total_emit_input_witness`. `lean-e2e-check` counts `sizeOkB` ("sizeOkB"
line: 1149 of 1149; the largest bound, 11.7 M words for the 9001-statement `large_frame`, against
279 k words of the actual spill code). The bound is linear in the statements (about 1300 words
each), so a function of more than about 12 000 statements is out of scope.

**Lowering and `prepare` totality (V7, #226)** (2026-10-16, `FV/Backend/Proof/LowerTotal*.lean`,
`FV/Backend/Proof/IselPrg*.lean`, `FV/Backend/Proof/PrepareTotal*.lean`,
`FV/E2E/LinkScopeInput{Defs,}.lean`, `FV/E2E/TotalInput.lean`). `lowerFunction` and `prepare`
succeed on decidable input conditions; `InScopeP`'s `lowersB` (which ran them) follows.

* **The driver (`Driver.lowerFunction_ok`).** Every failure path of `lowerFunction`
  (`FV/Backend/Isel.lean`) is excluded by a hypothesis (the list in `LowerTotal.lean`'s header):
  the scope conditions of `fnScopeB`, the new `driverInB` (AAPCS64 convention, at most 8 returns,
  `stmtInB`: result counts, declared AAPCS64 callees and symbols, `tls_value` offset 0, `i64` load/store addresses, no
  `i128` return in `call_indirect` signatures; `termInB`: successor blocks exist, the `try_call`
  table rules — declared `system_v` signature with at most 8 returns and no `i128`, no `context`
  items, `retN`/`exnN` placement, callee signature = table signature), and the ISLE side as
  `IselProg f ctx` (`StmtProg`: a statement's `lower` returns one register per result;
  `TermProg`; `TryProg`: a `try_call`'s code ends in its call).
* **The ISLE side (`Prg.iselProg_of_input`).** A progress analysis of the exported rules: the
  abstract domain `PA` (`IselPrgDom`), abstract models of the extern helpers sound under the
  context invariant `PInv` (`aext_sound`, `actor_sound`, `aidata_sound`, `ofvOk_sound`), the
  abstract interpreter's soundness (`progress`), a summary table for every internal term reachable
  from the statement and terminator roots (`IselPrgTab`, 1006 entries, generated by
  `FVTest/Backend/IselPrgGen.lean`, `prgTab_ok`/`stmtRoots_ok`/`termRoots_ok` by leaf-wise
  `decide +kernel`; the largest fuel an entry needs is 521) and two rules by hand (862/863 and
  `extr_32_or_64`: they rely on a relation of two matched constants the interval domain drops).
  `PInv` comes from `lowerScopeB`, `dominatedB`, `extendsWidenB` and `iselInB` (callee,
  `call_indirect` and `try_call` signatures pass `sigOkB` — argument locations and at most 8 ABI
  returns —, `func_addr` names a declared callee, `stack_addr` a frame slot, `return` arity, at
  most `maxTryItems` = 8 exception-table items).
* **`prepare` (`Prep.prepare_ok`).** No new condition: `prepare` succeeds on `lowerFunction`'s
  output (`dominatedB`, `lowerScopeB`); the cleanup pipeline's `prepare (prune vc)` from
  `prepare vc` (`prune_prepare_ok`).

```lean
theorem Backend.Proof.Prg.lowerFunction_ok_input (hE : Compile.functionE f = true)
    (hsig : sigAbiOk f.sig = true) (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hw : extendsWidenB f = true) (hdrv : driverInB f = true) (hin : iselInB f = true) :
    ∃ vc, lowerFunction f = .ok vc
theorem Backend.Proof.Prep.prepare_ok (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (hl : lowerFunction f = .ok vc) : ∃ vcp, prepare vc = .ok vcp
def E2E.LinkCheck.fnScopeInB (g : Clif.Function) : Bool   -- fnScopeB, lowersB replaced by
                                                           -- extendsWidenB, sizeOkB, driverInB, iselInB
def E2E.LinkCheck.addrSlotsInputB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  -- addrSlotsInB without outAreaB (L1g #228): no indirect call, or the functions with an
  -- address have no stack slots, or a program callee has slots (declSlotsB)
  P.funcs.all indFreeB || P.funcs.all (fun h => (S h.name).isNone || h.slots.isEmpty) ||
    declSlotsB P
def E2E.LinkCheck.progScopeInB (P : Clif.Program) (S : String → Option Nat) : Bool
                                                           -- progScopeB, addrSlotsInB replaced by
                                                           -- addrSlotsInputB
def E2E.LinkCheck.InScopeIn (I : LinkInput) : Bool :=
  progScopeInB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeInB
theorem E2E.LinkCheck.lowersB_of_input … (hw : extendsWidenB f = true) (hsz : sizeOkB f = true)
    (hdrv : driverInB f = true) (hin : Prg.iselInB f = true) : lowersB f = true
theorem E2E.LinkCheck.fnScopeB_of_input (h : fnScopeInB g = true) : fnScopeB g = true
theorem E2E.LinkCheck.addrSlotsInB_of_input (h : addrSlotsInputB P S = true) :
    addrSlotsInB P S = true
theorem E2E.LinkCheck.progScopeB_of_input (h : progScopeInB P S = true) : progScopeB P S = true
theorem E2E.LinkCheck.inScopeP_of_input (h : InScopeIn I = true) : InScopeP I = true
theorem E2E.backend_correct_final_total_input (hsub : InSubset p f) (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true)
    (hent : Spill.entryParamsB f = true) (hw : extendsWidenB f = true) (hsz : sizeOkB f = true)
    (hdrv : driverInB f = true) (hin : Prg.iselInB f = true) (ra : Except String RFunc) :
    ∃ vc vcp, lowerFunction f = .ok vc ∧ prepare vc = .ok vcp ∧
      -- the conclusion of backend_correct_final_total_emit_input
theorem E2E.backend_correct_final_cleanup_total_input …  -- prepare (DeadCleanup.prune vc)
```

`inScopeP_of_input` converts every theorem taking `InScopeP` (`DeadCleanup.compileExe_total_reach_input`
above, `Link.compileExe_spec`; `crate_correct_inScope*`); the correctness theorems on `compileExe`'s output take its
success, which the totality theorems give. Non-vacuity: `driverInB_witness`, `iselInB_witness`,
`backend_correct_final_total_input_witness` (`fnScopeInB` of the loop and `try_call` witnesses,
kernel-checked, `dominatedB` as premise: its fixpoint uses `Std.HashMap`, which the kernel does
not reduce). `lean-e2e-check` decides both per-function scopes ("per-function scope" line; a
disagreement fails the run): 1150 / 1150; `lean-link --verified` checks `fnScopeInB`.

**Validator completeness: `Opt.Legalize128` is correct without `Opt.Legal.check`** (2026-10-02,
`FV/Opt/Proof/LegalComplete.lean`, `FV/Opt/Proof/LegalDirect.lean`, `FV/E2E/LegalDirect.lean`;
`docs/contracts/legalize128.md` "Completeness"): `Opt.Legal.Complete.check_complete` (`Pre f` and
`function128Cert f = .ok (g, cert)` ⇒ `check f g cert = true`), hence
`Opt.Legal.legalize_refines` and `E2E.backend_correct_legal_direct` (`backend_correct_legal`
with `hpre`/`hlg` in place of `hchk`).

The proof follows `prepare` step by step. `reachable` (fuel-bounded worklist) marks a set that
contains the entry, is closed under successors, and is reachable from the entry
(`reachable_spec`; termination by the measure "queued + unmarked"). The kept blocks keep their
labels, with the entry first. Edge splitting retargets a terminator only to the old label or
to a fresh edge label (above every kept label) whose block jumps to the old one (`SInv`,
`innerFold`). `rpo` (fuel-bounded DFS) lists each block reachable from the entry once, entry
first, closed under successors (`rpo_spec`; termination by the potential "stack frames' unvisited
successors + unmarked blocks' weights" against the fuel `1 + Σ (|succs b| + 1)`). Reachability is
carried across the three CFGs by label (`reach01`, `reach12`).

Results with `sret` (2026-09-30, after merging main with the `i128` legalisation): `lean-e2e-check`
1076 accepted / 0 rejected / 149 out of scope, `prepCheck` 1076 / 0, `formsCoveredB` 1076 / 0
not covered (main: 1070; the 6 new are `corpus/clif-regress/sret.clif`: `sret` functions with
the pointer first, after a normal parameter, and returned from several blocks, and callers of
`sret` externs — the default corpora contain no other `sret` function). On the Rust fixtures
(`scripts/rust-clif/fixtures/sret.clif`, `smoke-data/f_crypto.norm.clif`): 20 accepted / 0
rejected / 0 not covered. Filetests: corpus 114/114, extrt 22/22, runtests 4672 pass / 0 fail /
0 disagree, `sret.clif` 5/5 agreeing with Cranelift-native; encode-check 1271 identical / 0
differ.

Results (`lake exe lean-e2e-check`, corpus/clif, corpus/clif/extrt, Cranelift runtests): both
validators accept 913/913 functions inside the theorem (with `brIdxOk`: no `br_table` rejected);
19 functions are outside `InSubset`: 14 with more than 8 parameters, and since contract change
#5 the 5 corpus functions calling an extern with more than 8 parameters (`Corpus__reverse8_w0/_w1`,
`Corpus__bumpAll_w0/_w1`, `Corpus__bumpFirst`; still compiled, flagged unverified). Filetests after
#5/#6 (M4Ctl, `scripts/lean-backend-filetests.sh`): corpus 114/114, extrt 22/22, runtests 3085
pass / 0 fail, all agreeing with Cranelift-native. Cost on the corpus (161 functions): `lowerFunction` 175 ms, `lowerCheck`
661 ms, `prepare` 2 ms, `prepCheck` 3 ms (the lowering validator re-runs isel; functions outside
the theorem are not validated). Since the near-linear certificate check (agent/trycall-proof;
it replaced list-based checks and a round-based dataflow that recomputed predecessor lists per
value, 23 s per round on a 283-block function): a survey test function with 325 blocks, 1354
statements and 1057 values, over an hour before, validates in 0.17 s (dataflow 18 ms,
certificate 16 ms, the rest re-running isel and the shape check); on the corpus and the
runtests (1105 functions) the new validator computes the same alias resolution and entry
values and accepts exactly the same functions as the old one. `lean-backend` does not run it on
functions over the validation budget (`Backend.validationBudget`: instructions × values above
25000000, 7.6 times the largest function of `examples/`), which it compiles and reports as
`compiled, unverified (validation budget)`.

**Functions outside the theorem** (`FV/Backend.lean` `unverifiedReason?`: outside
clif-subset-v2 E and its typed scope, calls (also `try_call`s) of functions of the same file, special-purpose parameters other than one `sret` pointer (`abiSigs`), indirect calls
with more than 8 parameters or special-purpose parameters (`indSigsOk`)) are still
compiled, without validation, and reported as unverified (`FileAsm.unverified`; `lean-backend`
prints `compiled, unverified (outside backend_correct): …`).

**The typed scope (S11e5 Stage C).** A function outside subset E is inside the theorem when
it is in the typed scope (`Backend.verifiableT`: `Compile.functionET` — float parameters,
returns, block parameters, loads, stores, constants, `select`, `bitcast` — with
`Compile.storeTypedB`, `abiSigs`, `indSigsOk`); its lowering is validated by the typed
validator `lowerCheckT` (`Backend.lowerCheckFor`: `lowerCheck` on subset E, `lowerCheckT`
outside it; `lowerCheckT_of_lowerCheck`), and the theorems are `backend_correct_finalT`/
`backend_correct_final_cleanupT` with `E2E.typedRules_program` (returns by class,
`ArmRefinesT`). `FV/E2E/VerifiableT.lean`: `InSubsetT.of_verifiableT`,
`verifiable_or_verifiableT_of_unverifiedReason`, `lowerChecked_spec`; witness
`FVTest/E2E/FloatVerifiedW.lean`. Float arithmetic (`fadd` …, `fcmp`, conversions) stays
outside (`functionET` has no arithmetic). The Stock routes are integer-only (their eligibility
requires `i32`/`i64` signatures and bodies): on a typed function they produce `lowerFunction`'s
code, accepted only by `lowerCheck` (which implies `lowerCheckT`, `lowerCheckT_of_lowerCheck`) or,
as the last retry, by `lowerChecked`'s `lowerCheckT`.
`lean-link --verified` was integer-only (decision 2026-10-22) because its claim reaches the Rust
source through front-end theorems (`Front.bundle_correct_raw*`) that existed only for integers.
Since S11e6 (#419) the typed versions exist and `--verified` widens to the typed input scope
(cleanup compiler, no `--opt`, no self tail calls): an input whose functions all meet
`fnScopeInTB` (`InScopeInT`) but not all `fnScopeInB` is compiled by
`Link.DeadCleanup.compileExeT`, covered by `compileExeT_correct{,_peak}`,
`compileExeT_correct_source{,_peak}` (`FV/Link/DeadCleanupExePeakT.lean`,
`FV/Link/DeadCleanupExeSourceT.lean`) and `Front.bundle_correct_{source,raw}{,_peak}T`
(`FV/Front/ExeT.lean`), returned values by class (`ExecRefinesT`); totality stays proven on
`InScopeIn` only, and the exceptional edges (`compileExeU`) are integer-only. The functions failing
`fnScopeInTB`, `fnScopeTB` or the typed output checks `outChksT` are left out of the region
(`lean-link`'s `exclude:` line). Witnesses: `FVTest/Link/FloatCompileExeT{Peak,Source}.lean`,
`crate-proofs/Crates/FrontendBundleWitnessT.lean`.

**Typed `--verified` on the Stock route (#722).** The units hold the code `lean-backend` wrote:
the Stock routes (Cranelift's code) on a function without `try_call`, `lowerFunction` on the
others and where the Stock lowering fails. `compileExeT` lowers every function with
`lowerFunction`, so where the two differ (`stockDiffersB`, #691) its layout is not the region
reserved. Since #722 `lean-link` then compiles the typed input with
`Link.SemanticCompilerWith.attemptT routes[0]! (SC0.placedProductionWith routes[0]! true)`
(`FV/Link/SemanticCompileT.lean`): the Stock route's pipeline, placement and link
(`leanLinkProductionWith`, so the generated code is the units' and unchanged), accepted by the
typed checks `okRWithTS` ("Typed checker on the Stock route" above). Coverage
`attemptT_correct{,_depth,_peak}` and, on the original program in `SrcScopeB`,
`attemptT_correct_source{,_peak}` (`FV/Link/SemanticExeSourceT.lean`), conclusion
`ExecBytes.ExecRefinesT` (returned values by class); totality stays proven on `InScopeIn` only.
When `attemptT` fails, `lean-link` prints the failing functions with their conditions
(`typedStockFails`; `cargo fv` repeats lean-link's `--verified:` lines) and leaves out of the
region only those functions when they are fewer than the typed ones and the Stock-lowered ones;
otherwise the #730 exclusion (the smaller of the two sets) applies. Witnesses:
`FVTest/Link/FloatStockCompileT.lean` (an integer Stock function and an `f64` function: the
integer `attempt` fails, `attemptT` succeeds), `FVTest/Link/FloatStockSretT.lean` (an `sret`
function outside subset E, admitted by `RetsX`). `examples/deps`, functions left out of the region
per test executable (all float functions): main 6264b7e3 (`compileExeT` and the #730 exclusion)
52 and 69 in `deps_demo` and `crates`; `attemptT` (ab76e3f0) 7, 14, 16, 16, from `OkT.sretE`
and the integer program call sites; with `RetsX` (8507435d) 4, 6, 6, 6, all from the program
call sites (`calleeInt`: a program callee returns `f64`; `callRegs`: a program call passes or
reads `f64`; #742). 4 of 4 executables verified by `binary_correct_exec_provenTS`. fv-demo,
`cargo fv test --build-std --lean-link --verified` (8507435d): both test executables written by
`attemptT` and verified (2 of 2), 39 and 40 functions left out (`compileExeT`, #616: 52 and 53),
by cause `callRegs/blrRegs` 28, `calleeInt` 6, `indScope/indSig` (indirect calls of program
functions with float signatures) 8 and 9, all #742.

**Program calls by class (#742).** A call of a function `h` of the program (`bl`, `blr` through
the GOT or an indirect call) passes its arguments in `h`'s parameter registers by class
(`regLocs`: x0..x7 and v0..v7) and takes `h`'s results from its ABI return registers by class,
`E2E.LinkCheck.sigRetRegs h.sig` (Cranelift's `compute_arg_locs` on the returns: integers in
x0.., `f32`/`f64` in v0.., the struct pointer of an `sret` signature without returns in x0;
x0.. for integer returns, `sigRetRegs_int`). The typed link (`FV/E2E/LinkArmT.lean`) reads them
through `LinkSys.progXT`/`LinkSys.XT` (`progX`/`X` with `sigRetRegs` in place of x0..; the
integer link keeps `progX`), and `LinkSys.OkT` is widened in place: `callRegs`/`blrRegs` take
vregs of either class (`argPairsC`/`callDefsC`) and defs in `sigRetRegs`
(`(Dc.map (·.1)).take (sigRets h.sig).length = (sigRetRegs h.sig).take Dc.length`), `calleeInt`
is gone (the callee's `RetsOkT` gives its result registers, `RetsOkT.reg_at`), and `indSig` no
longer has the returns conjunct (an indirect call enters a function only under `IndSigMatch`,
which gives as many ABI returns, `IndSigMatch.sigRets_length`). The integer checkers' facts give
the new fields (`callRegsC_of_int`, `LinkSys.blrRegsC_of_int`, with their "calleeInt" check);
`okRWithTS` checks the class-aware form directly (`linkChksTS`: `siteOkC`/`blrOkC`, `indBC`;
`siteOkC_sound`, `blrOkC_sound`). Generated code is unchanged. Witness
`FVTest/Link/FloatLinkCallsT.lean` (`%f`, `%h` calling `%g (f64) -> f64` by `bl` and by `blr`
through the GOT, `f64` arguments and results in v0; `okBTS` and `attemptT` hold). Measured
(#748 on 719f226f): `examples/deps`, `cargo fv test --lean-link --verified`: 0, 0, 0, 0 functions
left out of the region (before: 4, 6, 6, 6), 4 of 4 executables verified, tests pass. fv-demo,
`cargo fv test --build-std --lean-link --verified`: 2 of 2 verified, 17 and 18 left out (before:
39, 40), none a float function: 10 integer functions fail `callRegs/blrRegs` at vtable `blr`s
checked against GOT-declared callees with a different `sret` placement (#753); the other 7 (8)
failed only the integer route's `indB:sretRets`, which `lean-link` added to the typed failures.
Since #754 the typed Stock route's exclusion list is the typed failures alone (`exclusions`'
`only`: `attemptT_correct` has no per-function input premise). `indBC`'s at most 8 parameters
excludes nothing on either example.

## Contract changes taken (byte-identical)

`FrameTyped` conjunct of `DFGCons` (M4AluA f55011e), `ValsBelow` premise + `Refines` over every
control (M4Cmp 1a4de60), M4AluB 1532afa (`CtxInv.defClif`, ispec forms), first-match premise of
`LowerRuleOk` (M4AluB c696bfa, change #3), hand-written `LawfulBEq V` (M4Cmp 4de7914, change #4).
M7's own `IselContract` change: 0770fd7 (terminator statements; `BranchRuleOk` premises).
M4Ctl, integrator-approved: change #5 38600e8 (calls: `CallsRefine`, `CallRuleOk`/
`CallRulesCorrect`, `LowerRulesCorrect` excludes `callRootRule`, `InSubset.callRegArgs`,
`DriverHyp.regArgs`, `InstCalls` premise `CallRegArgs f`, ispec control forms); change #6
(`BrIdxTyped` premise of `BranchRuleOk` and `TermCalls`, decided by `lowerCheck`'s `brIdxOk`,
`LoweringObligations`/`DriverHyp.brIdx`).
agent/stack-tls-proof (stack arguments): `CallsRefine`'s call/try-call clauses take `ArgsAt`
(stack-passed arguments read from memory at `sp + off`) instead of "at most 8 values, all in
registers"; `CallRuleOk` takes the outgoing area `outB` with `SigStackOk` and `CallRulesCorrect`
also `MemRefines` and `OutArgsOk` (stores into `[sp, sp + outB)` keep `MR`); `CallsRegArgs` and
`DriverHyp.regArgs` are replaced by `CallsStack f vc.outgoing` (decided by `lowerCheck`'s
`callsStackOkB`) and `DriverHyp.tryRegArgs`/`entryLocs`; `InstCalls` takes "statement of `f`";
`IselSim` takes `ArgsAtEntry` (stack parameters at `fp + 16 + off`); `MemRefines`'s memory forms
include `spOffset`/`fpOffset` (M6: `amodeAddr`, `corr_load_sp/fp`, `os_load_sp/fp`).
agent/stack-tls-proof (`tls_value`): `MemRefines` has a ninth clause (TLSDESC: the address of a
linked symbol in the first def, a world agreeing up to the flags); `memRootRule` adds 1129/1130;
`ExtSem` gains `tp` and `tlsFlags`; `ArmHooks` gains `tls`; `Masked` includes x30; `RunsAs`
quantifies the step count; `realizes_all`/`regLevelCorrect_backend` take `TlsOk` for VCode with
an `ElfTlsGetAddr`; `lowerCheck`/`prepCheck` gain the `hasTls` conjuncts.
M6Ctl3 (compiler, behaviour-preserving): `ctlCheck` also requires every value of a `Rets` to be
an int vreg (so the `j`-th returned pair is the `j`-th fixed use); `lean-backend` on corpus,
extrt and runtests (445 files): no function rejected.

## Callee traps (S9a, #33)

`TrapsExplicit` (the run premise of every per-function theorem) lets a statement trap only if it
is an explicitly trapping instruction. A `call`/`call_indirect` whose callee traps (a trapping
`__*ti3` helper, a panic: `Clif.Rust.env`'s panics trap with `user1`, a callee of the linked
program that traps) is therefore outside every theorem. S9a covers it per function, for the
shipped compiler (`FV/E2E/DeadCleanupTrapCall.lean`):

```
E2E.backend_correct_final_cleanup_trapcall
  (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
  (hlU : lowerCheckU f vc = true) (hp : p.funcs = []) (hft : ∀ B ∈ f.blocks, B.term.isTry = false)
  hcov hC hTls hX hXI                                  -- as backend_correct_final_cleanup
  (hXT : ∀ s, XTrapsOk env (f.externs.map (·.2)) (indSigs f) (Rel.holds … s …) X)
  hsym hslot hent hres hbe hargs hcs hrel
  (htr : TrapsExplicitC env p cs) (hrun : Clif.runLoop env p fuel cs = .trapped c) :
  ∃ n, TrapAt fb base c (runX (ArmStepX X H fa) n s) ∨
    (CallTrapAt vcp (frameW … s) K (fun _ => False) s fa base X (fun _ _ => False)
        (TrapCallSem env (f.externs.map (·.2)) (indSigs f) (Rel.holds … s …) X c)
        (runX (ArmStepX X H fa) n s) ∧
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K (fun _ => False) (fun _ _ => False)
        (runX (ArmStepX X H fa) i s))
```

* **Premise** `TrapsExplicitC` (`FV/E2E/TrapCallClifRun.lean`): `TrapsExplicit` whose statement
  clause also allows a `call`/`call_indirect` (`CallInst`; such a step traps only inside its
  callee: the preludes `callArgs`/`indPre` never trap). `TrapsExplicit.toC`: the old premise
  implies it.
* **Conclusion**: the machine reaches a trap site of `f` with the code, or a **callee-trap state**
  (`CallTrapAt`, `FV/E2E/RegLevelTrapCall.lean`): the pc at the call line of a `call` of `f`,
  the callee contract's premises (`RL.CallPre`'s: dead stack, operand checks, the world `w`, `sp`
  aligned, no error, GOT guard) and `TrapCallSem … c` on the call's operand values and `w`: the
  machine semantics `X.call` gives no normal return and the CLIF semantics of the called extern
  (direct, or the extern at the callee address) traps with `c` on the arguments held there and a
  memory related to `w`. Every earlier state of the activation is `GoodX` (the trace facts the
  linking and executable layers use).
* **Trapping callees' contract** `XTrapsOk`: where an extern's CLIF semantics traps (arguments
  and memory related as in `XCallsOk`), its machine semantics `X.call` is `none` — the outside
  code does not return there (a `__*ti3` helper with divisor zero, a panic). It holds trivially
  for callees that never trap (`xTrapsOk_of_noTrap`).
* **Scope of S9a**: functions without `try_call`/`try_call_indirect` terminators, in a program
  without functions (`p.funcs = []`, the per-function theorems' `p.bare` in the linked
  theorems), whose lowering passes the unwinding validator `lowerCheckU` (decided by
  `lean-link` as `unwOkB`).
* **Proof**: the proof device `trapEnv env c` (`FV/E2E/TrapCallClif.lean`) turns a callee trap
  with `c` into an exception (`trapExn`) of the run with unwinding. `trapEnv_of_trapped`: for a
  run of `f` that traps with `c` under `TrapsExplicitC`, `trapEnv`'s run with unwinding satisfies
  `TrapsExplicitX` and traps with `c` or ends with an exception (`step_trapRel`: a step of
  `trapEnv`'s environment is `env`'s except at a callee trap with `c`, where it is `stuck` and the
  step with unwinding raises, `raiseAt_of_trapRel`; reachability and determinism of the run,
  `reachX_trapEnv`, `trapped_det`). The unwinding chain then carries the exception: CLIF → VCode
  by `iselSimU_of_driver` (with the raising semantics `xrT XT` of the trapping callees and its
  contracts `xRaiseOk_trapEnv`/`xRaiseIndOk_trapEnv`, the normal-return contracts transferred by
  `xCallsOk_trapEnv`), `prune` + `prepare` by `prepareCorrectU_cleanup_value`, and the register
  level on the machine **without** unwinding by `regLevel_trapCall_value`
  (`regLevel_trapCall_core`: `forward`/`forward_last` to the halting call, `realizes_trapT`:
  the value realiser transfers to the semantics whose trapping calls halt).
* **Non-vacuity** (`FV/E2E/DeadCleanupTrapCallWitness.lean`): `final_applies` applies the
  theorem to a compiled function calling a `%panic` that traps (`checks_true` receipt); on its
  entered state `cs0` the run traps with `user1` inside the callee, `cs0_trapsC` (the new
  premise holds), `cs0_not_trapsExplicit` (the old one does not), `cs0_unwinds` (the device).
* **Inside a linked program** (`FV/E2E/WorldTrapCall.lean`, the first step of S9c #376):
  `backend_correct_world_cleanup_trapcall`, the same for an activation with the memory relation
  `RelW`, the kept addresses `G` and the GOT pins `GotV vcp` (`ActEntry`, what `LinkArm`'s
  induction applies per function; `backend_correct_world_cleanup`'s trap half widened), by
  `iselSimU_relW_cleanup` and `regLevel_trapCall_world`; witness `world_applies`.
* `#print axioms` (list `scripts/audit/traps.lean`): `backend_correct_final_cleanup_trapcall`,
  `backend_correct_world_cleanup_trapcall`, `regLevel_trapCall_value`, `regLevel_trapCall_world`,
  `trapEnv_of_trapped`: `[propext, Classical.choice, Quot.sound]`.

### Callee traps in the linked program (S9c, #376)

`FV/E2E/LinkTrapCall.lean`, `FV/E2E/LinkTrapCallInd.lean`: the trap counterpart of `LinkArm`'s
induction. The linked hook of a program callee that does not return gives `junkAt` (an error
state), so on the linked machine a callee trap is a run that **stops**:

```
E2E.backend_correct_program_trap_budget (L : LinkSys) (hL : L.Ok) (hT : L.TrapsOk)
  (hB : L.BaseTrapsOk) (hκ : L.Budget κ) (hf : f ∈ L.P.funcs) (M : Nat)
  hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl      -- as backend_correct_program_budget
  (htr : L.std.TrapsD M f cs) (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped c) :
  L.TrapIn M f s c
```

(`backend_correct_program_trap`: the budget `L.K M`; `_peak`: depth `d` of the run of fuel `F`,
`(L.peak F).TrapsD d f cs`; `_core`: any callee runs, `LinkSys.CrunOk`.)

* **Observable** `TrapIn L M g s c` (inductive): the run of `L.mach M g` from `s` stops at step
  `n` (`Stop`: no error there, the body's `sp`, no return into `g`'s own code before
  (`PostTrace`), every later state errs) at a trap site of `g` with `c` (`site`), at a call of `g`
  whose callee outside `P` traps with `c` in its CLIF semantics (`base`, `BaseTrapCall`), or at a
  call of `g` of a function `h` of `P` (return address allowed for `h`, `RaOk`; the call state's
  facts `ProgCallOk`: `h ∈ P`, the code image intact, a `blr` through a register other than `xzr`
  by which `g` may enter `h`, what the executable's call step needs) whose activation entered
  from that call state has `TrapIn` one level down (`prog`). `noRet_of_stop`,
  `pcall_junk`: a stopping callee never returns to its caller, so its linked call is `junkAt`.
* **Run premise** `TrapsD L M g cs` (`TrapsExplicitC` of the linked program, by depth):
  `TrapsExplicitC` of the activation under `linkEnvR` (no memory-access trap) and the run under
  `envR` traps as it does with the program callee traps outside the premise one level down made
  stuck (`cutEnv`): every callee trap the run hits is one of an activation satisfying `TrapsD`.
* **Premises**: `TrapsOk` (decided by the compiler: every function `CompiledCleanup`, passing
  `lowerCheckU`, without `try_call` terminators); `BaseTrapsOk`, the outside code's trap contract
  (next to `BaseOk`): `XTrapsOk` of the base externs, the base hook errs at a call whose base
  callee traps (`stop`), the base hooks keep an error state (`err`, `tlsErr`; `hooks_err`: then
  so does the linked machine).
* **Proof** (`thmT_of`): the per-function theorem `backend_correct_world_cleanup_trapstop`
  (`FV/E2E/WorldTrapStop.lean`: `backend_correct_world_cleanup_trapcall` with the trace, the
  final `sp`/program and, at a trap site, the errors after it) under the activation's
  environment with the uncovered callee traps stuck; its trapping callees' contract
  `LinkSys.xTrapsOk`: for a program callee, `progX = none` because the callee's activation from
  the canonical state has `TrapIn` (`progCallT`, from `ThmT (M - 1)`) and so does not return
  (`progX_none`). At a callee-trap state the call goes outside `P` (`BaseTrapsOk.stop`) or to a
  function of `P` entered from the actual call state (`progCallT` with `CallerOk` from the call
  site's registers, `blSite`/`blrSite`; every caller state with its own body-entry world, no
  non-interference needed).
* **Non-vacuity** (`FV/E2E/LinkTrapCallWitness.lean`): `P = {f, h}`, `f` calls `h`, `h` is
  `trap user1`, compiled by the shipped pipeline (`chk_true` receipt); `program_trap_applies`
  (every premise but the entry state's); `f`'s run on `41` traps inside `h` (`run_traps`),
  `cs0_trapsD` (the new premise holds), `cs0_not_trapsExplicit` (the premise of
  `backend_correct_program_budget` does not).
* `#print axioms` (`scripts/audit/traps.lean`): `backend_correct_program_trap{,_budget,_peak,
  _core}`, `LinkSys.thmT`, `backend_correct_world_cleanup_trapstop`: `[propext,
  Classical.choice, Quot.sound]`.

### Callee traps on the executable and in the bundle theorems (S9d, #377)

`FV/E2E/DeadCleanupExecTrap.lean`, `FV/Link/DeadCleanupExeTrap.lean`, `FV/Front/RawExeTrap.lean`:
`TrapIn` carried to the executable machine `step I B file`.

```
Link.DeadCleanup.compileExe_correct_trap (h : compileExeU S file0 = .ok file) (B : BaseEnv)
  (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
  (hBT : (sys S.inputCleanup B).BaseTrapsOk)
  (hnoTry : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ b ∈ g.blocks, b.term.isTry = false)
  hf hc M hX ho hr                                  -- as compileExe_correct
  (htr : (sys S.inputCleanup B).std.TrapsD M f cs) :
  ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
    (DeadCleanupBinCheck.RelocAt S.inputCleanup) (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs)
```

(`compileExe_correct_trap_peak`: the run's peak call depth `d`, `((sys …).peak F).TrapsD d f cs`;
`compileExe_correct_source_trap{,_peak}`: the original pre-legalisation program's trap, the
`__*ti3` helpers being base externs covered by `BaseTrapsOk`; `Front.bundle_correct_source_trap
{,_peak}`, `Front.bundle_correct_raw_trap{,_peak}`: cg_clif's program, as `bundle_correct_raw`.)

* **Observable** `ExecRefinesC`: a return as `ExecRefines`; a trap with `c` is a state of the
  executable's run with `TrapAtE … c`: at a trap site with `c` of **any** compiled function of
  the program, or at a call of a compiled function whose callee outside the program traps with
  `c` (`LinkSys.BaseTrapCall` of a model state the executable state simulates: the same registers,
  the same bytes but at relocated instruction bytes). `ExecRefines.toC`: the old clause implies
  it.
* **Executable** `compileExeU` (`compileExe` with the unwind tables checked, what `lake exe
  lean-link` decides): it decides `lowerCheckU` of every function (`lowerU_of`), which the
  per-function trap theorem needs. Run premise `TrapsD` in place of `TrapsExplicit`; for a return
  the old theorem applies (`TrapsExplicit` of a returning run, `trapsExplicit_of_run`).
* **Proof** (`exec_of_trapIn`, induction on `TrapIn`): each level's run is simulated up to its
  stop state (`act_simN`; `RunOkSN` from `Stop.good` with no GOT slot in `leanLink`'s output,
  `runOkSN_of_good`; no return before the stop state from the entry's return address (top level,
  `no_return`) or `noRet_of_stop` (nested)); a trap at the second word of an `adrp` pair as in
  `exec_of_modelN`; a call word is no second word (`not_second_callPc`); at the call of a trapping
  program callee the executable's `bl`/`blr` enters the callee (`call_enter`, with `StepOkD` at the
  call state from the call line and `ProgCallOk`: `stepOkD_progCall`), whose activation has the
  observable one level down. The model's observable comes from `backend_correct_program_trap_budget`
  (`_peak`) for `LinkSys.ofInputCleanup` with the outside call's exterior (`trapsD_F`,
  `baseTrapsOk_F`: the premises do not read it).
* **Non-vacuity** (`FV/Link/DeadCleanupExeTrapWitness.lean`): `f(x, y) = h(x, y)`,
  `h(x, y) = x / y` (`udiv`) compiled by `compileExeU` into a small static executable
  (`compile_eq`, `native_decide`); with no code outside the program (`closedBase`) `f`'s run on
  `(41, 0)` traps with `int_divz` inside `h` (`run_traps`), `cs0_trapsD` holds and the old premise
  `TrapsExplicit` does not (`cs0_not_trapsExplicit`); `exec_traps`: every premise of
  `compileExe_correct_trap` discharged but the entry contract (`Image.Intact`, `OutsideCall`,
  `ClifRun`), the run of the written executable reaches a state at a trap with `int_divz`.
* `#print axioms` (`scripts/audit/traps.lean`): every compiler theorem above `[propext,
  Classical.choice, Quot.sound]`.

Not covered here: traps of the callees of `try_call`/`try_call_indirect` (premise `hnoTry`; done
in S9b per function and S9e on the executable, below), memory-access traps (`heap_oob` of a
load/store: no fault model, excluded by
`TrapsExplicitC`) and `MemBounded` of the source run (the bump allocator); the baseline
`Link.compileExe` (its pipeline is not the cleanup pipeline the per-function trap theorem is
proved for).

### Callee traps of `try_call`s, per function (S9b, #375)

`E2E.backend_correct_final_cleanup_trapcallT` (`FV/E2E/DeadCleanupTrapCallTry.lean`):
`backend_correct_final_cleanup_trapcall` without `∀ B ∈ f.blocks, B.term.isTry = false`, under
`TrapsExplicitCT` (`TrapsExplicitC` without its `try_call` clauses; `TrapsExplicitC.toT`);
conclusion: a trap site of `f`, or `CallTrapAtT` (the callee-trap state at a call site of
either kind, `CallTrapAt.toT`), every earlier state `GoodX`. The proof stops at the trapping
call instead of following the device's exception into a handler:

* CLIF (`TrapCallTry.lean`): a `try_call`'s preludes never trap; its callee trap is `stuck` in
  `trapEnv` and raises there (`step_try_trap_stuck`, `raiseAt_of_trapRel_try`);
* CLIF → VCode (`TrapCallTryStop.lean`): `sim_trapStop`/`driver_trapStop`, fuel induction on
  the run of `env`, ending at an explicit trap (`VTrapFrom`), a raising `call` (`VUnwFrom`) or a
  raising `tryCall` (`VTryRaiseFrom`, `term_step_try_stop`);
* `prune`/`prepare` (`TrapCallTryPrep.lean`): `tryRaise_cleanup`;
* register level (`RegLevelTrapCallTry.lean`): `haltTry` (the value semantics halting at a
  raising `tryCall`), `star_haltTry`, `realizes_haltTry`, `regLevel_trapCall_coreT`/`_valueT`
  (the `try_call` contract from the plain call's, `calleeTryOkG_of_call`).

Witness (`FV/E2E/DeadCleanupTrapCallTryWitness.lean`): `%tp`, a `try_call` of an extern `%panic`
that traps with `user1` (a `tag0` handler), compiled by the shipped pipeline (closed receipt
`checks_true`); `final_applies` applies the theorem to it (the trapping callees' contract and the
normal-return contracts discharged; open as in the S9a witness: `hC`, `hsym`, the entry premises);
`source_hasTry` (S9a's theorem does not apply), `cs0_traps` + `cs0_trapsCT` (the run on argument 5
traps inside the `try_call`'s callee and satisfies `TrapsExplicitCT`).

### Callee traps of `try_call`s in the linked program, on the executable and in the bundles (S9e, #408)

The S9c/S9d chain without "no `try_call` terminator" (old theorems unchanged):

* per function, world (`FV/E2E/WorldTrapStopT.lean`): `regLevel_trapStop_coreT` (the register
  level with the stopping state and a third end, a raising `tryCall`; the GOT pins of the reached
  calls from the run, `hgotS`, as `haltTry`'s halting `tryCall` has none), `regLevel_trapStop_worldT`
  (no `vcp.hasTryCall = false`: the `try_call` contract from `ActEntry.tries`),
  **`backend_correct_world_cleanup_trapstopT`** (under `TrapsExplicitCT`, conclusion
  `CallTrapAtT`);
* linked program (`FV/E2E/LinkTrapCallT.lean`): `LinkSys.TrapsOkT` (`TrapsOk` without `noTry`),
  the run premise **`LinkSys.TrapsDT`** (`TrapsD` with `TrapsExplicitCT`), the induction
  `LinkSys.thmTT`, **`E2E.backend_correct_program_trapT{,_budget,_peak}`** with the same
  observable `TrapIn` (its call sites, `CallSite`, are `call`s and `try_call`s). The induction
  pieces of S9c are stated for any run premise (`ThmTG`, `progCallTG`, `progX_noneG`,
  `xTrapsOkG`, `trapIn_callTrapG` at a `CallTrapAtT`); the S9c names are their instances;
* executable (`FV/E2E/DeadCleanupExecTrapT.lean`, `FV/Link/DeadCleanupExeTrapT.lean`):
  `DeadCleanupExecBytes.binary_correct_exec_trapT{,_peak}`,
  **`Link.DeadCleanup.compileExe_correct_trapT{,_peak}`**,
  `compileExe_correct_source_trapT{,_peak}`; bundles (`FV/Front/RawExeTrapT.lean`):
  **`Front.bundle_correct_{source,raw}_trapT{,_peak}`** — S9d's statements without `hnoTry`,
  `TrapsDT` in place of `TrapsD`.

Witness (`FV/Link/DeadCleanupExeTrapTWitness.lean`): `f(x, y)` does `try_call h(x, y)` (a `tag0`
handler), `h(x, y) = x / y`, compiled by `compileExeU` (`compile_eq`); `run_traps` (the run of `f`
on `(41, 0)` traps with `int_divz` inside `h`), `cs0_trapsDT` (the new premise holds),
`cs0_not_trapsD` and `not_noTry` (S9d's premises fail), `exec_traps`
(`compileExe_correct_trapT` with every premise but the entry contract discharged: the executable
reaches a state at a trap with `int_divz`).

## Memory traps of trapping atomics (A3, #412, F4–F7)

`docs/plans/memfault.md`. The trap theorems above take `TrapsExplicit`: no load, store or atomic
traps. cg_clif's `atomic_cas`/`atomic_rmw` carry the default trap code `heap_oob` (every load and
store is `notrap`), and `Clif.run` traps there when the access is outside every live allocation.
Cranelift inserts no check: the trap is the hardware fault of the access. New theorems (old ones
unchanged) take instead the run premise **`TrapsExplicitM`** (a statement traps only explicitly or
at a trapping atomic, `Clif.memTrapInst`; every callee returns) and the memory map premise
**`MapFaults mp`** (every memory trap of the run, `Clif.MemTrapAt … c a n`, has a byte of
`[a, a + n)` that the process's memory map `mp` does not map, `Perm.none`).

**What they claim.** The observable is a state of the run at a trap site of the entry function
with the CLIF code whose instruction errs (an explicit trap's `udf`) or **faults under `mp`**
(`ArmFault.InstFaults`: the `ldaxr x27, [x25]` of the trapping atomic's LL/SC loop, `x25` the
CLIF address). The machines are the existing ones, whose memory is total: the theorems say that
**if** the run reaches the trapping atomic, its `ldaxr` faults under the map; they do **not** say
that no earlier access of the run faults under `mp`. That is F8 (below): the `_memtrapF_rw`
theorems on the fault-aware machine.

* register level (`FV/E2E/RegLevelMemTrap.lean`): the observable `TrapAtM mp fa fb base c` (`TrapAt`
  at a `udf` line, `UdfLine`, or at an `ldaxr` line with an unmapped byte, `LdaxrUnmapped`;
  `trapAtF_of_trapAtM`: on the function's own machine it is `TrapAtF`, the next `stepF` is the
  fault); the proof device `haltLoop` (the VCode semantics with the trapping loop halting,
  `memTrap_halt`, `realizes_haltLoop`), `loop_ldaxr`, **`regLevel_memtrap_world_value`**;
* per function (`FV/E2E/WorldMemTrap.lean`): `iselSim_relW_cleanup_memtrap` (`driver_memtrap`),
  **`backend_correct_worldX_cleanup_memtrap`** (every activation reaches `TrapAtM`, every earlier
  state `GoodX`);
* linked program (`FV/E2E/LinkMemTrap.lean`): the per-state facts before the trap state
  `LinkSys.RunGoodLB n` (the total machine runs on past the `ldaxr`, so `RunGoodL` is bounded),
  **`E2E.backend_correct_program_memtrap_{core,budget,peak}`**;
* executable (`FV/E2E/DeadCleanupExecMemTrap.lean`, `FV/Link/DeadCleanupExeMemTrap.lean`): the
  observable **`ExecTrapM mp I file f c e`** (`TrapAt` of `f`, and the file's instruction word at
  the pc, executed by the processor, errs or faults under `mp`), `ExecRefinesM`; the simulation
  before a step `act_simNB`; `DeadCleanupExecBytes.binary_correct_exec_memtrap{,_peak}`,
  **`Link.DeadCleanup.compileExe_correct_memtrap{,_peak}`**,
  `compileExe_correct_source_memtrap{,_peak}` (the source run's trap without load/store traps,
  `Opt.Legal.NoMemTrap`, which allows atomic traps);
* bundles (`FV/Front/RawExeMemTrap.lean`): **`Front.bundle_correct_{source,raw}_memtrap{,_peak}`**:
  the trap halves of `bundle_correct_{source,raw}{,_peak}` with `TrapsExplicitM ∧ MapFaults mp` of
  the compiled program's run at every fuel in place of `TrapsExplicit`, conclusion `ExecRefinesM`.

Witness (`FV/Link/DeadCleanupExeMemTrapWitness.lean`): `f(a, e, x) = atomic_cas.i64 a, e, x`
compiled by `compileExe` (`compile_eq`); `run_traps` (the run on `(0, 1, 2)` traps `heap_oob`),
`cs0_trapsExplicitM`, `cs0_mapFaults` (the map `nullMap`: nothing mapped below 4096, the null
page), `cs0_not_trapsExplicit` (the old premise fails), `exec_traps` (`compileExe_correct_memtrap`
with every premise but the entry contract discharged). `#print axioms`: `scripts/audit/memfault.lean`.

### No earlier access faults (F8, #443)

`FV/E2E/DeadCleanupExecMemFault.lean`, `FV/Link/DeadCleanupExeMemFault.lean`,
`FV/Front/RawExeMemFault.lean`. The executable machine with faults `stepF mp I B file`
(`FV/E2E/DeadCleanupExecFault.lean`: its processor steps are `ArmFault.execF mp`, a step whose
access has a byte `mp` does not allow errs with `ArmFault.memFault`; the hook steps of outside code
are unchanged) and the observable **`ExecTrapF mp I B file f c r`**: the run of `stepF mp` from `r`
reaches, with **no faulting step before it** (`NoFault`: each earlier step is the step of `step`),
a state with `ExecTrapM … c`, and its step there errs. Theorems (trap halves; the returns are the
old theorems'): `DeadCleanupExecBytes.binary_correct_exec_memtrapF_rw{,_peak}`,
**`Link.DeadCleanup.compileExe_correct_memtrapF_rw{,_peak}`**,
`compileExe_correct_source_memtrapF_rw{,_peak}`,
**`Front.bundle_correct_{source,raw}_memtrapF_rw{,_peak}`**.

**The premise `MapRelRW mp I f N r args cm` assumes every entry CLIF byte read-write**: every byte
`mp` does not allow to be **written** lies outside the reserved stack (`N` bytes below `r`'s `sp`),
the stack arguments and every allocation of the entry's CLIF memory `cm`, and the program's code is
readable. Read-only data objects (`Clif.Alloc.readonly`) must therefore be mapped read-write: a
process that maps its `.rodata` read-only (most real Rust binaries) is not covered. The reason: the
proof keeps the unwritable bytes with the code image (`sysSK I B f K r NW`, the kept addresses `G`
of every activation), and the VCode semantics `csem F` admits only accesses, loads included,
outside `F ⊇ G` (`AccessOk`), so `G` cannot hold a byte the program reads. `Clif.run` already makes
every store into read-only data `stuck`; carrying that through isel (a write guard next to
`csemG`'s read guard) is F8a, #472, which will relax `MapRelRW` to the CLIF-writable bytes.

Proof: per function, `backend_correct_worldX_cleanup_memtrapW` (every state before the trap also
has `RL.WritesAt`: its writes avoid `G`); linked program, `backend_correct_program_memtrapW_*`
(`LinkSys.RunGoodLBW`); on a model state, `RL.evsOk_of_goodXW` (reads outside `G` or jump-table
bytes, writes outside `G`, so no fault) and `E2E.ExecBytes.evsOk_congr` (a fault depends only on
the registers, which the simulating executable state shares); `act_simNF`/`act_simNBF` (the
simulation with "no earlier executable step faults": hooked steps and `bl`/`blr`/`adrp`/`add`
words access no memory, `noFault_hook`, `noFault_call`, `noFault_pair`).

Witness (`FV/Link/DeadCleanupExeMemFaultWitness.lean`): the `atomic_cas` program above; `mapRelRW`
(`MapRelRW nullMap` for a reserved stack above the null page: the code lies above it, `img_ge`, the
entry CLIF memory is empty), `exec_trapsF` (`compileExe_correct_memtrapF_rw` with every premise but
the entry contract and the stack's position discharged).

## Entry-state and runtime premises (A5, #411)

`FV/E2E/EntryContract.lean`, `FV/Front/RawExeContract.lean`, `FV/Front/ExeContract.lean`,
`FV/Front/RawExeTrapContract.lean`, `FV/Link/DeadCleanupExeSourceContract.lean`,
`FV/Link/DeadCleanupExeTrapContract.lean`. The executable theorems (`Front.bundle_correct_raw{,_peak}`
and everything below them) take seven premises about the code
outside the program and the machine state the program is entered in: `BaseOk`, `HooksSim`, the
i128 helpers' contract (`hlegal`), the indirect-call signatures (`hsig`), `Image.Intact`,
`OutsideCall` and `ClifRun`. Each field is one of:

* **trusted** — a contract TO-PROVE §1.3 trusts by design (the code outside the program; the OS
  loader and runtime), stated as a premise;
* **derived** — follows from the written ELF (the checks `compileExe` runs and proves:
  `okB_leanLink`, `binOk_leanLink`) and a loader/caller contract stated on the file;
* **choice** — the choice of the CLIF state that models the machine state (which CLIF run the
  theorem is about), not an obligation of anyone;
* **open** — would need a fact nothing provides today.

| Premise / field | Gate | Kind | Notes |
| --- | --- | --- | --- |
| `BaseOk.baseNoAlloc` | a function with an outgoing-argument area | trusted (outside code) | externs allocate no CLIF memory |
| `BaseOk.keepSyms`, `.aliasSyms` | a function with an indirect call | trusted (outside code) | the CLIF model of the outside world keeps symbols; names at one address of no program function are one extern (met by `closedBase`) |
| `BaseOk.baseOs`, `.basePc`, `.baseExt` | — | trusted (outside code) | outside calls are AAPCS64-sound, return to `pc + 4`, set no model error, keep the program field |
| `BaseOk.baseX`, `.baseXI`, `.baseTry` | — | trusted (outside code) | the externs' CLIF semantics is what the machine's outside calls do (`XCallsOk`, `XCallsIndOk`, `CalleeTryOk`) |
| `BaseOk.baseTls`, `.baseTlsNI` | a `tls_value` / `NeedNI` | trusted (loader/runtime) | the TLSDESC resolver (on the hook-free route only `TlsLoader`) |
| `BaseOk.baseNI` | `NeedNI` | trusted (outside code) | non-interference of outside calls |
| `OkD.baseDet` (`HookDet`), `OkDX.baseDetX` (`HookDetX`) | `NeedNI` (prophecy determinism, `docs/plans/uninit.md` §5.8–§5.9) | trusted (outside code) | outside calls and the TLS resolver are deterministic on the dead stack below `sp`, and do not observe return addresses (`x30`, the saved-LR bytes of the frame-record chain, `LRByte`); an extern that takes a backtrace is outside the premise |
| `OkDNX.baseNIX` (`HookNIX`, [#704](https://github.com/eth-act/clifv/issues/704)) | `NeedNI` (prophecy determinism, `docs/plans/uninit.md` §5.9 "machine lock, as built") | trusted (outside code) | the machine analogue of `XNI`: from two states equal but for `x30` and bytes `Z` inside the activation's exterior `F` (callers' frames, CLIF-invisible bytes), outside calls and the TLS resolver give states equal but for `x30` and `Z`: they observe neither return addresses nor bytes outside the world; an extern that walks the stack or takes a backtrace is outside the premise |
| `BaseOk.baseKeepsPlace`, `.baseKeepsAllocs` | `NeedSlots` | trusted (outside code) | outside calls keep the slot-placement oracle and the allocations |
| `HooksSim.call`, `.tls` | — | trusted (outside code) | the hooks read no relocated instruction byte and not the program field |
| `hlegal` (`HelperOk`, `ExtLegal`, `EnvKeepsBounded`) | the program mentions `i128` | trusted (outside code) | the i128 helpers' contracts (gap "legalisation environment restrictions") |
| `hsig` (`∀ n, B.env.sigOf n = none`) | a function with an indirect call | trusted (outside code) | a property of the CLIF model of the outside world |
| `Image.Intact` | — | trusted (loader) | already stated on the file: the read-only and RELRO segments hold the file's bytes |
| `OutsideCall.pc`, `.spAligned`, `.args` (registers) | — | trusted (caller) | AAPCS64; `pc` is `f`'s link-map address, which `SymsOk` ties to the file's symbol table |
| `OutsideCall.err` | — | trusted (caller) | a model convention: no model error in the entry state |
| `OutsideCall.ra` | — | trusted (caller) | the caller is outside code; not derivable from the file (fallback functions share the read-only text segments with the program) |
| `OutsideCall.stack` (`N ≤ sp`) | — | trusted (loader/runtime) | `N = stackFn` or `frameDrop + D·d`; nothing relates it to the OS stack limit (open as a runtime fact, a premise by design) |
| `OutsideCall.stackFree` | — | **derived** (`stackFree_of`) | the code is in read-only segments (`DeadCleanupBinCheck.img_bytes`); the stack is writable (`Loader.stackRw`) |
| `OutsideCall.args` (stack arguments not code) | — | **derived** (`argsOut_of`) | stack arguments are in writable memory (`ArgsRw`) |
| `OutsideCall.bytes` + `.image` | — | **derived** (`image_of`) | one uniform agreement (`ClifView.bytes`: every live CLIF byte is the machine's) + `Image.Intact` + `BinCheck.roByte_sound` |
| `OutsideCall.valid` | — | choice (`ClifView.valid`) | the CLIF allocations fit, hold no code, lie in the free stack only in `f`'s slot region; "hold no code" would be derivable from a code/data separation fact of the file (open: not checked today) |
| `OutsideCall.symbols` | — | choice (`ClifView.symbols`) | the CLIF symbol table is the link map |
| `ClifRun.entry`, `.slots`, `.place` | — | choice (`ClifView.run`) | the reference run: CLIF leaves slot addresses unspecified |
| `OutsideAvoids` (GOT slots) | — | discharged | `leanLink`'s output has no GOT slot (`outsideAvoids_leanLink`) |
| `BaseTrapsOk` (trap family) | a trapping run | trusted (outside code) | the outside code does not return where its CLIF semantics traps; covers the legaliser's `__*ti3` helpers; field `traps` of `TrapContract` |
| `noTry` (trap family) | — | trusted (the program) | no `try_call` terminator in the program (S9b); field `noTry` of `TrapContract` |

The runtime contract covers every executable theorem (`Front.bundle_correct_raw{,_peak}`,
`Front.bundle_correct_source{,_peak}`, the trap theorems of #398, and the `_source` theorems):
* `Front.bundle_correct_raw_contract{,_peak}`, `Front.bundle_correct_raw_trap_contract{,_peak}`
  (`Front.TrapContract` = `EntryContract` + `traps` + `noTry`);
* `Front.bundle_correct_source_contract{,_peak}` (`FV/Front/ExeContract.lean`);
* `Link.DeadCleanup.compileExe_correct_source_contract{,_peak}`
  (`FV/Link/DeadCleanupExeSourceContract.lean`), `Link.DeadCleanup.compileExe_correct_trap_contract{,_peak}`
  (`FV/Link/DeadCleanupExeTrapContract.lean`, `TrapContract` = the six runtime fields + `traps` +
  `noTry`, since `compileExe_correct_trap` takes no `hlegal`/`hsig`).

Witnesses: `Crates.FrontendBundleWitnessContract` (the `g_u128` unit: `bundle_raw_contract_witness`,
`bundle_raw_peak_contract_witness`, `bundle_source_contract_witness`, `bundle_source_peak_contract_witness`;
no run of the unit traps), `Crates.TrapContractWitness` (`Link.DeadCleanup.TrapWitness`'s `f`/`h`
program, whose division by zero traps).

Genuinely open (not entry-contract fields): a model of the process start (the ELF entry point,
musl's startup and std's `lang_start` producing the entry state: outside code, trusted by design);
the stack size against the OS limit; the existence of a CLIF view for a given machine state (the
caller's heap as CLIF allocations); the run premises `MemBounded` (#407) and `NoMemTrap` (needs a
fault model).

```lean
-- E2E.EntryContract
structure Loader (file : ByteArray) (N : Nat) (r : Arm.ArmState) : Prop where
  intact : (imageOf file).Intact r
  stack : N ≤ (spv r).toNat
  stackRw : ∀ a, StackBelow N (spv r) a → ¬ Elf.ro file a   -- the stack is writable memory
def ArgsRw (file) (sig) (args) (r) : Prop      -- ArgsOut with `Avoids (Elf.ro file)` for stack args
structure Caller (I) (file) (f) (r) (args) : Prop where
  pc : Arm.r .PC r = (art I f).base
  err : Arm.r .ERR r = .None
  ra : ¬ img I (xreg 30 r)
  spAligned : (spv r).toNat % 16 = 0
  args : ArgsRw file f.sig args r
structure ClifView (I) (B) (f) (N) (r) (args) (cs) : Prop where   -- a choice
  bytes : ∀ a b, cs.mem.valid a 1 → cs.mem.bytes a = some b → read_mem a r = b
  valid : …                                  -- as OutsideCall.valid
  symbols : cs.mem.symbols = fun n => I.syms.lookup n
  run : ClifRun I B f r args cs
theorem outsideCall_of (hI : okBCleanup I = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hl : Loader file N r) (hc : Caller I file f r args) (hv : ClifView I B f N r args cs) :
    OutsideCall I (BinCheck.roByte I D) f N r args cs.mem
-- Front
structure EntryContract (S) (B) (file) (g) (N) (r) (args) : Prop where
  base : BaseOk (sys S.inputCleanup B)
  hooks : HooksSim S.inputCleanup B
  legal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
    HelperOk B.env ∧ ExtLegal B.env ∧ EnvKeepsBounded B.env
  sigs : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none
  loader : Loader file N r
  caller : Caller S.inputCleanup file g r args
theorem bundle_correct_raw_contract … (hC : EntryContract S B file g (stackFn S.inputCleanup g) r args')
    (hv : ClifView S.inputCleanup B g (stackFn S.inputCleanup g) r args' cs') …
    -- g = legalize (f.rename σ.fwd); otherwise the premises and conclusion of bundle_correct_raw
theorem bundle_correct_raw_peak_contract …    -- N = frameDrop (art _ g).af + D * d, as _peak
```

* **Non-vacuity** (`crate-proofs/Crates/FrontendBundleWitnessContract.lean`): on the codegen unit
  of `g_u128` (`Crates.FrontendBundleWitness`), every `PT_LOAD` segment of the written executable
  ends below `sp0 - 2^20` (`loadBelowB`, decided on its program headers), so the stack is in no
  read-only segment (`not_ro`); `contract`: `EntryContract` holds for the outside call of the
  compiled `wmul_u128` with up to `2^20` bytes of stack; `bundle_raw_contract_witness`,
  `bundle_raw_peak_contract_witness`: the two theorems instantiated, the executable returns
  `15, 5` in x0, x1.
* `#print axioms` (`scripts/audit/entry-contract.lean`): `[propext, Classical.choice,
  Quot.sound]`.

## Known gap: reads of uninitialised stack bytes (SEM1, [#537](https://github.com/eth-act/clifv/issues/537))

In `Clif.run` a stack slot's bytes start uninitialised (`none`: `Mem.allocAt`/`alloc` through
`bumpSlots`/`placeSlots` in `enterFunc`), and a `load` of such a byte (likewise `memcmp` in
`Clif.Rust`) is `stuck`. Cranelift has no such undefined behaviour: the load returns whatever
bytes are there, and cg_clif's output relies on this, e.g. for a partially initialised `Option`/enum
or the copy of a partially written `sret` slot. `ArmRefines`/`ExecRefines` make no claim for a
`stuck` outcome, and `Front.bundle_correct_*` cover only `returned`/`trapped`. So a run that reads an
uninitialised stack byte, in the entered function or in any callee, **currently gets no guarantee**
from `E2E.backend_correct_final`, `Link.DeadCleanup.compileExe_correct*` or
`Front.bundle_correct_*`. Measured (2026-10-23, shadow-stack qemu plugin, a lower bound):
9 of 21 fv-demo and 46 of 53 survey test runs (`cargo fv test --lean-link --verified`) perform at
least one such read. Planned fix (`docs/plans/uninit.md` §5, route (i)): slot bytes start with
values from an oracle (`Clif.Place.init`), which the theorems instantiate with the Arm memory at
activation entry. The generated code stays stock Cranelift's. **The gap stays open for a while**
([#556](https://github.com/eth-act/clifv/issues/556)). The linking's canonical callee runs and
non-interference (`CalleeOkG.os`, `LinkSys.Thm`) cannot carry stale reads, because those bytes
include regalloc-chosen values outside the world (earlier callees' register saves and spills). The
per-function theorem first needs a call semantics indexed by the actual run, threaded through the
reg-level simulation; new theorem variants will sit beside the existing ones. The heap-side gap
(allocating externs) is separate: [#547](https://github.com/eth-act/clifv/issues/547) (SEM2).

## Remaining (precise)

M4 (`LowerRulesCorrect` and the terminator statements) and M6 (`RegLevelCorrect`, `DriverSem`,
`Refines`/`MemRefines` of `csem`) are proven, `FormsCovered` follows from `formsCovered_complete`,
and the program callees' contracts are discharged by `E2E.backend_correct_program` (induction on
the call depth); the executable theorems are `Link.DeadCleanup.compileExe_correct{,_peak,_source,
_source_peak}` and, from cg_clif's dumps, `Front.bundle_correct_raw{,_peak}` (under the single
runtime contract `Front.EntryContract`: `Front.bundle_correct_raw{,_peak}_contract`, "Entry-state
and runtime premises" above); with callee traps
`Link.DeadCleanup.compileExe_correct_trap{,_peak,_source_trap,_source_trap_peak}` and
`Front.bundle_correct_raw_trap{,_peak}`, with `try_call` callee traps too
`compileExe_correct_trapT{,_peak}`, `compileExe_correct_source_trapT{,_peak}` and
`Front.bundle_correct_raw_trapT{,_peak}` (above). What remains is
listed in `docs/TO-PROVE.md` (§1.1 for totality, §4 for scope, §5 for the trusted base); from this
file: stack-passed arguments of indirect calls (`indSigs`, S5) and memory-access traps (need a
fault model; `TrapsExplicitC`).

## Trusted (not proven)

* Lean kernel; Lean's and the C compiler that run the compiler. Since T6 every fixed backend
  proof and every optimizer rule proof is kernel-checked (no `bv_decide`/`native_decide`
  certificate in the compiler theorems; per-crate witness files still use `native_decide`).
* **Arm model fidelity** (`FV/Arm`, ASL-derived, co-simulated against qemu) and **`Clif.run`
  fidelity** (checked against Cranelift's interpreter and native runs), including the choice
  that CLIF slot addresses are unspecified (`ClifEntry`).
* **Single-threaded atomics** (agent/atomics-proof): `bmask`, `atomic_load`, `atomic_store`
  and `fence` are inside `backend_correct_final`. This rests on the Arm model being single-core:
  `ldar`/`stlr` are plain accesses, an exclusive store always succeeds, there is no monitor, and
  `dmb` is a no-op (`docs/decisions/arm-model.md`, "Atomics"). `atomic_rmw`/`atomic_cas` stay
  outside E: their root rules are proven vacuous from `CtxInv.instE`.
* **TLSDESC hook** (agent/stack-tls-proof): `TlsOk` (premise `hTls`, functions with a
  `tls_value`): the resolver and `TPIDR_EL0` give the running thread's instance address of the
  variable (`X.sym v 0`, the `syms` address `Clif.run` uses for its one thread), preserve every
  register but x0, x30 and the temporary (Cranelift's TLSDESC convention) and may change the
  flags (`docs/decisions/arm-model.md`, "Thread-local storage"). For the executable
  (`binary_correct_exec_proven_tls`, `compileExe_correct_tls`, T1) the hook is gone: the
  local-exec words run on the model, and only the loader's thread-pointer contract `TlsLoader`
  remains (the entry's `TPIDR_EL0`, kept by outside code, and the variables' instances at
  `TPIDR_EL0 + TpOff`).
* **Object writing, linking and loading** (`elfObject`, rust-lld, the loader): the words of `fb`
  at `base`, relocations resolved to `syms`/callee addresses (M6's hooks), GOT contents. For a
  crate's executable (M9, "Binary level (M9)") the code, relocations, GOT slots used, data
  objects and symbol addresses are proven from the file (`bin_ok`); the loader (each `PT_LOAD`
  at `p_vaddr`) stays trusted. On the executable machine (`binary_correct_exec_proven`) the
  hooked GOT pair, the slot's value at its `ldr` (check `gotB`) and the "no branch between a
  pair's words" item are proven; the TLS local-exec rewrite is the TLSDESC hook there, and runs
  on the processor in `binary_correct_exec_proven_tls` (T1, loader contract `TlsLoader`).
* **Runtime/callee contracts**: externs implement `Clif.Env.extern` under AAPCS64
  (`CalleeSound`, stack use); OS behaviour at `udf` (SIGILL reported as the trap-table code).
  For the executable machine (`binary_correct_exec_proven`) also `HooksSim` (the outside-call
  and TLS hooks read no relocated instruction byte and not the program field; in the hook-free
  `binary_correct_exec_proven_tls` only its outside-call clause, the TLS one is proven,
  `hooksSim_le`) and
  `OutsideAvoids` (the outside caller keeps the GOT slots out of its free stack, stack arguments
  and live CLIF memory).
* **Rust route (trusted contracts, rust-route)**: the `core` panic entry points the corpus
  references (`panic*`, `*_fail`, `handle_*`, `fmt` — mangled symbols) and the libcalls
  `memcpy`/`memset`/`memmove`/`memcmp`. They fit the existing `XCallsOk`/`CalleeOk` contract
  (diverging = never returns; the mem* calls are byte-level copies/fills/compares). Lean
  side: `Clif.Rust.env` (`FV/Clif/Rust.lean`, used by `clif-filetest --rust-env`). Native
  side: `scripts/rust-clif/rust-runtime.{c,s}` (`clif-native --link`), where the panics
  abort with `udf #251` (SIGILL) and never return — the two representations of "aborted"
  are agreed at the call site. The cg_clif corpus also references the allocator shims
  (`__rust_alloc`, …) and the i128 builtins (`__udivti3`, `__rust_u128_mulo`); both are out
  of scope until `i_alloc`/i128 are taken up (the allocator is the existing flat-runtime
  path).
* Frontend: rustc and the patched cg_clif, and the frontend bundle's faithfulness to what cg_clif
  compiled (docs/contracts/frontend.md §1, §5).

## `#print axioms`

```
E2E.backend_correct, E2E.backend_correct_of_rules, E2E.loweringObligations_of_check,
E2E.prepareCorrect_of_check, Backend.Proof.Driver.driver_correct,
Backend.Proof.Driver.termCalls_of_rules:
  [propext, Classical.choice, Quot.sound]
E2E.clifEntry_initState: [propext, Quot.sound]
Backend.Proof.regLevelCorrect_backend:
  [propext, Classical.choice, Quot.sound] (T6: no native axioms)
E2E.backend_correct_final: those of `backend_correct_m4` and `regLevelCorrect_backend`
E2E.backend_correct_linked: those of `backend_correct_final`
Clif.runLoop_link, E2E.xCallsOk_link: [propext, Classical.choice, Quot.sound]
E2E.calleeOk_witness, E2E.final_contracts_witness, E2E.witness_saves_lr, E2E.calleeOk_id,
E2E.final_contracts_id:
  [propext, Classical.choice, Quot.sound] (T6)
E2E.backend_correct_final_witness, E2E.backend_correct_final_id: those of `backend_correct_final`
E2E.BinCheck.img_bytes, E2E.BinCheck.codeB_sound, E2E.BinCheck.symsB_sound,
E2E.BinCheck.binOk_of: [propext, Classical.choice, Quot.sound]
E2E.BinCheck.dataB_sound, E2E.BinCheck.hdrB_sound, E2E.BinCheck.roByte_sound,
E2E.BinCheck.dataByte_sound, E2E.Elf.agrees_ext: [propext, Quot.sound]
Crates.NAME.bin_ok: [propext, Classical.choice, Quot.sound] + `Crates.NAME.{hdr_bin, data_bin,
  syms_bin, sliceK_bin}._native.native_decide.ax_1_1`
```

Every top-level theorem of the compiler (per function, per executable, the frontend theorems) and
the result of an axiom scan of every constant of `FV`: `docs/research/axiom-audit.md`.


### Raw Stock arithmetic production

The default non-optimizer/non-unwind route now additionally accepts complete
single-block ordinary i32/i64 functions containing straight-line add/sub bodies
and a return, through actual raw Stock output. Source/SSA/ABI checks and the
executable ABI-read check derive the semantic premises. Unused parameters,
stack-passed arguments and explicit source slots retain the original input
conditions. Candidate, allocation, emission or layout failure retries the
previous production route with the same input/settings.

`CompiledSemanticNI` is additive: old production contracts and theorem variants
keep their legacy lowering-validator guarantees. The new consumer proves source
execution, exact return values, related-world non-interference, whole-program
linking, stack/binary/executable execution and original-source/peak variants.
Compiler roots use the standard axioms; fixed compiler-data witnesses are marked
separately. The semantic checker validates either retained or raw Stock artifacts;
consumer routing recovered from actual artifacts is untrusted data and introduces
no source-value, per-record family or caller-selected virtual-file certificate.

Other function families and optimizer/unwind activation, full Stock-only
completeness and every remaining original #140 obligation remain open. The
active branch is under validation; this paragraph is not a main landing receipt.

Mixed select/add/sub implementation is pending on `agent/stock-mixed-production`:
source-only executable checks derive its domain, flag-threaded paired execution
preserves exact ABI returns, and shared semantic consumers retain the original
source/machine boundary. It adds no caller-supplied map/run certificate. Default
adapters and the previous-semantic-compiler-before-legacy retry are unvalidated;
see `docs/research/stock-mixed-production-checkpoint.md`. This is not a main
activation or a change to the original #140 completion conditions.
