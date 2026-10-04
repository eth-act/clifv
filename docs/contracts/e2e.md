# M7: the end-to-end theorem `backend_correct`

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
| `LoweringObligations f vc` (`LowerShape` incl. `CtxInv`, `ValsBelow`, types; SSA certificate `Cert`) | **discharged**: `lowerCheck f vc = true` ⇒ it (`loweringObligations_of_check`) |
| `PrepareCorrect sem vc vcp` (unreachable blocks, critical-edge splitting, RPO) | **discharged**: `prepCheck vc vcp = true` ⇒ it (`prepareCorrect_of_check`); and without the validator on `PrepDomain` VCode (`prepareCorrect_of_domain`, from `prepCheck_complete`; see "Validator completeness") |
| Validators run by the compiler (`FV/Backend.lean` `lowerChecked`, `FV/Backend/Regalloc.lean` `allocateRegalloc2`: a rejection is a compile error) | done |
| **`backend_correct`**, **`backend_correct_of_rules`** from the hypotheses below | **proven**, sorry-free |
| **`backend_correct_m4`** (`FV/E2E/Final.lean`): `backend_correct_of_rules` with all M4 predicates discharged (`lowerRulesCorrect_program`, `excludedUnmatchable`, `callRulesCorrect`, `indRulesCorrect`, `memRulesCorrect_program`, `lowerTermRulesCorrect`, `termUnmatchable`, `branchRulesCorrect`, `branchExcludedUnmatchable`, `tryRulesCorrect`, `tryUnmatchable`, `tryIndRulesCorrect`, `tryIndUnmatchable`) and `sem s := csem (F s) (ctx s) (X s)` (discharges `DriverSem` by `driverSem_csem`, `CallsRefine` by `callsRefine_csem` from `XCallsOk`, `IndCallsRefine` by `indCallsRefine_csem` from `XCallsIndOk`) | **proven**; axioms: `propext`, `Classical.choice`, `Quot.sound` + 130 `_native.bv_decide` certificates |
| **`RegLevelCorrect`** for the backend's code (`regLevelCorrect_backend`, `FV/E2E/RegLevelCorrect.lean`, M6Ctl3): addresses outside the world `frameW K` (frame addresses `frameF` and, since agent/callee-fix, the callees' dead stack), context `⟨fa.k, af.slotBase⟩`, one external semantics `X`, machine `ArmStepX X H fa`; from `FormsCovered` and `CalleeOk` | **proven** |
| **`backend_correct_final`** (`FV/E2E/Final.lean`): `backend_correct_m4` with `hM6` discharged by `regLevelCorrect_backend` | **proven**; axioms: `propext`, `Classical.choice`, `Quot.sound` + `_native.bv_decide` certificates (M4's, M5's decoder `decode_armBits_*`/`decode_raw_inst_of_*`, `Arm.Memory.read_write_bytes_different`) |
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
| `FormsCovered cx vcp` | per-function decidable premise (`formsCoveredB`, the covered straight-line forms `FormOk`, including the per-instruction bitmask check `logicImmOk`; control forms are handled by the proof); decided by `lean-e2e-check` (corpus + extrt + runtests: 913 of 913 checked functions covered, M6Refines) |
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
  (`Backend.abiSigs`; other special purposes such as `vmctx`/`sarg` stay unverified).
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
* **Calls**: `gen_call_args` puts argument `i` at `(locsOf sig)[i]`: a register (with at most 8
  parameters `x (abiArgIdx …)[i]`, `sigArgLocs_regs`) or a store to `[sp + off]` of the outgoing
  area (`argStores_run`); `gen_call_output` allocates one def per
  `sigRets` entry. `CallsRefine`/`XCallsOk` are stated for the declared externs (`exts :=
  f.externs.map (·.2)`) with `ds.length = (sigRets ext.sig).length` defs, `outs.length =
  ds.length` and `PrefixHold rvals outs`; an `sret` call has no CLIF result (`CtxInv.resTys`),
  so its extra def is not related to anything (`results_call`). `ExternsNormal` is gone
  (`CallRuleOk` assumes `ExternsIn f exts`).

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
* **Not claimed**: nothing about unwinding. The landing pads (the handler edge blocks and their
  code), the exception payload on the handler edges, the call-site table and the LSDA
  (`callSites`, `.gcc_except_table`), the `.eh_frame` rows and the personality routine are
  trusted and outside every theorem.
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

### `tls_value` (one thread, trusted TLSDESC hook)

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

### Indirect calls and function addresses

**Semantics (trusted-semantics growth).** `Clif.stepCallIndirect` (`FV/Clif/Run.lean`) takes the
callee value as a code address. A function of the program at that address is entered, as
before. Otherwise it now calls the extern at that address
(`Clif.callExternAt`): the first name of `env.names ++ Program.externNames` (the environment's
further code symbols — empty by default, agent/link-scope —, then the externs the functions of
`p` declare, which `Program.initMem` gives link-time `symbols`) whose address is the callee
value, run as `env.extern` with the argument and result types checked against the call site's
`sigN`, like `Clif.stepCall`. Before this change such calls were stuck.
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
  `X.sym n 0` of an extern `n` of `env`, on arguments of the call site's parameter types (as
  `Clif.callExternAt` checks them), returns what `env.extern n` returns (one output per
  `sigRets`, the results first, the memory relation kept) — the clause `XCallsOk` states for a
  GOT call of a declared extern, for every extern of `env`. With `hsym` (the external
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

`InSubset.externCalls` excludes calls of functions of the program: `Clif.run` enters such a
callee, while the Arm model abstracts every call through the callee contract. `cargo fv`
compiles each function in its own file, so the only such call is a recursive one; every other
call of a crate function is already an extern call under `XCallsOk`/`CalleeOk`. `cargo fv`
(`self_call_alias`, `rust/crates/cargo-fv/src/pipeline.rs`) renames the self-call declarations
`fnK = [colocated] %f(…)` to the extern `%f__fvself(…)`, compiles that file (inside the theorem,
the recursive call under the callee contract like any other), and redirects the alias's
relocations to `f` (`llvm-objcopy --redefine-sym`): the code is the same (disassembly identical
to compiling the original file), the linker resolves both names to `f`. The claim is the modular
one made for every call: the callee at `f`'s address behaves as the environment's `f__fvself`.
`lean-backend` itself still reports a call of a function of the file unverified (multi-function
files, runtests).
* **Regression file**: `corpus/clif-regress/call_indirect.clif` (a vtable built with
  `func_addr` and dispatched through, a function address returned as a value, `try_call_indirect`).

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
names; `f` itself must be `InSubset (P.only f)`, so it calls itself only through `cargo fv`'s
alias (`f__fvself`, a function of `P` with `f`'s body). Runs in which a program callee traps are
excluded, as for any callee (`TrapsExplicit.stmt` of the per-function run).

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
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only f) cs) :
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
  activation's `sp` `c` when program callees have slots: the run of `P.only g` is the same,
  `step_envOf`, `runLoop_envOf` under the activation invariant `ActInv`) at depth `M` from depth
  `M - 1`.

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
per call site (`raCall`, `raBlr`); a function with indirect calls (`call_indirect`, `try_call_indirect`) has no link-time
address itself, the functions of `P` have distinct addresses, names sharing an address of no
function of `P` are one base extern, the base externs keep the symbols (`indScope`,
`indNoSym`), its indirect-call signatures and the
functions it may call (`MayCall`: declared, or any other function of `P` with an address) with
the parameter types of one of them (`IndSigMatch`) pass no `sret` and at most 8 register
parameters (`indSig`),
and with an outgoing-argument area in `P` the functions with an address have no slots
(`addrSlots`).
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
bytes. It is vacuous without program callees with slots (`NeedSlots`).

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
      (`runLoop_place`, `runLoop_allocs`, `linkEnvN_keepsPlace`), so the caller's relation holds
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
4. *Direct self-recursion, one copy* (agent/link-scope2): `cargo fv`'s alias as a program call.
   `P` contains `r` (its self-call renamed to `r__fvself`, as `cargo fv` emits) and `r__fvself`
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
   crate, `r__fvself` resolves to `r` as a program call (not a base extern). Not covered: a
   function calling itself under its own name (excluded at the CLIF level, `InSubset (P.only f)`),
   recursion through a pointer.
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

Every per-function premise of `LinkSys.Ok` (`compiled`, `covered`, `tryRets`, `outFits`,
`argRegs`, `sretRets`, `calleeFrame`, `slotFits`, `callRegs`, `blrRegs`, `blrTry`, `raBlr`,
`indSig`, `indScope`'s declarations, `indNoSym`, `addrSlots`, `declSig`, `entryRegs`, `fits`,
`raCall`, `depth`, `subset`, `free`, the image `imgCode`) is an executable check with a
soundness lemma (`chks`/`Facts`, `siteOk_sound`, `blrOk_sound`, `tryB_sound`, `tryB_reg`,
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
`gotChainB_true`, `oneCopyB_true`, `sigChainB_true`, `blrChainB_true`, `zChainB_true` (and the existing
`bv_decide`/`native_decide` ones of the backend proofs). The witness found the former `raCall`
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
  aliases : List (String × String) := []   -- cargo fv's self-call aliases (f__fvself, f)
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

**Recursion, one copy.** A directly recursive `f` calls itself through `cargo fv`'s alias
`f__fvself`, which the linker resolves to `f`. Since agent/link-scope2's one-copy recursion
(`RaOk`), the alias is a function of the program: `link-check` adds it to `P` with `f`'s body
(its self-call naming `f`) at `f`'s address (`aliases`, `baseOf`): one copy of the code, the two
calling each other, each call returning into the callee's own code (`raOkB`, the second case of
`RaOk`). The recursive call is a program call, not a base extern, so its contract is no longer
a base premise. The alias has no symbol in the executable; `addrs` gives it a fresh address that
no other symbol has (only `symInj` reads it). `fv-demo`'s recursive function is covered this way.

**The checker** (`okB`, `okR`): per function (`chks = staticChks ++ linkChks`, each check named
by the premise it discharges): the pipeline succeeds, `lowerCheck`, `prepCheck`, `checkAlloc`
(`compiled`), `FormsCovered`, `tryRets`/`blrTry`, `sretRets`, `outFits`, `argRegs`,
`calleeFrame`/`slotFits`, `callRegs`/`blrRegs` (per call site: a `bl` of a function of `P`
passes its ABI registers; a `bl` of an extern outside `P` needs nothing; a `blr` site, `blrOk`,
for every function it may enter, `LinkSys.BlrTo`: one it declares or that one of its indirect
calls can enter, `indToB` for `IndTo`; at a call through the GOT, `gotOf`/`gotOf_sound` of
agent/link-scope2's `GotFlow`, only the GOT symbol's), `declSig`, `entryRegs`, `fits`,
`raCall`/`raBlr` (`raOkB`: the return address of every call is outside every other function's
code, an interval check, or after a call of that function's own code), `depth`, `free`, `subset`
(clif-subset-v2 E, no direct self-call, ABI and indirect-call signatures),
`indScope`/`indNoSym`/`indSig` (`indSig` for the functions one of the caller's indirect calls
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

**Tooling.** `cargo fv build|test --keep-temps` keeps per codegen unit `fv-link.json`: per
Lean-compiled function the CLIF file `lean-backend` compiled (with the self-call alias, or the
optimised dump of the missing-data retry), `lean-regalloc`'s output for it (`fv-rustc` runs as
the `lean-regalloc` of `lean-backend` and keeps a copy, `cargo_fv::linkproof::regalloc_tee`),
and the merge's names (each CLIF name → the symbol it is linked as); and per executable the lld
link map (`link-<tag>.map`, `link-<tag>.json`). `cargo fv link-proof` writes the input
directory: the CLIF renamed to the linked symbols (local symbols renamed by the merge,
`c_LdataN` → `__fv_<tag>_LdataN`, self-call aliases with their functions), the functions at
their `__fvlean$` marker in the map, the data objects they reach (since M9), the other
referenced names at their address in the executable's symbol table. `lake exe link-check`
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
(some `bv_decide` proof modules of `FV.Opt.Proof` produce C files of up to 3.5 GB, more than
Clang accepts), and Lake's per-module shared libraries are not linked against their imports
on Linux, so loading `FV.E2E.LinkCheck`'s alone fails. So the proofs live in a separate Lake
package, `crate-proofs/` (`require fv from ".."`), whose custom target `fvcheck` links the
object files of the checker modules (`checkRoots`: `FV.E2E.LinkCheck`, `FV.E2E.BinCheck`) and
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
slice; of `correct_i`: those and the backend's existing `bv_decide`/`native_decide` ones
(`dbm_sxtb`, `dbm_sxth`, the `decode_armBits_*`); `okB_sound`, `okB_of`: standard.

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
were not CLIF image symbols; `cargo fv link-proof` now adds the program functions held by the
data objects the program reaches, `data_syms`).

Not blocking: `try_call` between program functions and to base externs (95 `fv-demo` functions
and every survey crate's landing-pad code pass), `sret` (121 `fv-demo` functions), indirect calls
of `fn` pointers and vtable slots whose signature admits only register-only, non-`sret` callees,
folded aliases outside the program (`BaseOk.aliasSyms`), data objects
(`symbol_value`: in `syms`, their contents are entry premises: the CLIF entry memory), std calls
(base premises), stack-passed and `i128` arguments, direct recursion (one copy, above).

**Trusted** in addition to `backend_correct_program`'s: that `cargo fv` records the file it
passed to `lean-backend` and the output of the `lean-regalloc` run it made (a different
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
  addend` into `rd` in one of the forms lld leaves (`PairOk`): `adrp`+`add`, `nop`+`adr`
  (relaxed), or for the GOT `adrp`+`ldr` of a slot `G` whose 8 bytes in `loadMem` are `T`; a
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

**Tooling.** `cargo fv link-proof` writes into `link.json` the data objects the functions reach
(`data`: `clif-data-export`'s `; data:` lines renamed to the linked symbols, local ones as
`.LdataN@<unit>` with their address from the link map's entry under the unit's object file) and
the addresses of every name they refer to; it renames a function's self-call alias with the
function. `lake exe link-check` reads the executable (`exe`), evaluates the binary checks on the
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

`lake build` of all ten proofs: about 12 s. Findings:

1. **lld relaxes every address pair**: all 1425 `adrp`/`add` and GOT `adrp`/`ldr` pairs of
   the ten executables are `nop` + `adr` (target within ±1 MiB), and the two TLSDESC sequences
   are local-exec `movz`/`movk`/`nop`/`nop`. No Lean code reads a GOT slot, so the GOT form of
   `PairOk` has no instance in these executables; it was exercised on a patched copy of
   GU128's executable (one pair rewritten as `adrp`+`add`, one as `adrp`+`ldr` of the `.got`
   slot holding the target: accepted, `bin_ok` builds; the slot altered: rejected). For the
   boundary: the model's hooks put the address in `rd` at the first word of a pair
   (`ArmStepX`), the executable at the second.
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

**Not done here**: the boundary statement that consumes `BinOk` (item 3), the stack bound
(item 4); data reachable only from outside code (std's own data) is not checked; the
executable's entry point and startup code are std/musl's.

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
clif-subset-v2 E, calls (also `try_call`s) of functions of the same file, special-purpose parameters other than one `sret` pointer (`abiSigs`), indirect calls
with more than 8 parameters or special-purpose parameters (`indSigsOk`)) are still
compiled, without validation, and reported as unverified (`FileAsm.unverified`; `lean-backend`
prints `compiled, unverified (outside backend_correct): …`).

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

## Remaining (precise)

1. **M4**: `LowerRulesCorrect` (in progress; `ExcludedUnmatchable` proven) and the terminator
   statements `LowerTermRulesCorrect`, `TermUnmatchable`, `BranchRulesCorrect`,
   `BranchExcludedUnmatchable` for `Isle.Aarch64.program`.
2. **M6**: `RegLevelCorrect` and `DriverSem` are discharged (`regLevelCorrect_backend`,
   `driverSem_csem`); open: `Refines`/`MemRefines` of `csem` (M6Insts) and the decision of
   `FormsCovered` by `lean-e2e-check` (`formsCoveredB`).
3. **Scope extensions**: discharging the program callees' contracts of
   `backend_correct_linked` from their own theorems (induction on call depth; the dead-stack
   obstruction is fixed, the exact world, frame locality and slot placement remain, see
   "Linking" and `docs/DEFERRED.md`); stack-passed arguments of indirect calls (`indSigs`);
   memory-access traps (need a fault model).

## Trusted (not proven)

* Lean kernel, `bv_decide`'s LRAT checker / compiled evaluation (M5, M6 axioms); Lean's and the
  C compiler that run the compiler.
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
  flags (`docs/decisions/arm-model.md`, "Thread-local storage").
* **Object writing, linking and loading** (`elfObject`, rust-lld, the loader): the words of `fb`
  at `base`, relocations resolved to `syms`/callee addresses (M6's hooks), GOT contents. For a
  crate's executable (M9, "Binary level (M9)") the code, relocations, GOT slots used, data
  objects and symbol addresses are proven from the file (`bin_ok`); the loader (each `PT_LOAD`
  at `p_vaddr`) stays trusted.
* **Runtime/callee contracts**: externs implement `Clif.Env.extern` under AAPCS64
  (`CalleeSound`, stack use); OS behaviour at `udf` (SIGILL reported as the trap-table code).
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
* Frontend (pluggable, PLAN.md §4 M7 restatement).

## `#print axioms`

```
E2E.backend_correct, E2E.backend_correct_of_rules, E2E.loweringObligations_of_check,
E2E.prepareCorrect_of_check, Backend.Proof.Driver.driver_correct,
Backend.Proof.Driver.termCalls_of_rules:
  [propext, Classical.choice, Quot.sound]
E2E.clifEntry_initState: [propext, Quot.sound]
Backend.Proof.regLevelCorrect_backend:
  [propext, Classical.choice, Quot.sound] + M5's `decode_armBits_*._native.bv_decide` and
  `decode_raw_inst_of_{br,dpi,dpr,dpsfp,ldst}._native.bv_decide`,
  `Arm.Memory.read_write_bytes_different._native.bv_decide.ax_1_9`
E2E.backend_correct_final: those of `backend_correct_m4` and `regLevelCorrect_backend`
E2E.backend_correct_linked: those of `backend_correct_final`
Clif.runLoop_link, E2E.xCallsOk_link: [propext, Classical.choice, Quot.sound]
E2E.calleeOk_witness, E2E.final_contracts_witness, E2E.witness_saves_lr, E2E.calleeOk_id,
E2E.final_contracts_id:
  [propext, Classical.choice, Quot.sound, Arm.Memory.read_write_bytes_different._native.bv_decide.ax_1_9]
E2E.backend_correct_final_witness, E2E.backend_correct_final_id: those of `backend_correct_final`
E2E.BinCheck.img_bytes, E2E.BinCheck.codeB_sound, E2E.BinCheck.symsB_sound,
E2E.BinCheck.binOk_of: [propext, Classical.choice, Quot.sound]
E2E.BinCheck.dataB_sound, E2E.BinCheck.hdrB_sound, E2E.BinCheck.roByte_sound,
E2E.BinCheck.dataByte_sound, E2E.Elf.agrees_ext: [propext, Quot.sound]
Crates.NAME.bin_ok: [propext, Classical.choice, Quot.sound] + `Crates.NAME.{hdr_bin, data_bin,
  syms_bin, sliceK_bin}._native.native_decide.ax_1_1`
```

**Status (M6Insts2, 2026-09-28)**: `hRef`/`hmem` of `backend_correct_m4` are not yet discharged.
csem now falls back to `mspec` (ispec + memory forms) off error-free aligned worlds; `FormOk` must be
narrowed (xzr-destination imm/extended add/sub make `Refines` false as is). See regalloc-proof.md
"Status update (M6Insts2)"; `MemRefines` for `csem` will need `ctx.slotBase = slotOff` and a
GOT premise `syms n = some b → X.sym n 0 = ofNat b`.
