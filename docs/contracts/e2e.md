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
| **`RegLevelCorrect`** for the backend's code (`regLevelCorrect_backend`, `FV/E2E/RegLevelCorrect.lean`, M6Ctl3): frame addresses `frameF`, context `⟨fa.k, af.slotBase⟩`, one external semantics `X`, machine `ArmStepX X H fa`; from `FormsCovered` and `CalleeOk` | **proven** |
| **`backend_correct_final`** (`FV/E2E/Final.lean`): `backend_correct_m4` with `hM6` discharged by `regLevelCorrect_backend` | **proven**; axioms: `propext`, `Classical.choice`, `Quot.sound` + `_native.bv_decide` certificates (M4's, M5's decoder `decode_armBits_*`/`decode_raw_inst_of_*`, `Arm.Memory.read_write_bytes_different`) |
| **`sret`** (2026-09-30, `agent/sret-proof`): functions with a struct-return pointer parameter and calls of `sret` callees are inside `backend_correct_final` (`InSubset.abiSigs`; see "`sret`" below) | **proven**; `lean-e2e-check`: all `sret` functions in scope accepted and covered |
| **`try_call`** (2026-09-30, `agent/trycall-proof`): functions with `try_call` of an extern are inside `backend_correct_final` **for their normal returns** (see "`try_call`" below); nothing is claimed about unwinding, landing pads or the LSDA | **proven** (`term_step_try`, `tryRulesCorrect`, `tryUnmatchable`, `realizes_tryCall`) |
| **Indirect calls** (2026-10-01, `agent/indirect-proof`): `call_indirect`, `func_addr` and `try_call_indirect` (normal return) are inside `backend_correct_final`: an indirect call of an extern under the contract `XCallsIndOk` (hypothesis `hXI`), an indirect call of a function of the program excluded by the run premise `TrapsExplicit.indirect`/`tryIndirect` (see "Indirect calls" below). Trusted-semantics growth: `Clif.stepCallIndirect` calls the extern at the callee address (`Clif.callExternAt`) where it was stuck | **proven** (`call_ind_ruleOk` 1033, `func_addr_ok` 1026, `try_ind_ruleOk` 1036, `stepCallIndirect_eq`, `term_step_try` over `IsTryWith`); `lean-e2e-check`: 1092 in scope (1083 before, plus the 9 functions of `corpus/clif-regress/call_indirect.clif`), 0 rejected, 0 not covered |
| **Atomics stage A** (2026-10-01, `agent/atomics-proof`): `bmask`, `atomic_load`, `atomic_store` and `fence` are in E (`Compile.instE`) and inside `backend_correct_final`, on the single-threaded Arm model (`docs/decisions/arm-model.md`, "Atomics"). `atomic_rmw`/`atomic_cas` stay outside E: their root rules (994–1004, 1007) are proven vacuous from `CtxInv.instE` | **proven** (`bmask_ok` 936, `fence_ok` 1024, `atomic_load_ok` 983, `atomic_store_ok` 984, `uextend_atomic_load_ok` 810, `atomic_loop_ok`; M6: `corr_csetm`/`corr_fence`/`corr_loadAcquire`/`corr_storeRelease`, `straight_loadAcquire`/`straight_storeRelease`, `ref_csetm`/`ref_fence`); `lean-e2e-check`: 1118 in scope (1092 before), 0 rejected, 0 not covered; filetests corpus 114/114, extrt 22/22, runtests 4672/0/0, `atomics_loops.clif` Lean 11/11; encode-check 1291 identical / 0 differ; `cargo fv` debug verified: fv-demo 1323/1346, survey 3156/3179, vendor 4324/4399, `compare.sh` SAME |
| **Atomics stage B** (2026-10-02, `agent/atomics-proof`): `atomic_rmw` (all 11 ops, i8–i64) and `atomic_cas` (i8–i64) are in E and inside `backend_correct_final`, on the same single-threaded Arm model (the LL/SC loop body runs once: `stlxr` succeeds and writes status 0). The loops are `isCtl` in `csem` (`loopSem`: one symbolic run of the body, FV/Backend/Proof/LoopRun.lean); register level in FV/E2E/RegLevelAtomic.lean (`realizes_rmwLoop`, `realizes_casLoop`). The RMW memory clause only fixes the low `ty.bytes*8` bits of the old-value def (smin/smax i8/i16 sign-extend x27 in place). The checker `ctlInstOk` requires every loop operand to be an int vreg. The CAS i32 comparison uses `uxtw` (deviation from Cranelift's upstream bug, docs/research/upstream-bugs.md) | **proven** (`atomic_rmw_*_ok` rules 2357–2377, `atomic_cas_ok` 2390; `rmwBody_spec`, `casHead_spec`, `stlxr_spec`; `csem_rmwLoop`, `csem_casLoop`). lean-e2e-check 1126 in scope / 0 rejected; cargo fv debug verified: survey 3174/3179, vendor 4381/4399, fv-demo 1332/1346 |
| **Stack-passed parameters and `call` arguments** (2026-10-01, `agent/stack-tls-proof`): functions with more than 8 parameters (an `sret` pointer does not count) and `call`s of externs with more than 8 parameters are inside `backend_correct_final`. `InSubset` drops `regParams`/`callRegArgs` (a `try_call`'s callee and the indirect calls keep at most 8 register parameters: `tryRegArgs`, `indSigs`). Entry: `ArgsIn` puts a stack location `off` (`locsOf`, `sigArgLocs`) at `sp + off` of the ABI entry state (`StackArgAt`); the entry code loads it from `fp + 16 + off` (`DriverCheck.entryLoads`, `entry_step`). Calls: the outgoing stores go to `[sp + off]` (`argStores_run`), the callee contract `XCallsOk` takes `ArgsAt` (stack arguments read from memory at `sp + off`). `Rel` gains the outgoing-area size `out` (`OutRel`: `[sp, sp + out)` fits, avoids `F` and holds no live CLIF byte; `backend_correct_final` takes `out := intBase`). `lowerCheck` adds `callsStackOkB` (every call's stack area fits `vc.outgoing`, `stackLayoutOk`) and `entryOkB`; `prepCheck` keeps `outgoing`. Specialisations (new ⇒ old for ≤ 8 parameters / no stack arguments): `InSubset.of_regArgs`, `argsIn_iff_of_regs`, `argsAt_iff_of_regs`, `xCallsOk_of_regArgs`, `Rel.holds_zero` | **proven** (`call_bl_ruleOk`/`call_got_ruleOk` any arity, `entry_step`, `callsStack_of_check`, `entryOk_of_check`, `stackArgsAvoid_frameF`, `outgoing_le_intBase`); `lean-e2e-check`: 1146 in scope (1126 before), 0 rejected, 0 not covered |
| **`tls_value`** (2026-10-01, `agent/stack-tls-proof`): `tls_value.i64` of a `symbol tls` global value (offset 0; `elf_gd`, cg_clif's TLS model) is in E (`Compile.instE`, `globalE`) and inside `backend_correct_final` for the one thread `Clif.run` models (its instance of the variable is the memory's symbol). M4: root rules 1129 (`elf_gd`, `tls_value_ok`) and 1130 (`macho`, vacuous), `MemRefines`' TLSDESC clause (`memRefines_csem`). M6: `ElfTlsGetAddr` is `isCtl`; `csem` gives `[X.sym n 0, X.tp]` and the flags `X.tlsFlags n w` (`ExtSem.tp`/`tlsFlags`); the machine hooks the TLSDESC sequence (`ArmStepX`: `adrp` advances the pc, `ldr` runs `H.tls n tmp`) under the trusted contract `TlsOk` (premise `hTls`, only for a function with a `tls_value`; see "`tls_value`" below); `realizes_tls`/`os_tls` (FV/E2E/RegLevelTls.lean). x30 joins `Masked` (`docs/contracts/regalloc-proof.md`: no weakening for other functions). Validators: `lowerCheck` (`noTls_of_check`) and `prepCheck` (`noTls_of_prepCheck`) keep `ElfTlsGetAddr` out of the VCode of a function without `tls_value`; `ctlInstOk` requires int vregs | **proven**; `lean-e2e-check`: 1148 in scope (1146 before), 0 rejected, 0 not covered; cargo fv debug verified fv-demo 1336/1346, survey 3174/3179, vendor 4398/4399 |
| **Last unverified functions** (2026-10-01, `agent/last-unverified`): (1) stack-passed arguments of a `try_call` are inside `backend_correct_final`: `TryRuleOk` takes `SigStackOk e.sig outB` instead of "at most 8 parameters", `TryRulesCorrect` also `MemRefines`/`OutArgsOk` (as `CallRulesCorrect`), `TryCalls` takes the outgoing area, `DriverHyp.tries` carries `TryStack f out`, `lowerCheck`'s `callsStackOkB` also checks `try_call` callees (`tryStack_of_check`); `InSubset.tryRegArgs` and `Backend.regArgCalls` are gone. (2) `Opt.Legal.check` accepts `try_call` (expanded arguments/returns, normal-return arguments `expandTry`) and `call_indirect` without `i128` operands (plan `callInd`); `backend_correct_legal` drops `hci`/`hnt` and takes `hCT`, `hXI` and `hind` (vacuous without such calls: `backend_correct_legal_callFree` is the former statement). (3) recursion: `cargo fv` renames a function's self-call declaration to an extern alias (see "Calls of the function itself") | **proven** (`try_sym_lowerTryOk`/`try_got_lowerTryOk` any arity; `sim_try`, `sim_callInd`, `check_callInd`); `cargo fv` debug: fv-demo 1340/1346 (6 skipped), survey 3179/3179, vendor all verified |
| **Linking** (2026-10-02, `agent/link-proof`): the CLIF side of linking the per-function theorems is proven — a whole-program run `Clif.runLoop base P` (calls and `try_call`s of functions of `P` enter them) that returns or traps is a per-function run of `P.only f` under `Clif.linkEnv P base` (`Clif.runLoop_link`) — and `E2E.backend_correct_linked` states `f`'s Arm code against the whole-program run, with the program callees' contracts as premises. Discharging those from the callees' own theorems is **not** done: the callee contract `CalleeOk` cannot be met by code that saves its return address below `sp` (`E2E.calleeOk_saves_lr_false`); see "Linking" below | **proven** (CLIF layer, contract-level theorem, no-go lemma); Arm-level discharge open |

### Final hypotheses (`E2E.backend_correct_final`, 2026-09-28)

Notation: `FF s := frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s`
(the allocator-private frame addresses of the activation entered in `s`: spill/save slots, the
fp/lr pair and padding above the CLIF slots, the code words), `cx := ⟨fa.k, af.slotBase⟩`.

| Hypothesis | Kind / owner |
| --- | --- |
| `InSubset p f`, `Compiled f k vc vcp rf af fa fb` | the compiler ran (pipeline + validators) |
| `FormsCovered cx vcp` | per-function decidable premise (`formsCoveredB`, the covered straight-line forms `FormOk`, including the per-instruction bitmask check `logicImmOk`; control forms are handled by the proof); decided by `lean-e2e-check` (corpus + extrt + runtests: 913 of 913 checked functions covered, M6Refines) |
| `∀ s, CalleeOk (FF s) X H` | callee contract of the machine's call hook `H` (AAPCS64: `OperandsSound` of every call, return to pc+4, `X.call` error-free and program-preserving) — environment |
| `(∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk (FF s) X H` (`hCT`) | only for a function with a `try_call`: the def registers of a `try_call`'s call hold what `csem` gives them — the results, then the exception payload registers x0/x1 that are not return registers, as the callee's world `X.call` has them (see "`try_call`") — environment; vacuous for a function without `try_call` |
| `hasTls f = true → ∀ s, TlsOk (FF s) X H` (`hTls`) | only for a function with a `tls_value`: the machine's TLSDESC hook `H.tls` ends after the sequence, puts the variable's address `X.sym n 0` in x0 and the thread pointer `X.tp` in the temporary, keeps every other register but x30, the memory and the program, and leaves the flags `X.tlsFlags n w` — trusted (`docs/decisions/arm-model.md`, "Thread-local storage"); vacuous for a function without `tls_value` |
| `∀ s, XCallsOk env (f.externs.map (·.2)) (Rel.holds ⟨FF s, syms, slotOff, OB⟩ f) X` (`OB := (RAFrame.compute vcp rf).intBase`, the outgoing stack-argument area) | external contract for the externs `f` declares: callees, linker symbols — environment. The arguments are given by `ArgsAt` (register ones in their registers, stack-passed ones in memory at `sp + off`; for externs with at most 8 parameters this is the former "at most 8 values, all in registers", `xCallsOk_of_regArgs`); the callee returns a world related by `Rel.holds`, so in particular its outgoing area `[sp, sp + OB)` still avoids the frame and holds no live CLIF byte (`OutRel`; trivial when `OB = 0`, `Rel.holds_zero`). A call returns one value per ABI return of the declaration (`sigRets`), the first ones the extern's results (`PrefixHold`); for declarations without `sret` this is implied by the former extern-independent contract (`xCallsOk_of_results`) |
| `∀ s, XCallsIndOk env (indSigs f) (Rel.holds ⟨FF s, syms, slotOff, OB⟩ f) X` (`hXI`) | external contract for the indirect calls of `f` (`call_indirect`, `try_call_indirect`), per call-site signature (`Backend.indSigs f`): a `blr` whose target holds `X.sym n 0` of an extern `n` of `env` behaves as `env.extern n` does under that signature (the same clause as `XCallsOk`'s GOT call) — environment; vacuous for a function without indirect calls (`xCallsIndOk_nil`, `backend_correct_final_indirectFree`) |
| `∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b` (`hsym`) | linker: the external semantics' symbol addresses are the linked ones — environment; with `hslot` it discharges the former `MemRefines` hypothesis (`memRefines_csem`, M6MemRef) |
| `af.slotBase = slotOff` (`hslot`) | the relation's slot-region offset is the frame's slot base — caller (instantiate `slotOff := af.slotBase`) |
| per run: `AbiEntry fb base ra s`, `StackAvail af s`, `BodyEntry af s w₀`, `ArgsIn f.sig args s`, `ClifEntry f args cs`, `Rel.holds ⟨FF s, syms, slotOff, OB⟩ f cs.frame.slots cs.mem w₀`, `TrapsExplicit env p cs` (with the `try_call`/`try_call_indirect` trap clauses, and the indirect-call clauses `indirect`/`tryIndirect`: an indirect call of the entered function reaches no function of `p`; all vacuous for a function without them: `TrapsExplicit.of_tryFree`, `TrapsExplicit.of_indirectFree`) | caller of the theorem |

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
* **Callee contract** `CalleeTryOk F X H` (`FV/E2E/RegLevelTry.lean`, hypothesis `hCT`, only for
  functions with a `try_call`): the call of a `try_call` defines, beyond the results, the
  exception payload registers x0/x1 that are not return registers (`gen_try_call_rets`); on a
  normal return their values are unconstrained by the ABI, so the clause states that the
  hooked callee leaves in every def register the value `csem`'s `tryCall` clause gives it
  (the results as `CalleeOk` says; the payload registers as the callee's world `X.call` says).
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
before. Otherwise it now calls the extern of the program at that address
(`Clif.callExternAt`): the first name of `Program.externNames` (the externs the functions of
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
  `X.sym n 0` of an extern `n` of `env` returns what `env.extern n` returns (one output per
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
/-- no `call_indirect`, `try_call_indirect`, `return_call` (`call`, `try_call` allowed) -/
def LinkFree (g : Function) : Prop
theorem runLoop_link {P : Program} {base : Env} {f : Function}
    (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs) (hP : ∀ g ∈ P.funcs, LinkFree g) :
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
`backend_correct_final`, `FF`/`OB` as in "Final hypotheses"; the indirect-call contract is
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

**Why the program callees' contracts are not discharged** (proven obstruction and the gaps):

1. *`CalleeOk` is unsatisfiable for real non-leaf callees.* Its `os` clause compares the hooked
   callee's state with `X.call`'s world by `SameWorld F` (equal memory outside the caller's
   frame addresses `F`) for every state with the caller's world, and `X.call` sees only the
   world. So the memory a callee leaves outside `F` cannot depend on the pc, x19–x28 or x30
   (`calleeOk_mem_world`); a callee that stores its return address `pc + 4` below `sp` — every
   prologue `stp x29, x30, [sp, #-16]!`, ours included — contradicts it whenever its `X.call`
   returns (`calleeOk_saves_lr_false`). (The same holds for leaf externs only if they write no
   state-dependent byte below `sp`.)
2. *Exact world.* `X.call` must give the exact 128-bit def registers and the exact world (flags,
   memory outside `F`) of the hooked callee, while a compiled callee's theorem fixes only the
   low bits of its results and the live CLIF bytes (`ArmRefines`).
3. *Frame locality.* `ArmRefines` does not say that the callee leaves the caller's frame `F` and
   the memory outside live CLIF allocations unchanged, which `CalleeOk` (`FrameKeep`) needs.
4. *Slot placement.* `Clif.run` places a callee's slots with its bump allocator
   (`enterFunc`), the Arm code `sp`-relatively; the per-function theorem puts the entered
   function's slots at the Arm frame (`ClifEntry`, `SlotRel`). A program callee whose slot
   addresses escape (returned, compared) has different CLIF and Arm results, so its `linkEnv`
   contract is unsatisfiable; for the others it is satisfiable.

The remaining plan is in `docs/DEFERRED.md` ("Linking").

## The theorem (`FV/E2E/Main.lean`)

```lean
theorem backend_correct {p f k vc vcp rf af fa fb}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F syms slotOff out astep env}
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
    (hM6 : RegLevelCorrect sem F astep vcp af fb)
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
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
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
  at the same addresses; every live CLIF address is below 2⁶⁴ and outside the frame addresses
  `F` (the allocator-private part of the frame: spill/save slots, fp/lr); `cm.symbols = syms`
  (link-time `symbol_value` addresses).
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
  `backend_correct`, discharged by `stackArgsAvoid_frameF`): those bytes avoid the frame.
* **Resource precondition** `StackAvail af s`: the frame (`af.frameSize` + fp/lr) fits below sp.
  Callee stack use is part of the callee contract (M6's `CalleeSound`).
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
   `backend_correct_linked` from their own theorems (induction on call depth; blocked by the
   callee contract's shape, see "Linking" and `docs/DEFERRED.md`); stack-passed arguments of
   indirect calls (`indSigs`); memory-access traps (need a fault model).

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
  at `base`, relocations resolved to `syms`/callee addresses (M6's hooks), GOT contents.
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
Clif.runLoop_link, E2E.xCallsOk_link, E2E.calleeOk_mem_world, E2E.calleeOk_saves_lr_false:
  [propext, Classical.choice, Quot.sound]
```

**Status (M6Insts2, 2026-09-28)**: `hRef`/`hmem` of `backend_correct_m4` are not yet discharged.
csem now falls back to `mspec` (ispec + memory forms) off error-free aligned worlds; `FormOk` must be
narrowed (xzr-destination imm/extended add/sub make `Refines` false as is). See regalloc-proof.md
"Status update (M6Insts2)"; `MemRefines` for `csem` will need `ctx.slotBase = slotOff` and a
GOT premise `syms n = some b → X.sym n 0 = ofNat b`.
