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
| `PrepareCorrect sem vc vcp` (unreachable blocks, critical-edge splitting, RPO) | **discharged**: `prepCheck vc vcp = true` ⇒ it (`prepareCorrect_of_check`) |
| Validators run by the compiler (`FV/Backend.lean` `lowerChecked`, `FV/Backend/Regalloc.lean` `allocateRegalloc2`: a rejection is a compile error) | done |
| **`backend_correct`**, **`backend_correct_of_rules`** from the hypotheses below | **proven**, sorry-free |
| **`backend_correct_m4`** (`FV/E2E/Final.lean`): `backend_correct_of_rules` with all M4 predicates discharged (`lowerRulesCorrect_program`, `excludedUnmatchable`, `callRulesCorrect`, `indRulesCorrect`, `memRulesCorrect_program`, `lowerTermRulesCorrect`, `termUnmatchable`, `branchRulesCorrect`, `branchExcludedUnmatchable`, `tryRulesCorrect`, `tryUnmatchable`, `tryIndRulesCorrect`, `tryIndUnmatchable`) and `sem s := csem (F s) (ctx s) (X s)` (discharges `DriverSem` by `driverSem_csem`, `CallsRefine` by `callsRefine_csem` from `XCallsOk`, `IndCallsRefine` by `indCallsRefine_csem` from `XCallsIndOk`) | **proven**; axioms: `propext`, `Classical.choice`, `Quot.sound` + 130 `_native.bv_decide` certificates |
| **`RegLevelCorrect`** for the backend's code (`regLevelCorrect_backend`, `FV/E2E/RegLevelCorrect.lean`, M6Ctl3): frame addresses `frameF`, context `⟨fa.k, af.slotBase⟩`, one external semantics `X`, machine `ArmStepX X H fa`; from `FormsCovered` and `CalleeOk` | **proven** |
| **`backend_correct_final`** (`FV/E2E/Final.lean`): `backend_correct_m4` with `hM6` discharged by `regLevelCorrect_backend` | **proven**; axioms: `propext`, `Classical.choice`, `Quot.sound` + `_native.bv_decide` certificates (M4's, M5's decoder `decode_armBits_*`/`decode_raw_inst_of_*`, `Arm.Memory.read_write_bytes_different`) |
| **`sret`** (2026-09-30, `agent/sret-proof`): functions with a struct-return pointer parameter and calls of `sret` callees are inside `backend_correct_final` (`InSubset.abiSigs`; see "`sret`" below) | **proven**; `lean-e2e-check`: all `sret` functions in scope accepted and covered |
| **`try_call`** (2026-09-30, `agent/trycall-proof`): functions with `try_call` of an extern are inside `backend_correct_final` **for their normal returns** (see "`try_call`" below); nothing is claimed about unwinding, landing pads or the LSDA | **proven** (`term_step_try`, `tryRulesCorrect`, `tryUnmatchable`, `realizes_tryCall`) |
| **Indirect calls** (2026-10-01, `agent/indirect-proof`): `call_indirect`, `func_addr` and `try_call_indirect` (normal return) are inside `backend_correct_final`: an indirect call of an extern under the contract `XCallsIndOk` (hypothesis `hXI`), an indirect call of a function of the program excluded by the run premise `TrapsExplicit.indirect`/`tryIndirect` (see "Indirect calls" below). Trusted-semantics growth: `Clif.stepCallIndirect` calls the extern at the callee address (`Clif.callExternAt`) where it was stuck | **proven** (`call_ind_ruleOk` 1033, `func_addr_ok` 1026, `try_ind_ruleOk` 1036, `stepCallIndirect_eq`, `term_step_try` over `IsTryWith`); `lean-e2e-check`: 0 rejected |

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
| `∀ s, XCallsOk env (f.externs.map (·.2)) (Rel.holds ⟨FF s, syms, slotOff⟩ f) X` | external contract for the externs `f` declares: callees, linker symbols — environment. A call returns one value per ABI return of the declaration (`sigRets`), the first ones the extern's results (`PrefixHold`); for declarations without `sret` this is implied by the former extern-independent contract (`xCallsOk_of_results`) |
| `∀ s, XCallsIndOk env (indSigs f) (Rel.holds ⟨FF s, syms, slotOff⟩ f) X` (`hXI`) | external contract for the indirect calls of `f` (`call_indirect`, `try_call_indirect`), per call-site signature (`Backend.indSigs f`): a `blr` whose target holds `X.sym n 0` of an extern `n` of `env` behaves as `env.extern n` does under that signature (the same clause as `XCallsOk`'s GOT call) — environment; vacuous for a function without indirect calls (`xCallsIndOk_nil`, `backend_correct_final_indirectFree`) |
| `∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b` (`hsym`) | linker: the external semantics' symbol addresses are the linked ones — environment; with `hslot` it discharges the former `MemRefines` hypothesis (`memRefines_csem`, M6MemRef) |
| `af.slotBase = slotOff` (`hslot`) | the relation's slot-region offset is the frame's slot base — caller (instantiate `slotOff := af.slotBase`) |
| per run: `AbiEntry fb base ra s`, `StackAvail af s`, `BodyEntry af s w₀`, `ArgsIn f.sig args s`, `ClifEntry f args cs`, `Rel.holds ⟨FF s, syms, slotOff⟩ f cs.frame.slots cs.mem w₀`, `TrapsExplicit env p cs` (with the `try_call`/`try_call_indirect` trap clauses, and the indirect-call clauses `indirect`/`tryIndirect`: an indirect call of the entered function reaches no function of `p`; all vacuous for a function without them: `TrapsExplicit.of_tryFree`, `TrapsExplicit.of_indirectFree`) | caller of the theorem |

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
* **Entry** `ArgsIn sig args s`: argument `i` in `x (argIdx sig i)` (`abiArgIdx`: x0.. in
  order, the `sret` parameter in x8). Without `sret` it is the former "argument `i` in `x i`"
  (`argsIn_iff_of_noSret`). `lowerCheck`'s entry `Args` (`pre`) uses the same registers;
  `BodyEntry` keeps x0–x8 (`argsIn_body`, `argIdx_lt`).
* **Return**: `LowerShape`/`lowerCheck` lower `abiTerm f B.term`; the certificate makes the
  appended `sret` value available at every `return` (`Cert.term`), so the `rets` returns the
  CLIF values followed by the pointer. The driver's and the layer statements' return clause is
  `PrefixHold vals outs` (the CLIF values are the first ABI returns); the conclusion
  `ArmRefines` is unchanged (CLIF return values in x0.., memory), so for an `sret` function it
  claims the memory the function wrote through the pointer, not the value of x0.
* **Calls**: `gen_call_args` with at most 8 parameters puts argument `i` in
  `x (abiArgIdx …)[i]` (`sigArgLocs_regs`); `gen_call_output` allocates one def per
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
  "Indirect calls").
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
  `lean-backend` flags such functions unverified under `--opt`/`--opt-proven-only` and after
  `i128` legalisation.

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
* **Mid-end and `i128`**: `lstep` does not model `call_indirect`, so `backend_correct_opt`/
  `_opt_proven` and `backend_correct_legal` keep the premise that the (source resp. legalised)
  function has none (`hci`, next to `hnt`); the indirect-call contract is then vacuous.
  `lean-backend` flags `call_indirect` functions unverified under `--opt` and after `i128`
  legalisation (`Opt.Legal.check` rejects indirect calls anyway).
* **Regression file**: `corpus/clif-regress/call_indirect.clif` (a vtable built with
  `func_addr` and dispatched through, a function address returned as a value, `try_call_indirect`).

## The theorem (`FV/E2E/Main.lean`)

```lean
theorem backend_correct {p f k vc vcp rf af fa fb}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F syms slotOff astep env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w))
    (htries : ∀ s, TryCalls f (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w)
      env p)
    (htryInds : ∀ s, TryIndCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w)
      env p (indSigs f))
    -- M6 + M5
    (hM6 : RegLevelCorrect sem F astep vcp af fb)
    -- the shared VCode semantics of each activation (M6's `csem (F s)`)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    -- the callee contract (M6, from `CalleeSound`)
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w) (sem s))
    -- the indirect-call contract (M6, from `XCallsIndOk`)
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    -- the run
    {base ra s w₀ args cs}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff⟩ f cs.frame.slots cs.mem w₀)
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
  E), at most 8 parameters (all in registers), every `call` targets an extern (not a function
  of `p`), every extern of `f` takes at most 8 parameters (`callRegArgs`: no stack-passed call
  arguments; the compiler flags such functions unverified, `Backend.regArgCalls`), and the
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
  slots`, `Γ.slotReg w = sp(w) + Γ.slotOff`, `SlotRel`: slot `id` is at `base + off(id)` with
  `off` from `slotLayout f.slots`. This is M4's `MR` (`MRStable`, `mrStable_holds`).
* **Traps** `TrapsExplicit env p cs`: every trap of the CLIF run from `cs` comes from a `trap`
  terminator or a `div` (explicit check + `udf`/`trapIf` in the code; `stmt`), and the step of a
  `try_call` terminator of the entered function does not trap (`tryCall`). Memory-access traps
  and traps inside externs are excluded: the Arm model has no memory faults, callees are outside
  the theorem (for DSL output traps are unreachable, PLAN.md §3.2).
* **ABI entry** `AbiEntry fb base ra s`: code words of `fb` loaded at `base`
  (`s.program = fb.program base`), pc = base, no model error, x30 = ra outside the code, sp
  16-aligned, code fits the address space. `ArgsIn f.sig args s`: argument `i` in
  `x (argIdx f.sig i)` (low bits): x0.. in order, an `sret` parameter in x8.
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
| `PrepareCorrect (sem s) vc vcp` | M7 | **discharged** by `prepCheck` (`Compiled.prepOk`) + `DriverSem` |

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
clif-subset-v2 E, more than 8 parameters, calls (also `try_call`s) of functions of the same
file, special-purpose parameters other than one `sret` pointer (`abiSigs`), indirect calls
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
3. **Scope extensions**: calls between compiled functions (induction on call depth, using
   `backend_correct` of the callee as its callee contract); stack-passed parameters
   (`InSubset.regParams`); memory-access traps (need a fault model).

## Trusted (not proven)

* Lean kernel, `bv_decide`'s LRAT checker / compiled evaluation (M5, M6 axioms); Lean's and the
  C compiler that run the compiler.
* **Arm model fidelity** (`FV/Arm`, ASL-derived, co-simulated against qemu) and **`Clif.run`
  fidelity** (checked against Cranelift's interpreter and native runs), including the choice
  that CLIF slot addresses are unspecified (`ClifEntry`).
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
```

**Status (M6Insts2, 2026-09-28)**: `hRef`/`hmem` of `backend_correct_m4` are not yet discharged.
csem now falls back to `mspec` (ispec + memory forms) off error-free aligned worlds; `FormOk` must be
narrowed (xzr-destination imm/extended add/sub make `Refines` false as is). See regalloc-proof.md
"Status update (M6Insts2)"; `MemRefines` for `csem` will need `ctx.slotBase = slotOff` and a
GOT premise `syms n = some b → X.sym n 0 = ofNat b`.
