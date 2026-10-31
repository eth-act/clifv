# Deferred work

Work that is deliberately postponed. Each item says what exists already, what remains and how to
pick it up.

For the work towards a compiler verified once with no per-program certificates, see
`docs/TO-PROVE.md` (work packages, dependencies, how to take one). The sections below remain the
detailed background for several of its packages.

## Mid-end `simplify` rule proofs (decided 2026-09-28)

**Decision (owner):** don't block the end-to-end theorem on proving every mid-end rule. The
end-to-end theorem is delivered for the **proven-rules configuration** (`Opt.Config.ruleAllow :=
.proven`, CLI `--opt-proven-only`). Only allow-listed rules contribute rewrites. More rules become
available by proving them and adding them to the allow-list; the theorems don't change.

**Exists (main):**
- Rule data: `Isle.Opt.program`, 1605 rules. E-closure: `Isle.Opt.Closure`, 1357 rules / 1193 roots (1156 `simplify`, 37 `simplify_skeleton`).
- Framework: `RuleOk`, `SimplifyRulesCorrect`, multi-term interpreter soundness, `simplifySound`, the skeleton framework, `simplifySound_proven`, `skeletonSound_proven`.
- Allow-lists: `Opt.provenSimplifyRules`, `Opt.provenSkeletonRules`, `RuleAll.simplifyRulesCorrect_proven`, `RuleAll.skeletonRulesCorrect_proven`.
- Template tactics and the generated constructor lemmas.
- The exact proven set and the per-family recipe are in `docs/contracts/midend.md`, section "Rule proofs".

**Status (2026-10-10, R4, merged in [#212](https://github.com/eth-act/clifv/pull/212)):** 1191 of 1193 roots are proven:
1154 `simplify` and all 37 `simplify_skeleton`. Shifts reach 73/75; only the documented
false originals 84/88 remain disabled. R4 closes all seventeen sound remaining roots
without changing the exported rules, `RuleOk` premises or fuel. Exact masked-sum
guards and symbolic mixed-width rotation/shift identities replace wide SAT problems.
Every new theorem has a concrete witness. All seventeen roots fire in the 3990-function
smoke: 41430 exact, differential and AArch64/Cranelift-native expectations agree;
all optimized functions pass the Cranelift verifier. Instructions fall from 13950
to 9629, versus 12766 before enablement, matching the full-rule diagnostic. Full
compiler/crate builds, 40 axiom audits, native filetests, encoding and E2E gates pass.
Proven-only corpus/runtests remain 4668 → 2287 and 3389 → 3043; all 445 file summaries
are no worse. Legacy unsupported/error cases remain separate. See midend.md "R4".

**Status (2026-10-10, R1, merged in [#211](https://github.com/eth-act/clifv/pull/211)):** 1174 of 1193 roots are proven:
1137 `simplify` and all 37 `simplify_skeleton`. All 258 arithmetic roots are enabled.
R1 closes all twenty-eight remaining roots with unchanged `RuleOk` premises.
High-half extraction, odd modular cancellation and symbolic product identities avoid
wide-product bit-blasting; early type/guard normalization avoids interpreter expansion.
Every new theorem has a concrete witness. All twenty-eight roots fire in the
610-function smoke: 7124 exact, differential and AArch64/Cranelift-native expectations
agree; all optimized functions pass the Cranelift verifier. Instructions fall from
2430 to 1626, versus 2154 before enablement. Full compiler/crate builds, 50 axiom audits,
native filetests, encoding and E2E gates pass. Proven-only corpus remains 4668 → 2287;
runtests improve from 3055 to 3043 (3389 before optimization). All 445 file summaries
are no worse; legacy unsupported/error cases remain separately reported. See midend.md
"R1".

**Status (2026-10-10, R2, merged in [#210](https://github.com/eth-act/clifv/pull/210)):** 1146 of 1193 roots are proven:
1109 `simplify` and all 37 `simplify_skeleton`. All 124 icmp roots are enabled.
R2 closes the fifteen remaining roots with unchanged `RuleOk` premises. Shared
class/decomposition evaluators, typed composition RHS proofs and width-parametric
predicate identities replace the earlier timeout-prone expansion. Concrete witnesses
include sixteen actual RHS executions over a proved fresh-allocation graph.
All fifteen roots fire in the 1890-function smoke: 15740 exact, differential and
AArch64/Cranelift-native expectations agree, and every optimized function passes
the Cranelift verifier. Instructions fall from 6597 to 3595, versus 6127 before
enablement. Full compiler/crate builds, 66 axiom audits, native filetests, encoding
and E2E gates pass. Proven-only corpus instructions now match the all-rules count:
4668 → 2287; runtests improve from 3063 to 3055 (3389 before optimization).
All 445 file summaries are no worse; legacy unsupported/error cases remain
separately reported. See midend.md "R2".

**Status (2026-10-10, R5, merged in [#209](https://github.com/eth-act/clifv/pull/209)):** 1131 of 1193 roots are proven:
1094 `simplify` and all 37 `simplify_skeleton`. All 40 spaceship roots are enabled.
R5 closes all twenty select roots with unchanged `RuleOk` premises, shared typed RHS
proofs and width-parametric signed/unsigned identities. The 426-function CLI smoke
exercises every new root, widths 8–128 and distinct-operand controls. All 4236 exact
interpreter/native expectations agree; the Cranelift verifier accepts all 426 functions.
Instructions fall from 2682 to 1702, versus 2602 before enablement. Full compiler/crate
builds, 47 axiom audits, native filetests, encoding and E2E gates pass. Proven-only
differential counts remain corpus 4668 → 2289 and runtests 3389 → 3063; all 445 summaries
are no worse than baseline, with no refinement/pass errors or verifier rejections.
Legacy unsupported/error cases remain separately reported. See midend.md "R5".

**Status (2026-10-09, R3, merged in [#208](https://github.com/eth-act/clifv/pull/208)):** 1111 of 1193 roots are proven:
1074 `simplify` and all 37 `simplify_skeleton`. All 100 selects roots are enabled.
R3 closes roots 15, 81, 85, 188, 189, 193–196 and 199–202 with unchanged `RuleOk`
premises. The 682-function CLI smoke exercises every new root, all ten integer comparisons
and widths through i128, including mixed-extension and mixed-source-width controls.
All 4438 interpreter/native expectations agree; all functions pass the Cranelift verifier.
Instructions fall from 3146 to 1884, versus 3050 before enablement. Full compiler/crate
builds, 35 axiom audits, native filetests, encoding and E2E gates pass. Proven-only
differential counts are corpus 4668 → 2289 and runtests 3389 → 3063, with no new failures
or verifier rejections. Legacy unsupported/error cases remain separately reported.
See midend.md "R3".

**Status (2026-10-09, R7, merged in [#207](https://github.com/eth-act/clifv/pull/207)):** 1098 of 1193 roots are proven:
1061 `simplify` and all 37 `simplify_skeleton`. All 450 bitops roots are enabled.
R7 closes the masked-OR guard (79) and LLVM-style byte-swap trees (157/170), without
changing their `RuleOk` premises. An opcode-indexed decoder avoids the byte-swap
matcher's earlier branch explosion. The 82-function CLI smoke exercises all three roots:
766/766 interpreter and native executions agree; instructions 392 → 250, versus 336
before enablement; all 82 functions pass the Cranelift verifier. Full compiler/crate builds,
15 axiom audits, native filetests, encoding and E2E gates pass. Proven-only differential
counts are corpus 4668 → 2289 and runtests 3389 → 3069, with no new failures or verifier
rejections; legacy unsupported/error cases remain separately reported. See midend.md "R7".

**Status (2026-10-09, R8, merged in [#206](https://github.com/eth-act/clifv/pull/206)):** 1095 of 1193 roots are proven: 1058 `simplify` and all 37
`simplify_skeleton`. R8 completes all 29 extends roots by proving equality, inequality and
signed comparisons of sign extensions against zero (40/42/44), without adding premises.
The targeted 100-function CLI smoke exercises all three roots: 700/700 executions agree,
instructions 340 → 268 (304 before enablement), no unsupported inputs or pass errors.
All 700 optimized native executions agree with Cranelift. The full proven-only differential
run retains corpus 4668 → 2289 and runtests 3389 → 3071 instructions, with no new failures
or verifier rejections. Full compiler/crate builds, axiom audits, native filetests, encoding
comparison and E2E lowering gates pass; see midend.md "R8" for their scope.

**Status (2026-10-09, R9):** 1092 of 1193 roots are proven: 1055 `simplify` and all 37
`simplify_skeleton`. R9 completes signed i32/i64 `div_const` division/remainder and the four
leading/trailing-zero branch rules, including i128 and reduced counts. Proven-only differential
tests: corpus 4668 → 2289 instructions, runtests 3389 → 3071, no refinement failures or verifier
rejections. All eight new roots fire in a 798-case CLI/AArch64 smoke with exact agreement.
See midend.md "Skeleton rules" for the proofs, witnesses and verification scope.

**Status (2026-10-07, R0 / RuleInfra):** 1055 `simplify` roots are proven and allow-listed: arithmetic 230 of 258, cprop 68 of 68, bitops 447 of 450, icmp 109 of 124, selects 87 of 100, extends 26 of 29, shifts 56 of 75, spaceship 20 of 40 and remat 12 of 12; 29 `simplify_skeleton` roots (`arithmetic.isle` 79, 80, 83, 87, 102, 114, 117, 130-132, 135, 142, 157, 160; `cprop.isle` 32, 38, 44, 50; `skeleton.isle` 7, 9, 22, 26, 33, 37, 44, 50, 53, 56, 80). R0 added the shared infrastructure (an `iabs` `bif` form, the right-hand-side finish for constants made under a type variable, a `truthy` if-let lemma, `u64_bswap*`, `imm64_power_of_two`/power-of-two division and `div_const` magic-number specs `magicU_spec`/`magicS_spec`, low-memory icmp/selects templates) and 43 + 10 roots with it; midend.md "R0" has the details. `E2E.backend_correct_opt_proven` covers exactly these sets. With only these rules enabled (`--opt-proven-only`), corpus instructions fall from 4668 to 2289 (unchanged by R0), runtests from 3389 to 3010 (2926 before R0) and the survey file from 355 to 190 (191). In these sets the new `simplify` rules fire 35 times (`cprop.isle` 269 18 times) and the new skeleton rules 32 times; the latter replace a division by a constant with its shift or multiply-high sequence (cheaper, but more instructions), hence the +84 in runtests.

**Status (2026-10-01, RulesRest):** 1012 `simplify` roots were proven: arithmetic 216 of 258, cprop 61 of 68, bitops 444 of 450, icmp 95 of 124, selects 82 of 100, extends 26 of 29, shifts 56 of 75, spaceship 20 of 40 and remat 12 of 12. **Skeleton (2026-10-01, SkeletonProof):** 19 `simplify_skeleton` roots (`arithmetic.isle` 79, 80, 130-132; `cprop.isle` 32, 38, 44, 50; `skeleton.isle` 7, 9, 22, 26, 33, 37, 44, 50, 53, 56), after the framework fix below. With these rules, corpus instructions fell from 4668 to 2289 (2322 without skeleton rules; all rules: 2287), and runtests from 3389 to 2926 (was 2976).

**Findings:** `shifts.isle` 84 and 88 are false under the CLIF semantics (shift constants above the type width make `shift_amt_to_type` pick a type wider than `ty`, so the rule builds an ill-typed `ireduce`/`sextend`; midend.md has the example). The skeleton framework gap (node facts of the start state vs. refinement in later valuations) is closed by a reads-defined premise: `SkeletonSound`/`SkelRuleOk` assume the instruction's reads (`Opt.skelReads`) are defined when the rules run, and `runSkel_spec` discharges the undefined case (known values never change, so the original is stuck); see midend.md "Skeleton rules".

**Remaining:** only the two false shift originals 84/88. Every sound original root is proven. Corrected masked upstream variants have not been adopted; midend.md records the counterexample and exact coverage. Roots per family:

| Family | Roots |
| --- | --- |
| bitops | 450 |
| arithmetic | 258 |
| icmp | 124 |
| selects | 100 |
| shifts | 75 |
| cprop | 68 |
| spaceship | 40 |
| extends | 29 |
| remat | 12 (all proven) |
| skeleton (incl. div_const) | 37 (all proven) |

**How to add a family:** follow the recipe in midend.md "Rule proofs":
1. Write a per-family file with `RuleOk` proofs over an abstract `p` with `Data p`.
2. Add the rule ids to `Opt.provenSimplifyRules` (skeleton rules: `Opt.provenSkeletonRules`, `FV/Opt/RuleAllow.lean`) and import the new file in `FV/Opt/Proof/RuleAll.lean` (a skeleton rule needs `ok_rule_X : SkelRuleOk p rule_X`).
3. Run `scripts/opt-difftest.sh` with `--opt-proven-only` and record how many instructions the proven subset removes.

Families are independent and can run in parallel, one agent per opts file.

**Also deferred in the mid-end** (from midend.md "Gaps"):
- alias analysis (redundant-load elimination, store-to-load forwarding);
- merging identical trapping instructions;
- elaboration-based sinking and general rematerialisation;
- full e-class visibility for later matches;
- the passes on functions with `call_indirect`: the well-formedness check `Opt.check` rejects
  them, so they only get unreachable-block removal (`Opt.optimizeExe` and its theorems, S1, cover
  them; accepting them needs the `call_indirect` obligations of `GvnEditX`/`SimpSimX`, vacuous
  today).

## i128 legalisation: what `E2E.backend_correct_legal` does not cover (2026-09-30)

Legalised `i128` functions are inside the end-to-end theorem (`E2E.backend_correct_legal`,
`docs/contracts/legalize128.md`; survey 31 and runtests 159 functions reported verified).
Deferred:
- ~~composing the legalisation with the mid-end theorems~~ Done (S2, #26, [#245](https://github.com/eth-act/clifv/pull/245)):
  `E2E.backend_correct_legal_opt` (`--opt-proven-only` reports legalised functions verified) and
  the optimising executable compiler's `Link.compileExeOpt_correct_source{,_peak}`;
- in `Link.compileExe_correct_source` (and `_source_peak`, the `Link.DeadCleanup` variants, L1f
  #217): the outside environment's `HelperOk`/`ExtLegal`/
  `EnvKeepsBounded` when a source function mentions `i128` and `sigOf = none` with indirect
  calls (environment contracts); the source run's memories below `2^64` (`Clif.run`'s bump
  allocator can exceed it; proven for slotless programs, `bounded_of_noSlots`; ~~for the shipped
  compiler~~ derived, A2/B1 #407: `Link.DeadCleanup.compileExe_correct_source{,_peak}_nobnd`,
  `Front.bundle_correct_{source,raw}{,_peak}_nobnd`, with callee traps
  `compileExe_correct_source_trap{,_peak}_nobnd`, `Front.bundle_correct_{source,raw}_trap{,_peak}_nobnd`;
  baseline `Link.compileExe_correct_source{,_peak}_nobnd` (#434), optimising
  `Link.{DeadCleanup.}compileExeOpt_correct_source{,_peak}_nobnd`; with unwinding
  `Front.bundle_correct_raw_unwind_src_nobnd`; still a premise of the CLIF half
  `Front.raw_legal_unwind`, which has no stack premise) and, for traps,
  the source run's `NoMemTrap` and the target run's `TrapsExplicit` (run conditions);
- runs that trap inside a `__*ti3` helper (`i128` division by zero, `sdiv MIN, -1`): the
  backend theorem excludes extern traps (`TrapsExplicit` of the legalised run). Per function
  they are covered since S9a (#33, e2e.md "Callee traps"): `E2E.backend_correct_final_cleanup_trapcall`
  takes `TrapsExplicitC` (callee traps of `call`/`call_indirect` allowed) and the helper's
  trap contract `XTrapsOk` (the helper does not return on the machine), and ends at the call
  state of the trapping helper; the legalised whole-program and executable theorems still take
  `TrapsExplicit` (S9c/S9d);
- a correct `umulhi`/`smulhi` expansion at `i128` (now unsupported), ~~`try_call` with `i128`
  in the validator~~ (done, legalize128.md "`try_call` and `call_indirect`"), `i128`
  `umul_overflow`/`smul_overflow` and atomics (~~`uadd`/`sadd`/`usub`/`ssub_overflow`~~ done,
  S4: pure patterns, legalize128.md "Overflow ops at `i128`"); ~~stack-passed `i128`
  arguments~~ done
  (S4, #28: `expandGroups` places pairs beyond `x0..x7` on the stack as Cranelift does; still
  unsupported: a later integer argument Cranelift passes in `x7`, legalize128.md "Stack-passed
  `i128` arguments").

## Completeness of `Opt.Legal.check`: what `Opt.Legal.Complete.Pre` excludes (2026-10-02)

`Opt.Legal.Complete.check_complete`, `Opt.Legal.legalize_refines` and
`E2E.backend_correct_legal_direct` are proven (`docs/contracts/legalize128.md`, "Completeness").
Deferred:
- `call_indirect` with an `i128` signature and `try_call_indirect`: the pass expands them but
  `check` has no plan for them (`callInd` needs plain operands and the same call-site
  signature; `termOk` has no `try_call_indirect` case). Either extend the validator and its
  soundness proof, or make the pass throw (the functions would become unsupported instead of
  unverified);
- `noSelf` (a statement reading its own result) and the `f`-only conjuncts of `check` (`defs`,
  `ids`) are preconditions; ~~a decidable `Pre` is not implemented~~ done (S6, 2026-10-15):
  `preB_iff`, `check_complete_of_preB` (`FV/Opt/Proof/LegalPre.lean`); the compiler keeps
  running `check` as a double-check.

## `sret`: what `E2E.backend_correct_final` does not cover (2026-09-30)

Functions with a struct-return pointer and calls of `sret` callees are inside the end-to-end
theorem (`docs/contracts/e2e.md`, "`sret`"). Deferred:
- ~~x0 holds the pointer on return~~ (done, S7 #31, 2026-10-22): `E2E.backend_correct_final_abi`
  / `backend_correct_final_sret` (premise `sretStableB`, met by every `sret` function of fv-demo,
  the survey and `examples/deps`); the dead-cleanup copies `backend_correct_final_cleanup_abi`
  / `_sret` (`FV/E2E/SretReturnCleanup.lean`); the typed copies `backend_correct_finalT_abi` /
  `_sret` (`FV/E2E/SretReturnT.lean`); the executable theorem `compileExe_correct_abi`
  (`FV/Link/DeadCleanupExeAbi.lean`); `backend_correct_opt{,_proven}_abi`,
  `backend_correct_legal{,_env,_wide,_env_wide}_abi`, `backend_correct_legal{,_env}_cleanup_abi`;
  with unwinding
  `backend_correct_final_unwind_abi` / `_unwind_sret` (premise `sretStableXB`: also no handler
  block binds the `sret` value; not yet measured on the crates). Still with the CLIF-values
  conclusion only: the linked `_unwind` theorems, the other legalisation variants (`_direct`, `_opt*`, `_wide_cleanup`) and
  `OptX`/`_opt_exe*` (the same `_abi` copy of their composition);
- `vmctx`/`sarg` parameters (flagged unverified, `sigAbiOk`): not emitted by cg_clif on aarch64
  (0 functions in fv-demo, the survey, `examples/deps`, vendor; `StructArgument` only for
  x86-style `byval` arguments, `VMContext` is wasmtime's). (`sret` with 8 further parameters is
  covered since agent/stack-tls-proof: `InSubset.regParams` is gone.)

## Stack-passed arguments: what `E2E.backend_correct_final` does not cover (2026-10-01)

Stack-passed parameters and stack-passed arguments of `call`, `try_call` (agent/last-unverified)
and `call_indirect`/`try_call_indirect` (S5, #29: `InSubset.indSigs` is `sigAbiOk` only) are
inside the end-to-end theorem (`docs/contracts/e2e.md`, "Stack-passed parameters and `call`
arguments", "Stack-passed arguments of indirect calls"). Deferred:
- the callee contract `XCallsOk` relates the world the callee returns by `Rel.holds`, including
  `OutRel` of the caller's outgoing area; that the callee does not touch live CLIF memory in it
  is part of the environment contract, not derived from AAPCS64.

## Linking: what `E2E.backend_correct_linked` does not cover (2026-10-02)

Proven (`docs/contracts/e2e.md`, "Linking"): whole-program CLIF runs are per-function runs under
`Clif.linkEnv` (`Clif.runLoop_link`, with `call` and `try_call` between program functions,
recursion included), and `E2E.backend_correct_linked` states a function's Arm code against the
whole-program run with the program callees' contracts (`CalleeOk`, `XCallsOk (linkEnv …)`) as
premises. Deferred, in order:
- ~~**Callee contract with a dead stack.**~~ Done (agent/callee-fix): `CalleeOk F K X H S`
  compares the world outside `F = frameW K …` (the frame and the callees' `K`-byte dead stack
  below the body's `sp`), keeps the frame only outside the dead stack (`CallSoundCtl`), and is
  required only at the compiled code's call sites (`VCode.CallSite`); `TlsOk` likewise. Witness:
  `E2E.calleeOk_witness`/`final_contracts_witness` (`FV/E2E/NonVacuity.lean`), a callee pushing
  two frames below `sp`. The flags stay part of the world, produced by `X.call`.
- ~~**`try_call` payload registers.**~~ Done (agent/trycall-contract): the payload defs of a
  `try_call`'s call are havocked on the normal return (`havocFrom`), the checker forgets them on
  the normal-return edge only (`CheckCtx.edgeForget`), and `CalleeTryOk` constrains only the
  results at the `try_call` sites (`VCode.TrySite`). Witness: `E2E.calleeTryOk_witness`,
  `E2E.backend_correct_final_try_witness`.
- **Arm-level linking: done for the scope of `LinkSys.Ok`** (agent/arm-link,
  `E2E.backend_correct_program`): exact world (one VCode outcome per body-entry world,
  `backend_correct_world`), frame locality (`G` kept), the induction on depth (`LinkSys.thm`).
  Witness done (`E2E.LinkWitness.backend_correct_program_witness`, `FV/E2E/NonVacuityLink.lean`;
  it found `raCall` unsatisfiable for every program with a call, now stated per call-site
  callee). Widened (agent/link-widen, e2e.md "Widening"): `try_call` between program functions
  (normal returns); `sret` between program functions; stack-passed arguments between program
  functions; direct self-recursion through the `cargo fv` alias in one copy (agent/link-scope2:
  the alias at the function's address, `RaOk`, M6's post-call trace `PostTrace`, `linkedCall`
  takes the first return with the caller's `sp`);
  indirect calls (`call_indirect`, `try_call_indirect`, GOT `blr`) between program functions
  (the caller has no address itself; register-only, non-`sret` indirect callees; the M6 callee
  contract now holds for the call instruction at the pc, `CallAt`); undeclared indirect callees
  (vtables, agent/link-scope: `Clif.Env.names`, `linkEnvN` resolves program-wide,
  `LinkSys.MayCall`; `blrRegs`/`callRegs` constrain only the defs a site has); calls through
  the GOT pinned to their symbol (agent/link-scope2: M6's VCode semantics `csemV` with the static
  GOT analysis `GotV`, `LinkSys.BlrTo`: a GOT site constrains only its symbol's function); `i128` pairs
  between the functions of a legalised program (`Opt.Legalize128`;
  per-function composition with `backend_correct_legal`, `a2_legal`); program callees with
  stack slots or an outgoing-argument area (stage 2: the VCode non-interference
  `backend_correct_world_ni` from the memory rules' read footprint and pinned calls, the
  premises `baseNI`/`baseTlsNI` needed only then; the slot-placement oracle `Clif.Mem.place`,
  a trusted-semantics change, with the entry premise `hpl` placing the reference run's slots at
  the compiled frames — CLIF leaves slot addresses unspecified, so this picks one legitimate CLIF
  behaviour; witness callees `t` and `u`). Remaining:
  - ~~**The `i128` source program as a whole**~~ (done, S3, 2026-10-15):
    `E2E.LegalProgram.legalProg_refines` (`FV/E2E/LegalProgram.lean`) relates the original
    program's whole-program run to the legalised program's, by induction on the source fuel
    with two environments (`check_refines2`); `Link.compileExe_correct_source` composes it with
    `compileExe_correct` (premises: `docs/contracts/legalize128.md`, "The executable compiler on
    the original source program").
  - reachable indirect callees (whose
    signature matches an indirect call of the caller, `IndSigMatch`: parameter types and
    purposes, return types since agent/sret-purpose; agent/link-scope2 restricted `indSig` to
    those, agent/crate-check3 `blrRegs`/`blrTry` to `IndTo`) with stack-passed or `sret`
    parameters; a declared function entered through a pointer whose call-site signature has its
    parameter types but not its purposes (`indSig` still constrains it: since agent/scope-widen
    (#89 (c)) the per-function run's `callExternAt` checks the purposes against the linked
    environment's `sigOf`, but the non-interference contract's pinned indirect call (`CallLg`,
    `xni`) records only the parameter types, so `indSig`'s `DeclN`/`IndTyMatch` disjunct stays).
  - float parameters; a depth-free machine (monotonicity of `linkedCall` in the depth, needs base
    hooks preserving errors). (A function calling itself under its own name: done, #88, native
    self-calls in function-free activations; its executable theorem: L1d, "Recursion" below.)
  - ~~**Indirect calls of a known function admitting an `sret` callee**~~ (done,
    agent/sret-purpose, e2e.md "Widening" 11): `Clif.stepCallIndirect` requires the parameter
    purposes to match (`Clif.Signature.abiMatch`), so `fv-demo`'s two `catch_unwind` shims (and
    their 4 callers) pass; `fv-demo` is whole (551 of 551). A CLIF value-flow invariant (a
    `func_addr` result holds its symbol's address at the uses it dominates) would still narrow
    `MayCall` at calls of known functions whose signature matches several address-taken ones.
  - **Crate-level instance** (agent/crate-check, `FV/E2E/LinkCheck.lean`, `cargo fv
    link-proof`, e2e.md "Crate-level instance"): an entry-level instance for a crate function
    (the entry premises of `ProgStmt` for concrete arguments and a CLIF entry memory holding the
    crate's data objects, as `backend_correct_program_witness` does for its `f 41`); the image
    premise `himg` with the relocated words of the process image (`imgMem` is the unrelocated
    encoding; relocation in Lean, or relocation-independence of the machine); moving
    `NonVacuityLink.lean` onto `LinkCheck` (it keeps its own copy of the checks).
- **Exact world of a call.** (superseded for program callees by agent/arm-link) `X.call` is a function of the arguments and the world and must give
  the exact def registers and world of the hooked callee; a compiled callee's theorem fixes only
  the low bits of its results and the live CLIF bytes. Either make `csem`'s call clause
  relational (a set of outcomes; driver and M6 refactor) or prove non-interference of compiled
  code (results/world depend only on the arguments, unmasked registers and memory outside
  `F ∪ D`), e.g. from `RegLevelCorrect`'s final-memory clause and the determinism of the VCode
  run once `BodyEntry`'s memory premise is relaxed to agreement outside the caller's frame.
- **Frame locality of the conclusion.** `ArmRefines` (returned) should also state that memory
  outside the live CLIF allocations and the callee's own frame, x18 and the other unmasked
  registers are unchanged (threaded through M4's `MRStable`), which `CalleeOk`'s `FrameKeep`
  and `SameWorld` need.
- **Slot placement of callees.** `Clif.run` allocates a callee's slots with its bump allocator,
  the Arm code at `sp`-relative addresses; for a callee whose slot addresses escape, `linkEnv`'s
  outcome differs from the code's. Needs a slot-placement oracle in the whole-program semantics
  (trusted-semantics change) or a relocation-invariance lemma for runs whose slot addresses do
  not escape.
- **Then the induction.** Define the linked hook by depth (`H_{d+1}.call (some g) s`: run `g`'s
  code by `ArmStepX X_d H_d fa_g` from the `bl` state with `g`'s image, until its return) and
  discharge `hC`/`hX` for program callees from each callee's `backend_correct_final`, by
  induction on the depth (bounded by the whole-program fuel, as in `runLoop_link`).
- `call_indirect`/`try_call_indirect` between program functions (the whole-program
  `stepCallIndirect` resolves addresses among all functions and externs of `P`), `return_call`
  (a function's `return_call` of itself: done, as a loop, "Tail calls" below; of another
  function: open there), and traps inside program callees.

## Completeness of the lowering validator `lowerCheck` (done, 2026-10-05)

Done on agent/lower-complete (TO-PROVE V1/V2): `lowerCheck_complete` on `Dominated`/`LowerScope`
input, `E2E.Compiled.of_lower` (see `docs/contracts/e2e.md`, "Validator completeness"). The
feasibility note's two code changes were made (V1a: `inFix` fuel-bounded; additionally
`lowerFunction`'s alias resolution keeps the referencing register's class, since otherwise
completeness would need a per-rule register-class property). The def-set property became
`stmt_flow`, decided over the rule data by an abstract interpretation (`IselFlowCheck`) rather
than per-rule lemmas. Remaining: the input conditions join `InScope` for the totality work
(TO-PROVE L1/L2); `lowerCheck` still runs as a double-check.

## Recursion: the stack premise of `compileExe_correct_depth` (2026-10-15)

Done (L1d, #204, #215; e2e.md "Recursive programs"): `Link.compileExe_correct_depth`
covers every entry, recursive ones included, with `frameDrop (art S.input f).af + S.input.D * M`
bytes of stack for a whole-program CLIF run of at most `M + 1` steps (no call-graph premise), and
`Link.compileExe_correct_peak` with `frameDrop (art S.input f).af + S.input.D * d` bytes for a run
of peak call depth `d` (`Clif.DepthLe`: no state it reaches has more than `d` callers), whatever
its fuel: the linked system carries its callee runs (`LinkSys.crun`, `CrunOk`), the induction runs
on the depth with the fuel fixed (`Clif.runD`, `Clif.linkEnvD`, `Clif.runLoop_linkD`). On the
original `i128` program (L1f, #217): `Link.compileExe_correct_source_peak`, stack from the
**source** run's call depth (the legalisation keeps `DepthLe`, `legalProg_refines_depth`); for
the shipped compiler `Link.DeadCleanup.compileExe_correct_peak`/`_source_peak`.
Deferred:
- **Exact frames.** Each level is charged the largest frame `D`; charging the frames actually
  live along the executed call derivation needs a budget indexed by the run, not `LinkSys.Budget`
  (which quantifies over every syntactic callee).
- Neither covers divergence or stack overflow (no theorem about a run that exceeds the stack);
  `TrapsExplicit` still restricts traps inside callees (S9: per function S9a covers the callees
  of `call`/`call_indirect`; the linked and executable theorems are S9c/S9d).

## Tail calls: what `compileExeTail_correct` does not cover (S8a, #32, 2026-10-22)

Done (TO-PROVE S8; e2e.md "Self tail calls as loops"): a function's `return_call` of itself
(its own declaration, with its parameter and return types), in a function without stack slots
and without `try_call`, becomes a jump to its first block (`Opt.TailLoop.loop`; a new entry block
jumps there), so the frame is reused; `Opt.TailLoop.TailRel.refines` (the transformed program's
run refines the input program's and keeps its call depth), `Link.DeadCleanup.compileExeTail`
(`compileExe` on `LinkSpec.tail`) with `compileExeTail_correct`, `compileExeTail_correct_peak`
(the input run's peak depth: a self tail call adds no caller, so the stack does not grow per
tail call), `compileExeTail_total_reach_input`/`_total_ld`; `lean-link` runs it on inputs with a
self tail call. Deferred:
- **`return_call` of another function** (mutual tail recursion, tail calls of externs): the
  backend rejects `return_call` (`Isel.termData`: "not in E"). Needs a VCode terminator (the
  callee contract `X.call`, then the function's return with its results), its regalloc check
  (fixed argument uses, a terminator like `rets`) and emission (the epilogue, then `b sym` /
  `br xN` with a register outside the arguments and the callee-saved ones), an Arm-level tail
  hook (`ArmStepX` at a `b` to a symbol: the callee runs from the caller's entry `sp` and returns
  to x30) with a `CalleeOk` variant at tail sites, the per-function theorem's conclusion
  through the callee's return, and in `LinkSys` a budget `Budget f ≥ Budget g` (no frame) at a
  tail site with an induction on (depth, fuel), a tail call staying at its depth.
- **`return_call_indirect`**: not in `Clif.Syntax` (parser, `Clif.run`, oracle runs).
- **The `tail` calling convention**, which Cranelift's verifier requires for `return_call`
  (aarch64: arguments and results from x2, callee-popped stack arguments, no `sret`): rejected
  by the backend. `Clif.run` does not check calling conventions, so `system_v`/`fast`
  functions with a self `return_call` are in our CLIF.
- **Self tail calls with stack slots or `try_call`**: the input run frees and re-enters the
  slots (fresh, uninitialised, at new bump addresses without the placement oracle); the new
  entry block's parameters raise `Function.freshValue`, where `try_call` binds its results.
- **Source and `--opt` variants**: `ProgCtx` (the `i128` legalisation's source domain) excludes
  `return_call`, so `--verified` (`SrcScopeB`, `linkFreeB`) rejects inputs with one; the
  optimising compiler is not composed with the transform. MidendM1c's shape guard
  (`keepsShapeB`: branch folding may make the only `return_call` block unreachable, then
  `optimizeExe` keeps its input) is unaffected: after the transform no self `return_call` is left.
- Premises of the composition: the externs keep the slot-placement oracle
  (`Clif.EnvKeepsPlace`) and the input run's entry has a consistent oracle stack
  (`Opt.TailLoop.SpsOk`: the entry's stack pointer is what entering the function from the
  stack below pushes, as for every activation `Clif.run` enters; vacuous without the oracle).
- Rust inputs: cg_clif emits no `return_call` (`TerminatorKind::TailCall` is a `span_bug!` in
  `rustc_codegen_cranelift/src/base.rs`); none of the fv-demo, survey or deps functions has one.

## Totality on input conditions: what remains (L1e, #216, 2026-10-16)

Done: `Link.compileExe_total_reach` (`FV/Link/ExeInputReach.lean`, and
`Link.DeadCleanup.compileExe_total_reach`) decides every premise of `compileExe_total` on the
inputs: `CallPageReach` (the `bl`/`adrp` targets of the compiled relocations) follows from
`reachOkB`, a condition on the CLIF functions and the link map, by **name provenance**
(`relocOk_tab`): the compiled code of `f` relocates a `bl` only against an external function `f`
declares and an `adrp` pair only against a name `f` declares with a declared offset (`0` or a
global value's offset). The ISLE part is an abstract interpretation of the exported rules
(`FV/Backend/Proof/RelocProv*.lean`: names enter values only through `func_ref_data` and
`symbol_value_data`; table and root rules kernel-checked in chunks), the rest follows the
instructions through `prepare`, `DeadCleanup.prune`, `lowerRFunc`, `emitFunc` and `layout`.
Coarseness of `reachOkB`: every external function name is asked to be a `bl` target (also one
only `func_addr` reads), and every declared name with every declared offset an `adrp` target; the
abstraction does not pair a name with its own offset nor separate colocated from GOT accesses.
All hold on the survey executables tried (66 and 493 functions); a finer relational analysis
would only matter for executables over 128 MiB of text or offsets near `±4 GiB`. Remaining:
- **The driver's layout (done, L1g item 3, #228).** `lake exe lean-link` no longer reads sizes
  (`sizes.txt` is gone): it compiles `placedPar` of the bundle's spec, the Lean compiler's layout
  (`LinkSpec.placedPar_eq : S.placedPar = S.placed`, `DeadCleanup.placedPar_eq`,
  `FV/Link/PlacedEq.lean`), so the spec it compiles is the totality theorems' by construction.
  Still open: the region object rust-lld places is `lean-backend`'s, compiled per unit; `symsOkB`
  checks that its functions sit at the Lean layout's offsets.
- **`PT_TLS`.** `tlsOkB` asks for a `PT_TLS` segment even when no function has a `tls_value`
  (every std executable has one); dropping it for TLS-free programs needs the instruction-level
  step of the provenance chain (`RelocProvEmit`) for `elfTlsGetAddr` (`lowerCheck` already gives
  `!hasTls f → !vc.hasTls`).
- **rust-lld itself** stays a tool whose output `file0` is an input with decidable conditions
  (`file0OkB`); a verified Lean static linker for the outside objects (L2b stage 3) would remove it.

## Lowering totality: what `InScopeIn` still leaves (V7, #226, 2026-10-16)

Done (TO-PROVE V7): `lowerFunction` and `prepare` succeed on input conditions
(`Prg.lowerFunction_ok_input`, `Prep.prepare_ok`); `InScopeIn` (`fnScopeInB`: `driverInB`,
`iselInB`, `sizeOkB`, `extendsWidenB` for `lowersB`) implies `InScopeP`, and
`Link.DeadCleanup.compileExe_total_reach_input` takes it; since L1g (#228) `Link.compileExe` checks
`InScopeIn` and its totality theorems (`compileExe_total{,_input,_reach}`) take it.
`lean-link --verified` checks `fnScopeInB` and `addrSlotsInputB`. Since L1g item 2 (#228)
`InScopeIn` runs no compiler stage: its program-level part `progScopeInB` replaces `addrSlotsInB`
(which asked whether `lowerFunction`'s output has an outgoing-argument area, `outAreaB`) by
`addrSlotsInputB`, the same disjunction as if every function had an area. Deferred:
- **A sharper `addrSlotsInputB`.** It rejects a program with an indirect call, address-taken
  functions with stack slots and no program callee with slots even when no function has an
  outgoing area. Admitting it needs an input-side bound on the lowering's outgoing area (`outAreaB f`
  → some call of `f` passes arguments on the stack), i.e. signature provenance through the ISLE
  abstract interpretation (`IselPrg` records only `SigOk` for `.sig` values). No fv-demo or survey
  executable is in that case.
- **`maxTryItems`.** `iselInB` bounds every exception table to 8 items, a proof-convenience bound
  (the table checks the `try_call` roots for up to 8 items), not a Cranelift rule; every corpus
  and crate function meets it.
- **The shipped compiler's check.** `Link.DeadCleanup.compileExe` (@codygunton's,
  `FV/Link/DeadCleanupCompile.lean`) still checks `InScopeP` (with `lowersB`); `Link.compileExe`
  checks `InScopeIn` since L1g (#228; its totality premises strengthened from `InScopeP` to
  `InScopeIn`, the acceptance sets equal on the corpus and the crates). The same one-line change
  (`inScopeInPar` for `inScopePar`) is proposed for the cleanup variant on #140.
- **Kernel witness of `dominatedB`.** `backend_correct_final_total_input_witness` takes
  `dominatedB` as its premise: the availability fixpoint `inFix` uses `Std.HashMap`/`Std.HashSet`,
  which the kernel does not reduce (`USize`); `lean-e2e-check` evaluates it on every function.
- **Proof engineering.** `IselPrgLe` derives `ReflBEq`/`LawfulBEq` for `CTy`/`OK` globally;
  `IselPrgHand`'s `handIds_program` decides over the rule ids of all rule lists; the table check
  could evaluate `aRule` once per rule (the soundness proof would follow).

## Frontend boundary: what stays trusted after T7b/T7c (#221, 2026-10-16)

T7b/T7c are done (docs/contracts/frontend.md): cg_clif, patched by
`scripts/patches/cg-clif-extnames.patch`, writes each dump's external-name table and the module's
declarations; the decoding is `Front.decodeFn` (Lean) with `Front.rawLink_eq_link`, and
`clif-data-export`'s order-based identity recovery and `normalize.py` are gone. Deferred:

- **cg_clif and the patch** stay the trusted frontend (out of scope, TO-PROVE §1.3). The patch is
  applied to the nightly's own cg_clif sources by `scripts/build-cg-clif.sh`; `cargo fv` needs
  that build (the shipped `rustc-codegen-cranelift-preview` writes no tables). Upstreaming a dump
  option to cg_clif would remove the local build; not proposed.
- **Object reading.** `clif-data-export` still reads the data objects (bytes, `R_AARCH64_ABS64`
  relocations) from the object; the binary check compares the reached ones with the executable.
  A structured data export from cg_clif (`DataDescription` at `define_data`) would move this into
  the frontend too; not needed for identities.
- **Stage selection.** No theorem relates `*.opt.clif` to `*.unopt.clif`; the retry compiles the
  optimised dump when the unoptimised code references a symbol cg_clif's object neither defines
  nor references.

## Threads: what `E2E.backend_correct_final` does not give (T2, #38, 2026-10-18)

`Concurrency.ProgE2E.program_correct` (#303, `docs/plans/atomics.md` §3c) states program-level
correctness of race-free multi-threaded programs on Armv8 under the per-thread contract
`ProgE2E.Realizes` (the compiled thread's memory events embed the CLIF thread's). The per-thread
`backend_correct_final` cannot discharge it:

- **No interference.** It is a whole-run theorem: `Clif.runLoop` reads its own memory and an
  extern's result is a function of its arguments and the memory, so other threads' writes between
  a thread's steps (atomics, spin loops, message passing) are outside it, on both sides.
- **No footprint.** It constrains only the final memory (`MemAgree`), not what the compiled code
  touches before it returns, so even non-communicating threads do not compose.

Remaining (T2h, #311; plan `docs/plans/atomics.md` §3e): re-prove the isel (`IselSim`/driver),
`prepare` and register-level (`RegLevelCorrect`) layers as footprint-preserving simulations with
interference (CASCompCert, Jiang et al. PLDI 2019). Layer 0 is done: `Realizes` follows from
per-thread refinements (`ThreadRefine.realizes_of_threads`), and refinements compose across
layers (`ThreadRefine.Refines.trans`). The backend layers 1–4 are open, so #38 stays open. The multi-threaded CLIF semantics has
per-thread allocation metadata, no step for extern calls that touch memory, and one `tls_value`
instance; widening those is part of the same item.

## SIMD lane operations (S12 phase B, 2026-10-22)

S12 phase A (`docs/plans/simd.md`) covers vector data movement: vector types, `load`/`store`,
parameters, returns, calls and `bitcast`. Lane semantics and vector arithmetic (`splat`,
`extractlane`, `insertlane`, vector `iadd`/`imul`/compares/shifts, widen/narrow, `shuffle`,
`swizzle`, float lanes) are deferred: cg_clif implements SIMD intrinsics lane by lane through
memory, so no function of `examples/deps`, the survey, fv-demo, vendor or core/alloc has such a
vector instruction (`scripts/simd-scan.py`, 2026-10-22). They are needed only by Cranelift's
SIMD runtests (177 files) and hand-written CLIF. Needed for them: `Clif.run` lane semantics
(decisions recorded in `simd.md` §2), the Arm Advanced SIMD classes LNSym had and the port
dropped (`Advanced_simd_{extract,permute,shift_by_immediate,table_lookup,three_different}`,
compares and float lanes in `three_same`/`two_reg_misc`), co-simulation, and the vector ISLE
roots (138 excluded root rules mention vector types). Start when a measured crate needs it.

## std through `cargo fv --build-std`: what stays outside (T3, #39, 2026-10-22)

`cargo fv --build-std` compiles std's Rust crates like dependencies (`docs/plans/std.md`). Left:

- **musl libc** (C, no C → CLIF path), **libunwind** (C/asm, its model already trusted, S10f),
  **compiler_builtins** (cg_clif cannot compile its `f128` code; kept on LLVM) and the
  **allocator shim** `__rust_alloc` & co. (cg_clif emits it without a CLIF dump; T3b).
- **The 128-bit atomic types** are removed from core by cg_clif's own stdlib patch (cg_clif cannot
  compile 128-bit atomics); crates using `AtomicU128`/`AtomicI128` do not build with
  `--build-std`.
- **The executable theorem with std in `P`**: 17–18 functions of std/test (and one of fv-demo whose
  indirect calls can now reach std functions) fail `InScopeP`'s `indB`/`callScopeB`; `--verified`
  leaves them out of the region per executable (T3c), so they run cg_clif's code. Widening
  `indB`/`callScopeB` (S5) would bring them in. `link-check` still takes hours on a
  ~30k-function region (T3d; `lean-link` takes 12 min).
- **musl's API**: the 170 C/libcall names the region references (`docs/plans/std.md` §3.1).

## Other deferred items

- **M3 validator** (Cranelift's own machine code vs CLIF, per function): paused on branch `agent/validator`. Only needed to ship Cranelift's bytes with assurance.
- **M3b** (Lean-optimised vs Cranelift-optimised CLIF comparison): optional, not started.
- **DSL `compile_correct` (M2):** paused on branch `agent/m2proof`.
- **Rust route extras:** data objects via a cg_clif fork, panic/`mem*` contracts, `dyn`. See `docs/research/rust-clif-survey.md`.
- **After M7 (PLAN.md):** SIMD, RISC-V, a verified frontend.
