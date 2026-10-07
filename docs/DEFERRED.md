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

**Status (2026-10-01, RulesRest):** 1012 `simplify` roots are proven and allow-listed: arithmetic 216 of 258, cprop 61 of 68, bitops 444 of 450, icmp 95 of 124, selects 82 of 100, extends 26 of 29, shifts 56 of 75, spaceship 20 of 40 and remat 12 of 12. **Skeleton (2026-10-01, SkeletonProof):** 19 `simplify_skeleton` roots are proven and allow-listed (`arithmetic.isle` 79, 80, 130-132; `cprop.isle` 32, 38, 44, 50; `skeleton.isle` 7, 9, 22, 26, 33, 37, 44, 50, 53, 56), after the framework fix below. `E2E.backend_correct_opt_proven` covers exactly these sets. With only these rules enabled, corpus instructions fall from 4668 to 2289 (2322 without skeleton rules; all rules: 2287), and runtests from 3389 to 2926 (was 2976).

**Findings:** `shifts.isle` 84 and 88 are false under the CLIF semantics (shift constants above the type width make `shift_amt_to_type` pick a type wider than `ty`, so the rule builds an ill-typed `ireduce`/`sextend`; midend.md has the example). The skeleton framework gap (node facts of the start state vs. refinement in later valuations) is closed by a reads-defined premise: `SkeletonSound`/`SkelRuleOk` assume the instruction's reads (`Opt.skelReads`) are defined when the rules run, and `runSkel_spec` discharges the undefined case (known values never change, so the original is stuck); see midend.md "Skeleton rules".

**Remaining:** arithmetic 42, cprop 7, bitops 6, icmp 29, selects 18, extends 3, shifts 19 (2 of them false), spaceship 20, skeleton 18 (power-of-two and `div_const` division sequences, `icmp.isle` 461-475, `skeleton.isle` 80; midend.md "Skeleton rules"). midend.md lists them with reasons. Roots per family:

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
| skeleton (incl. div_const) | 37 |

**How to add a family:** follow the recipe in midend.md "Rule proofs":
1. Write a per-family file with `RuleOk` proofs over an abstract `p` with `Data p`.
2. Add the rule ids to `Opt.provenSimplifyRules` (skeleton rules: `Opt.provenSkeletonRules`, `FV/Opt/RuleAllow.lean`) and import the new file in `FV/Opt/Proof/RuleAll.lean` (a skeleton rule needs `ok_rule_X : SkelRuleOk p rule_X`).
3. Run `scripts/opt-difftest.sh` with `--opt-proven-only` and record how many instructions the proven subset removes.

Families are independent and can run in parallel, one agent per opts file.

**Also deferred in the mid-end** (from midend.md "Gaps"):
- alias analysis (redundant-load elimination, store-to-load forwarding);
- merging identical trapping instructions;
- elaboration-based sinking and general rematerialisation;
- full e-class visibility for later matches.

## i128 legalisation: what `E2E.backend_correct_legal` does not cover (2026-09-30)

Legalised `i128` functions are inside the end-to-end theorem (`E2E.backend_correct_legal`,
`docs/contracts/legalize128.md`; survey 31 and runtests 159 functions reported verified).
Deferred:
- composing the legalisation with the mid-end theorems (`--opt` keeps legalised functions
  unverified);
- runs that trap inside a `__*ti3` helper (`i128` division by zero, `sdiv MIN, -1`): the
  backend theorem excludes extern traps (`TrapsExplicit` of the legalised run); covering them
  needs a trapping-helper contract on the Arm side (natively the helper aborts);
- a correct `umulhi`/`smulhi` expansion at `i128` (now unsupported), `try_call` with `i128`
  in the validator, `i128` overflow ops and atomics, stack-passed `i128` arguments.

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
  `ids`) are preconditions; a decidable `Pre` (for a runtime report that `check` cannot fail)
  is not implemented — the compiler keeps running `check`.

## `sret`: what `E2E.backend_correct_final` does not cover (2026-09-30)

Functions with a struct-return pointer and calls of `sret` callees are inside the end-to-end
theorem (`docs/contracts/e2e.md`, "`sret`"). Deferred:
- the conclusion claims the CLIF return values (none for an `sret` function) and the memory the
  function wrote through the pointer, not that x0 holds the pointer on return (the ABI's
  `sigRets`); callers compiled by cg_clif and the Lean backend do not read it;
- `vmctx`/`sarg` parameters (flagged unverified). (`sret` with 8 further parameters is
  covered since agent/stack-tls-proof: `InSubset.regParams` is gone.)

## Stack-passed arguments: what `E2E.backend_correct_final` does not cover (2026-10-01)

Stack-passed parameters and stack-passed arguments of `call` are inside the end-to-end theorem
(`docs/contracts/e2e.md`, "Stack-passed parameters and `call` arguments"). Deferred:
- stack-passed arguments of a `try_call` (`InSubset.tryRegArgs`, flagged unverified) and of
  `call_indirect`/`try_call_indirect` (`InSubset.indSigs`, at most 8 register parameters);
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
  - **The `i128` source program as a whole**: `backend_correct_program` relates the Arm run to
    the legalised program; relating that to the source program's whole-program run needs a
    program-level legalisation refinement (`Opt.Legal.check_refines` per function under a
    linked environment satisfying `ExtLegal`, by induction on the call depth; `NoMemTrap` of
    callee runs, `EnvKeepsAllocs` of the linked environment).
  - recursion through a pointer (the caller's own address); reachable indirect callees (whose
    signature matches an indirect call of the caller, `IndSigMatch`: parameter types and
    purposes, return types since agent/sret-purpose; agent/link-scope2 restricted `indSig` to
    those, agent/crate-check3 `blrRegs`/`blrTry` to `IndTo`) with stack-passed or `sret`
    parameters; a declared function entered through a pointer whose call-site signature has its
    parameter types but not its purposes (`indSig` still constrains it: since agent/scope-widen
    (#89 (c)) the per-function run's `callExternAt` checks the purposes against the linked
    environment's `sigOf`, but the non-interference contract's pinned indirect call (`CallLg`,
    `xni`) records only the parameter types, so `indSig`'s `DeclN`/`IndTyMatch` disjunct stays).
  - a function calling itself under its own name (excluded at the CLIF level by `InSubset (P.only f)`; `cargo fv`'s alias covers it), float parameters; a
    depth-free machine (monotonicity of `linkedCall` in the depth, needs base hooks preserving
    errors).
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
  `stepCallIndirect` resolves addresses among all functions and externs of `P`), `return_call`,
  and traps inside program callees.

## Completeness of the lowering validator `lowerCheck` (done, 2026-10-05)

Done on agent/lower-complete (TO-PROVE V1/V2): `lowerCheck_complete` on `Dominated`/`LowerScope`
input, `E2E.Compiled.of_lower` (see `docs/contracts/e2e.md`, "Validator completeness"). The
feasibility note's two code changes were made (V1a: `inFix` fuel-bounded; additionally
`lowerFunction`'s alias resolution keeps the referencing register's class, since otherwise
completeness would need a per-rule register-class property). The def-set property became
`stmt_flow`, decided over the rule data by an abstract interpretation (`IselFlowCheck`) rather
than per-rule lemmas. Remaining: the input conditions join `InScope` for the totality work
(TO-PROVE L1/L2); `lowerCheck` still runs as a double-check.

## Other deferred items

- **M3 validator** (Cranelift's own machine code vs CLIF, per function): paused on branch `agent/validator`. Only needed to ship Cranelift's bytes with assurance.
- **M3b** (Lean-optimised vs Cranelift-optimised CLIF comparison): optional, not started.
- **DSL `compile_correct` (M2):** paused on branch `agent/m2proof`.
- **Rust route extras:** data objects via a cg_clif fork, panic/`mem*` contracts, `dyn`. See `docs/research/rust-clif-survey.md`.
- **After M7 (PLAN.md):** SIMD, RISC-V, a verified frontend.
