# Deferred work

Work that is deliberately postponed. Each item says what exists already, what remains and how to
pick it up.

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
- **`try_call` payload registers.** `CalleeTryOk` fixes the def registers of a `try_call`'s call
  beyond its results (x0/x1, the exception payload) to `X.call`'s world, but a callee that does
  not write them leaves the caller's (masked) values: unsatisfiable for such callees. Needs the
  allocated-code semantics to havoc those defs on the normal return while the checker keeps them
  for the handler edges (a per-edge transfer in `RegallocCheck` and its soundness proof).
- **Exact world of a call.** `X.call` is a function of the arguments and the world and must give
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

## Other deferred items

- **M3 validator** (Cranelift's own machine code vs CLIF, per function): paused on branch `agent/validator`. Only needed to ship Cranelift's bytes with assurance.
- **M3b** (Lean-optimised vs Cranelift-optimised CLIF comparison): optional, not started.
- **DSL `compile_correct` (M2):** paused on branch `agent/m2proof`.
- **Rust route extras:** data objects via a cg_clif fork, panic/`mem*` contracts, `dyn`. See `docs/research/rust-clif-survey.md`.
- **After M7 (PLAN.md):** SIMD, RISC-V, a verified frontend.
