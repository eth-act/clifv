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

## Completeness of `Opt.Legal.check` for `Opt.Legalize128` (in progress, 2026-10-02)

Goal (owner-approved): `function128Cert f = .ok (g, cert) → mentions128 f = true → LegalDomain f →
Opt.Legal.check f g cert = true`. With `check_refines` this gives `legalize_refines` and
`E2E.backend_correct_legal_direct` without the `hchk` premise. Not finished. The validator
stays the runtime check (`parsedFile128`).

**Exists:**
- Empirically complete. On the runtests and corpora (185 `i128` functions, 163 legalised, 22
  legaliser failures), `check` accepts all 163 legalised functions (throwaway driver over
  `function128Cert`/`check`).
- `FV/Opt/Proof/LegalComplete.lean` (layer 1). `pureOk_of` is the generic lemma for every
  `Plan.pure` case: a renamed well-formed pattern (`PatWF`, decidable per pattern) passes
  `pureOk` when the values it writes are distinct, none an input, each an output or fresh.
  Also the `@[simp]` run lemmas that evaluate the legaliser's `M` computations symbolically
  (`fresh_run`, `emit1_run`, `kI64_run`, …). One `simp only [un128, StateT.run_bind, …]` turns
  a case's emission into `st.out ++ pat.map (renameStmt τ)`.

**Plan (remaining, about 3-4k lines):**
1. *Allocation ledger.* Every `fresh` id is at least `maxValueId f + 1 = T0 + 1`, ids are
   allocated once, and pairs only grow (`phaseA1` before `rewriteM`, then `groupRet` for `i128`
   call results). So for the final certificate, the ids a statement allocates (`[st.next,
   st'.next)`) are fresh (`Ctx.fresh`): not the zero (allocated first in `rewriteM`), not a pair
   component (earlier ones are below `st.next`, later ones at or above `st'.next`). State it as
   a relation `Ledger T0 C st` derived from `Ev st stFinal`.
2. *`phaseA1` invariant.* A pair exists only for a value whose `tyOf f` is `i128`; components
   are in range, `a ≠ b`, and different values have disjoint pairs. Loop reasoning like
   `PrepareComplete.forIn_inv`, for `StateT St (Except String)`.
3. *Type map.* `typeMapOf f` (`HashMap`, last insert wins) agrees with `tyOf f` (`defsOf`, first
   definition) under distinct definitions.
4. *Statements.* One lemma per `rewriteStmt` case: evaluate the run with the layer-1 simp set and
   show `planOf C s = some pl`, `pl.len = seg.length` and `segOk C s pl seg`. The pure cases go
   through `pureOk_of`. `load`/`store`/`div`/`call`/`trap` are direct.
5. *Blocks.* The `rewriteM` block loop: `paramsOf`/`entryParamsOk`, `blockParamsOf`/`paramsOk`,
   the entry block's zero statement, `codeOk` from the per-statement segments (out =
   segments ++ terminator condition statements), `rewriteTerm`/`termOk` (`rewriteBC`/`bcOk`,
   `argsOf`/`expandArgs`, `rewriteTryDest`/`expandTry`).
6. *Assembly.* `certOk` from the ledger (`HashMap.toList` lookups, distinct keys); `g.externs =
   newExterns ++ extraExts` (helper refs are above `maxFnRef f`); `sigExp f.sig = some g.sig`.

**Mismatches found** (legaliser output `check` rejects; none occurs in the corpora). Each needs a
legaliser fix (a `throw`, no change on well-typed CLIF; rerun `clif-filetest --legalize128`) or a
`LegalDomain` precondition:
- `iconst.i128` is emitted unchanged, but `planOf` has no plan for it (fix: throw);
- an `i128` operand of a narrow `unary`, `icmp`, `iconcat` operand, or the address of an `i128`
  `store` is not rejected by the legaliser, but `same`/`copy2`/`store` need plain operands (fix:
  throw, as the other narrow cases do);
- an `i128` `load`/`store` with a big-endian flag or a non-plain opcode (`planOf` needs
  `.load`/`.store` and not big-endian) (fix: throw);
- `call_indirect` with an `i128` signature is expanded by the legaliser, but `planOf` only has
  `callInd` (the unchanged statement) (precondition: no `i128` `call_indirect` signature;
  throwing would make such functions unsupported instead of unverified);
- statements with a result count different from `Inst.resultTypes` (`head!` in the legaliser)
  (precondition: result arity);
- `func_addr` of an undeclared `FnRef` (the helper refs may reuse it) (precondition: declared
  refs).
The f-only conjuncts of `check` become preconditions too: distinct definitions (`defsOf`),
every id below `maxValueId f`, a statement never reads its own result (`pureOk` injectivity),
distinct call results, and for `try_call`, `maxValueId f ≤ f.freshValue`.

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
- **Callee contract with a dead stack.** `CalleeOk.os` compares the hooked callee's state with
  `X.call`'s world on all memory outside the caller's frame `F`, so it rejects any callee that
  writes state-dependent bytes below `sp` (`E2E.calleeOk_saves_lr_false`: the saved return
  address). Split the region of `OperandsSoundCtl` for calls: the world comparison ignores `F`
  and the dead stack `D = [sp_body − K, sp_body)` (`K` a stack budget), `FrameKeep` keeps only
  `F`; `Q`'s world relation becomes `SameWorld (F ∪ D)`; `MemRel`/`OutRel` additionally keep
  live CLIF bytes outside `D` (an entry premise and part of `XCallsOk`'s relation); the flags
  either masked across calls (AAPCS64 does not preserve NZCV) or produced by `X.call`. Touches
  `realizes_call`/`realizes_tryCall`, `realizes_op_core` and every lemma that unfolds `frameF`.
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

## Completeness of the lowering validator `lowerCheck` (feasibility, 2026-10-02)

`prepCheck` is now proven complete (`Prep.prepCheck_complete`, `docs/contracts/e2e.md`
"Validator completeness"), which makes `prepare` correct outright. The same for `lowerCheck`
(`lowerFunction f = .ok vc → lowerCheck f vc = true`) was assessed, not attempted. Verdict: keep
`lowerCheck` as a validator; a completeness proof is a project of its own (estimate 6-10k lines,
against 1.7k for `prepCheck`), and two of its parts need code changes first.

What `lowerCheck` checks, and what completeness would need for each part:

- **The re-run of the ISLE calls** (`lowBlocks` against `lowerFunction`'s per-block loop):
  a simulation of `lowerFunction`'s imperative loop (statement loop, terminator, `try_call`
  edge blocks, label counter) by the recursive `lowBlocks`. The calls are the same deterministic
  `runTerm` calls, so this is bookkeeping, about 1-1.5k lines in the style of
  `PrepareComplete.prepare_facts`.
- **The shape** (`shapeOk`): labels are block indices, parameters, branch arguments, edge
  blocks (direct from the loop invariant), and `vb.insts = pre ++ segments ++ tseg` after alias
  resolution. `lowerFunction` resolves aliases with a fuel-bounded array chase (`resolve`);
  the check with `gnTable`/`chase` over a `HashMap`. Showing both agree needs acyclic alias chains
  (an alias target is defined by the instruction defining the aliased value, which only reads
  earlier values) and enough fuel. That is a well-foundedness argument over the recorded results,
  about 0.5-1k lines.
- **The SSA availability certificate** (`certOk`, `inFix`). This is the main obstacle:
  1. `lowerFunction` does not check dominance, so completeness needs a precondition on `f`
     (every use dominated by its definition, Cranelift's verifier), stated in the form the
     certificate uses (`availOf`).
  2. `inFix` computes the must-availability fixpoint with a `while true` worklist loop
     (`Loop`, implemented by `partial`), and proofs cannot unfold it. It would first have to be
     rewritten with fuel (as `reachable`/`rpo` are) and proven to reach a fixpoint that
     contains the dominating definitions, for any CFG. That is a dataflow-completeness proof,
     about 1.5-2k lines.
  3. "No available value's register is written by a statement's lowering" (`certBlockOk`'s
     clobber and freshness conditions) is a property of the ISLE rules: every rule's emitted
     code defines only fresh vregs (at or above `nextVreg`) or the statement's result vregs.
     It needs a lemma per root rule over the ~1000 `lower` rules. M4's rule theorems
     (`LowerRulesCorrect`) state semantics, not this syntactic def-set property, so it could be
     discharged generically (an `emitted` def-set analysis decided over the rule data, like
     `excludedUnmatchable`) or rule family by rule family. About 2-4k lines, or a decided
     property over the exported rule data.
- **The remaining conjuncts** (`ctxOk`, `brIdxOk`, the `hasTryCall`/`hasTls` flags,
  `callsStackOkB`: `outgoing` is the maximum over the calls, `entryOkB`) follow from
  `buildCtx`'s own checks and the loop invariant. About 0.5k lines.

Suggested order, if picked up: (a) make `inFix` fuel-bounded (no behaviour change, check the
filetests and `lean-e2e-check` counts); (b) define the dominance precondition and prove the
dataflow complete; (c) decide the def-set property over the rule data; (d) the loop
simulation and alias chase. Steps (b) and (c) carry the risk.

## Other deferred items

- **M3 validator** (Cranelift's own machine code vs CLIF, per function): paused on branch `agent/validator`. Only needed to ship Cranelift's bytes with assurance.
- **M3b** (Lean-optimised vs Cranelift-optimised CLIF comparison): optional, not started.
- **DSL `compile_correct` (M2):** paused on branch `agent/m2proof`.
- **Rust route extras:** data objects via a cg_clif fork, panic/`mem*` contracts, `dyn`. See `docs/research/rust-clif-survey.md`.
- **After M7 (PLAN.md):** SIMD, RISC-V, a verified frontend.
