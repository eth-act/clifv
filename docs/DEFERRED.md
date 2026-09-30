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
- Allow-list: `Opt.provenSimplifyRules`, `RuleAll.simplifyRulesCorrect_proven`.
- Template tactics and the generated constructor lemmas.
- The exact proven set and the per-family recipe are in `docs/contracts/midend.md`, section "Rule proofs".

**Status (2026-09-30):** 668 `simplify` roots are proven and allow-listed: arithmetic 172 of 258, cprop 52 of 68 and bitops 444 of 450. The skeleton allow-list is empty. `E2E.backend_correct_opt_proven` covers exactly this set. With only these rules enabled, corpus instructions fall from 4668 to 2628 (all rules: 2287), and runtests from 3389 to 3128 (all rules: 3040). Bitops rules rarely fire in these corpora, so this batch changed the corpus count by only 2 instructions.

**Remaining:** prove the rest of the E-closure roots, one opts file per family. The remaining counts are arithmetic 86, cprop 16 (shift/rotate folds, if-let right-hand sides, bswap folds; midend.md lists them), and all roots of the families below:

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
| remat | 12 |
| skeleton (incl. div_const) | 37 |

**How to add a family:** follow the recipe in midend.md "Rule proofs":
1. Write a per-family file with `RuleOk` proofs over an abstract `p` with `Data p`.
2. Add the rule ids to `Opt.provenSimplifyRules`, and a case to `RuleAll.simplifyRulesCorrect_proven` (skeleton rules: `skeletonSound_proven`).
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

## Other deferred items

- **M3 validator** (Cranelift's own machine code vs CLIF, per function): paused on branch `agent/validator`. Only needed to ship Cranelift's bytes with assurance.
- **M3b** (Lean-optimised vs Cranelift-optimised CLIF comparison): optional, not started.
- **DSL `compile_correct` (M2):** paused on branch `agent/m2proof`.
- **Rust route extras:** data objects via a cg_clif fork, `sret`, panic/`mem*` contracts, `dyn`. See `docs/research/rust-clif-survey.md`.
- **After M7 (PLAN.md):** SIMD, RISC-V, a verified frontend.
