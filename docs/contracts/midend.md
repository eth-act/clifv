# Lean mid-end (`FV/Opt`), M7

<!-- The mid-end pass owns this contract; the section below is the rule-data interface it
consumes. Details: `docs/contracts/isle.md`, "Mid-end export". -->
`Opt.optimize : Clif.Function → Clif.Function` (and `Opt.optimizeProgram`) is the FV
compiler's CLIF → CLIF optimiser (PLAN.md §4 M7, "Lean mid-end"). It runs Cranelift 0.136.1's
own `simplify` / `simplify_skeleton` rules (exported as data, `docs/contracts/isle.md` "Mid-end
export") inside a small, separately provable pipeline of passes. Correctness criterion:
`Clif.run` refinement — whenever the input returns (values) or traps (code), the output does
the same; stuck or out-of-fuel input runs carry no obligation.

## Status

- [x] Passes (`FV/Opt/*.lean`): well-formedness check, unreachable-block removal, rule-based
  simplification of pure nodes and of skeleton instructions (Cranelift's rules via the ISLE
  interpreter), GVN, DCE, LICM. Written first and proven afterwards ("Pass proofs"); no `sorry`,
  no hand-written axioms.
- [x] Drivers: `clif-opt` (optimised CLIF out; accepted by `clif-oracle check`), `--opt` for
  `lean-backend`, `lean-backend-armrun`, `lean-e2e-check`, `scripts/lean-backend-filetests.sh`.
- [x] Differential tests: `scripts/opt-difftest.sh` (corpus, runtests, cg_clif survey),
  `opt-fuzz` (random functions); backend with `--opt`: corpus 114/114 (+22/22 extrt), runtests
  3270/0/0, `lean-e2e-check --opt` 934/934 accepted and `formsCoveredB`-covered.
- [x] Metrics (`scripts/lean-backend-metrics.sh`): Lean no-opt / `--opt` vs Cranelift
  `opt_level=none` / `speed` ("Results").
- [x] Proofs: every pass ("Pass proofs"), the rule interpreter and 1154 `simplify` + 37
  `simplify_skeleton` roots ("Rule proofs"; the false shifts 84/88 stay disabled):
  `Opt.optimize_sim_proven`, `E2E.backend_correct_opt_proven` (`ruleAllow := .proven`).
- [x] `call_indirect`, `try_call`, `try_call_indirect` (S1, #25): the executable compiler's
  mid-end `Opt.optimizeExe` (`optimize` with two guards) refines every program, indirect and
  `try` calls included (`Opt.optimizeProgramExe_refines`, `E2E.backend_correct_opt_exe`); the
  `i128` legalisation composed with it (S2, #26: `E2E.backend_correct_legal_opt`); the
  optimising executable compiler `Link.{DeadCleanup.}compileExeOpt` (`lean-link --opt`,
  `cargo fv --lean-link --opt-proven-only`). See "The executable compiler's mid-end".

## Using it

```sh
lake build clif-opt opt-difftest opt-fuzz
.lake/build/bin/clif-opt [--stats] [OPTIONS] IN.clif [OUT.clif]   # optimised CLIF (stdout default)
.lake/build/bin/opt-difftest [-v] [--rules-stats] [OPTIONS] FILE.clif...
.lake/build/bin/opt-fuzz [--seed N] [--count N] [--ext] [--out FILE.clif] [-v] [OPTIONS]
scripts/opt-difftest.sh [-v] [OPTIONS] [--corpus] [--runtests] [--survey] [FILE.clif...]
.lake/build/bin/lean-backend IN.clif OUT.o --opt [OPTIONS] ...     # also lean-backend-armrun, lean-e2e-check
scripts/lean-backend-filetests.sh --opt [OPTIONS] [--corpus | --runtests | FILE.clif...]
scripts/lean-backend-metrics.sh [FILE.clif...]                     # METRICS_OPT="OPTIONS" for --opt
```

`OPTIONS` (`FVTest/Opt/Common.lean`, any of them implies `--opt`): `--opt-rules cranelift|hand`
(default `cranelift`), `--opt-no-simplify`, `--opt-no-gvn`, `--opt-no-dce`, `--opt-no-licm`,
`--opt-remat-const`, `--opt-no-hoist-const`, `--opt-rounds N` (default 1).

## Design

The input/output is `Clif.Function`; every pass is a function `Function → Function` (plus
statistics) with its own invariant, so that each can get its own simulation proof. There is no
separate IR: a *pure node* is a `Clif.Inst` (`Opt.isPure`: `iconst`, `unary`, `binary`, `icmp`,
`select`, `bitselect`, `bmask`, `extend`, `ireduce`, `iconcat`, `bitcast`, `stack_addr`,
`symbol_value`), whose operands are value numbers. Everything else is the *skeleton*
(side effects, traps, memory, calls, multi-result arithmetic, `select_spectre_guard`): it is
never moved or duplicated, only rewritten in place by skeleton rules or deleted by DCE when it
is `Opt.removable` (non-trapping, memory-free) and dead.

Pipeline (`FV/Opt/Optimize.lean`):

```
removeUnreachable ; check ;
(simplify ; removeUnreachable ; check ; gvn ; check ; dce) × rounds ;   -- rounds = 1
licm ; check ; gvn ; check ; dce
```

`check` is re-run after every pass. If the input fails it, the function is returned with only
unreachable blocks removed (`Report.illFormed`); if a pass's output fails it (a bug), the
pipeline stops and returns the last well-formed function (`Report.passError`, reported by the
difftests, never observed).

**Backend subset.** If the input is in the backend subset E (`Compile.functionE`), the
simplifier may only emit pure nodes and skeleton instructions in E (`Opt.allowedIn`,
`Opt.skelAllowedIn`; others get infinite cost). So `--opt` never takes a function out of the
Lean backend's reach. (Rewrites can build `bmask`, `iabs`, `iconcat`, `trapz`, `trapnz` —
`Isle.Opt.Closure.introducedOpcodes`.)

### Modules

| Module | Contents |
| --- | --- |
| `Basic` | operands/renaming of instructions and terminators, `isPure`, `removable`, `Subst` (value renaming, `find`, `apply`), `maxValue` |
| `Cfg` | CFG by layout index, RPO, Cooper–Harvey–Kennedy dominators, `dominates`, dominator-tree preorder, natural loops, `removeUnreachable` |
| `Check` | `Opt.check : Function → Except String Info` (well-formedness, below); `Info` = CFG, types, defining blocks, pure defs |
| `Cost` | Cranelift's cost model |
| `Rules` | the rule-set interface (`SimplifyFn`, `SkeletonFn`, `RuleSetId`) |
| `HandRules` | a small hand-written rule set with the same interface (driver tests, `--opt-rules hand`) |
| `Simplify` | the rewriting pass (acyclic e-graph with hash-consing, extraction, materialisation, skeleton rules) |
| `Gvn`, `Dce`, `Licm` | the other passes |
| `Optimize` | `Config`, `optimizeReport`, `optimize`, `optimizeProgram` |

## Pass invariants (for the proofs)

Notation: `f` input, `f'` output; "σ" a value renaming `v ↦ w` produced by a pass and applied
to every later use (`Subst.apply`).

**`check` (precondition of every pass).** `Opt.check f` succeeds iff every block is reachable,
block ids are unique, every value is defined once, every use is dominated by its definition
(same block: earlier; other block: the defining block strictly dominates; block arguments are
uses at the end of the branching block), result arities match `Inst.resultTypes`, branch
arguments match the target's parameters, the entry parameters match the signature, and every
pure node's operands have the types `Clif.evalInst` requires (`pureTyped`). Consequences used
below: (T) a pure node never evaluates to `stuck` (except `symbol_value` of a symbol missing
from the link-time image); (D) *dominance lemma*: if the definition of `x` dominates a point
`P` and `P` dominates a point `Q`, then on every execution, between the last execution of
`x`'s definition before a visit of `Q` and that visit, `P` is executed — so a value computed at
`P` from `x` equals the same computation at `Q`.

**`removeUnreachable`.** Deletes blocks unreachable from the entry. `Clif.run` looks blocks up
only when branching to them, so runs are identical step for step.

**`simplify`** (`FV/Opt/Simplify.lean`). Blocks in RPO, statements in order. For a pure
statement `v = n` (operands renamed by σ so far): hash-cons `n` (a previously seen equal node
gives its value — Cranelift's GVN map); otherwise run the rules on `v`, build `v`'s e-class
(≤ 5 candidates, sorted, deduplicated; a `subsume`d candidate wins outright), extract the best
member by `(cost, value number)`, and if it is not `v`, *materialise* it right before `v`'s
position (emit the virtual nodes of its tree in dependency order, cloning a value whose earlier
emission does not dominate this block) and add `v ↦ best` to σ. Skeleton statements and
terminators go through the skeleton rules (`chooseSkel`, Cranelift's `simplify_skeleton_inst`
choice) and are replaced by the chosen form (with made nodes materialised before it), up to 5
re-simplifications.
Invariant: (S1) every emitted statement is a pure node whose operands are defined at its
position (dominance); (S2) for every `v ↦ w` in σ, `w` evaluates to the value of `v` in every
state reaching `v`'s position — by the rule-set obligation (`Opt.SimplifyFn`) applied to the
e-graph valuation, and by (D) for hash-consing hits; (S3) every skeleton replacement is
equivalent to the original instruction (same results, same trap, same successor with the same
arguments; `Opt.SkeletonFn` obligation); (S4) removed CFG edges only strengthen dominance, so
the dominator tree computed before the pass stays sound for placement decisions.
The e-graph state (`SState`) satisfies a *graph consistency* invariant: there is a valuation ρ
of all e-class ids such that every node `n` of every class `x` evaluates to `ρ x` under ρ; `make`
extends ρ (pure nodes are total by (T)), and rules only return classes with `ρ w = ρ v`.

**`gvn`** (`FV/Opt/Gvn.lean`). Dominator-tree preorder with a scoped table `node ↦ value`; a
pure statement whose renamed node is in scope as `w` is deleted and `v ↦ w` added. Invariant:
`w`'s statement is the same pure node over the same (renamed) operands and strictly dominates
`v`'s; by (D) and (T) `w` holds `v`'s value at every use of `v`, and the deleted statement
could not trap. (With `rematConst`, `iconst` is numbered per block only.)

**`dce`** (`FV/Opt/Dce.lean`). Mark from the operands of non-removable statements and
terminators through the definitions of live values; delete removable statements with no live
result. Invariant: deleted statements are `removable` (no trap, no memory) and none of their
results is read by the output, so only dead register entries differ.

**`licm`** (`FV/Opt/Licm.lean`). For each natural loop (innermost first, to a fixpoint), move
the pure statements of loop blocks whose operands are all defined outside the loop (or by
already hoisted statements) to the end of `idom(header)`, in RPO/statement order.
`symbol_value` is never hoisted (a missing symbol would make a run that did not execute it
`stuck`); `iconst` is hoisted unless `--opt-no-hoist-const`. Invariant: a moved statement is
pure and well-typed (T); its new position dominates the old one; each operand's definition
dominates the new position (an operand defined outside the loop dominates the header strictly,
hence `idom(header)`); by (D) every use reads the same value. Executions that pass the new
position without reaching the loop only gain a dead register entry.

## Cost model (extraction)

As Cranelift's `egraph/cost.rs` + `elaborate.rs::compute_best_values` (`FV/Opt/Cost.lean`):

- block parameters and skeleton results cost 0; a pure node costs its opcode cost plus the
  costs of its operands (a tree cost; shared operands counted per use), saturating below
  `Cost.infinite` = 2³²−1;
- opcode costs: `iconst` 1; `uextend sextend ireduce iconcat isplit` 1;
  `iadd isub band bor bxor bnot ishl ushr sshr` 3; `imul` 10; every other pure node 4;
- an e-class's representative is its member of least `(cost, value number)` (ties go to the
  older value, as in Cranelift);
- skeleton replacements (`Replace*`) must have lower `Cost::of_skeleton_op` (opcode cost, +10
  if it can trap, + operand count) than the original; `Remove*`, `ReplaceBranchCond`,
  `ReplaceWithTwo` are taken at once (Cranelift's order: last candidate first);
- deviation: nodes outside `allowed` (outside E for an E function) get `Cost.infinite` and are
  never materialised; a `subsume`d candidate is only taken if its cost is finite.

Limits as Cranelift: rewrite depth 5 (`REWRITE_LIMIT`), 5 candidates (`MATCHES_LIMIT`), 5
e-nodes per class (`ECLASS_ENODE_LIMIT`).

Differences from Cranelift's e-graph pass (all conservative for correctness, some cost code
quality): values are materialised where they were (no sinking into uses; LICM and constant
remat are separate); an e-class's alternative nodes are visible to later matches only through
a representative created by the same statement; candidate order is ISLE rule order, not
Cranelift's trie order, and there is no `MAX_ISLE_RETURNS` = 8 cap before truncation to 5;
no alias analysis (redundant loads, store-to-load forwarding) and no merging of identical
trapping instructions (`is_mergeable_for_egraph`).

## ISLE rule data and `simplify` (`FV/Isle/Opt`, `FV/Isle/Generated/Opt`)

Cranelift 0.136.1's mid-end ISLE unit (`opt`: 1605 rules, 1281 of them `simplify`, 39
`simplify_skeleton`) is exported by `rust/crates/isle2lean` as `Isle.Opt.program`. The
mid-end calls the rules through two entry points in `FV.Isle.Opt.Simplify`, which depends only
on `FV.Clif.Syntax`, the interpreter and the generated data:

```lean
def Isle.Opt.simplify {σ} (enodes : σ → Nat → List Clif.Inst) (typeOf : σ → Nat → Option Clif.Ty)
    (make : σ → Clif.Inst → Nat × σ) (st : σ) (v : Nat) :
    Except String (List (Nat × Bool) × List String × σ)
def Isle.Opt.simplifySkeleton {σ} (enodes …) (typeOf …) (make …)
    (trapBlock : σ → Clif.BlockId → Option Clif.TrapCode) (st : σ) (i : SkelInst) :
    Except String (List SkelSimp × List String × σ)
```

- `enodes st v`: the pure single-result nodes of e-class `v` (operands are e-class ids), in
  the order Cranelift's `InstDataEtorIter` would yield them; `typeOf st v`: its type;
  `make st inst`: insert a pure node (Cranelift `make_inst` → `insert_pure_enode`, which
  simplifies the new node recursively) and return its e-class. `trapBlock`: Cranelift's
  `just_trap_block`.
- Result of `simplify`: every candidate in rule order with whether the rule `subsume`d it
  during this call, and the producing rule's name (parallel lists). Candidates may repeat and
  may be `v` itself (the `remat` rules). Cranelift's driver (`egraph/mod.rs`
  `optimize_pure_enode`) shuffles, truncates to `MATCHES_LIMIT`, sorts and dedups, skips `v`,
  and if a candidate was subsumed keeps only it. Cranelift's generated code also stops after 8
  results (`MAX_ISLE_RETURNS`) in its own order; `simplify` returns all of them.
- `SkelInst` is `.inst Clif.Inst` (`div`, `trapz`, `trapnz`) or `.term Clif.Terminator`
  (`brif`, `br_table`, `jump`); `SkelSimp` is Cranelift's `SkeletonInstSimplification`
  (`remove`, `removeWithVal`, `replace`, `replaceWithVal`, `replaceBranchCond`,
  `replaceWithTwo`).
- Nodes and rewrites outside `Clif.Inst` (float or vector types, `i128` `iconst`, other
  opcodes) are never passed to `make`; the candidates built from them are dropped.
- `.error` means an interpreter error: an unmodeled extern helper, a Rust panic of a helper,
  or fuel. It is never "no rewrite".
- `Isle.Opt.Closure` lists the rules that can fire on E programs at `i8`..`i64` (1357 rules,
  1193 of them roots), the opcodes outside E that rewrites can build (`bmask`, `iabs`,
  `iconcat`, `trapz`, `trapnz`), and the rules that build them.
- Checked against Cranelift (`FVTest/Isle/Opt.lean`, `OptCorpus.lean`): 20 hand-written
  `simplify` calls, 12 `simplify_skeleton` calls and 930 `simplify` calls over the CLIF corpus
  fire the same rules as a `trace-log` build at `opt_level=speed` (per call, on e-classes whose
  operands are single original nodes).
  1154 `simplify` roots, all 37 `simplify_skeleton` roots and their helpers are proven (see "Rule
  proofs").

## Results (2026-09-28, default configuration: Cranelift rules, 1 round)

**Differential tests** (`scripts/opt-difftest.sh`, `opt-fuzz`). "noclaim": the source run is
stuck (the corpus `extrt` functions call runtime externs that `Clif.run`'s empty `Env` lacks;
some runtests are stuck by design), so there is no obligation; in every such run the optimised
program was stuck too.

| Set | functions | `Clif.run` runs: agree / fail / noclaim | static insts before → after | `clif-oracle check` |
| --- | ---: | --- | --- | --- |
| corpus (`corpus/clif`, `extrt`) | 174 | 114 / 0 / 22 | 4 668 → 2 287 | 50 files, 0 rejected |
| Cranelift runtests | 1 258 | 5 706 / 0 / 10 | 3 383 → 3 040 | 146 files, 0 rejected |
| cg_clif survey smoke (`smoke.clif`) | 24 | 88 / 0 / 0 | 283 → 144 | ok |
| cg_clif survey, all `*.unopt.reader.clif` (no run lines) | 2 326 | — | 116 713 → 67 251 | 30 files, 0 rejected |
| `opt-fuzz` seeds 1–4 (150 E + 100 `--ext` functions each) | 1 000 | 8 000 / 0 / 0 | 128 484 → 57 279 | — |
| `opt-fuzz` seeds 11, 12, 21, 22 (earlier builds; incl. `--opt-remat-const`) | 1 050 | 8 352 / 0 / 0 | — | seeds 21, 22 files: ok |

No function was ill-formed and no pass ever produced an ill-formed function. The optimised
corpus and runtests files also meet their run lines under the Cranelift interpreter wherever
the originals do (one file improves: `div-checks` agrees more often after constant folding
avoids a known interpreter deviation).

**Backend with `--opt`** (`scripts/lean-backend-filetests.sh --opt`, native under qemu vs
Cranelift-native): corpus 114/114, extrt 22/22, runtests **3 270** pass / 0 fail / 0 disagree
(3 085 without `--opt`: rewrites turn 17 functions with `i128` shift amounts —
`iconcat`/`ireduce` of the amount — into E functions); `opt-fuzz --seed 21` file: 1 166/1 166.
`lean-e2e-check --opt`: `lowerCheck` and `prepCheck` accept 934/934, `formsCoveredB` 934
covered / 0 not covered (913 of each without `--opt`) — the optimised code uses no instruction
form outside the proven set.

**Metrics** (`scripts/lean-backend-metrics.sh`, corpus: code size of 156 functions; executed
instructions on the Lean Arm model over the run lines of the 25 self-contained functions):

| | Lean stack | Lean regalloc2 | Lean regalloc2 + `--opt` | Cranelift `none` | Cranelift `speed` |
| --- | ---: | ---: | ---: | ---: | ---: |
| code size (bytes) | 171 628 | 51 648 | **27 096** | 30 424 | 19 664 |
| executed instructions | 17 930 | 5 887 | **4 392** | 3 032 | 2 716 |

`--opt` shrinks the Lean backend's code to 0.52× and its executed instructions to 0.75×
(Cranelift's own mid-end: 0.65× and 0.90×). Relative to Cranelift at the same optimisation
level the Lean pipeline goes from 1.70× / 1.94× (`none`) to 1.38× / 1.62× (`speed`). The largest
gains are `chacha20Block` (24 656 → 2 064 bytes; Cranelift `speed` 1 796: constant branches of
the unrolled rounds folded by the skeleton rules, then constant propagation), `signedMix`
(0.38× executed) and `bumpCopy` (0.46× size). Regressions: `findIdx` +19% size (hoisted
constants across a 9-parameter function; −11% executed), `sumSquares` +9%, `meanSquare` +6%,
`sumChecked` +4% size, `sub3` +4% executed (a constant reused across blocks).

Ablations (code size / executed instructions; full pipeline 27 096 / 4 392):

| Configuration | size | executed |
| --- | ---: | ---: |
| `--opt-no-simplify` (GVN, DCE, LICM only) | 48 792 | 5 027 |
| `--opt-rules hand` (the stand-in rule set) | 40 708 | 4 812 |
| `--opt-no-gvn` (hash-consing in `simplify` remains) | 27 180 | 4 394 |
| `--opt-no-licm` | 26 892 | 4 719 |
| `--opt-no-hoist-const` | 26 912 | 4 719 |
| `--opt-remat-const` | 27 188 | 4 366 |
| `--opt-remat-const --opt-no-hoist-const` | 27 536 | 5 089 |
| `--opt-rounds 2` | 27 096 | 4 392 |

LICM pays off only through constants: this backend lowers every `iconst` (even one isel folds
into an immediate), so hoisting them out of loops removes executed `mov`s.

Speed: `clif-opt` takes 0.6 s on `chacha20Block` and 26 s on the 1 088 functions of the
survey's `core` (the ISLE interpreter dominates).


## Planned proof architecture

Goal: `Opt.optimize` refines `Clif.run`, and `E2E.backend_correct_final` extends over it:
`Arm.run (emit (regalloc (isel (opt p)))) ≈ Clif.run p`.

1. **Semantics of nodes.** `Opt.evalNode ρ n` := the single result of `Clif.evalInst` on a
   frame whose registers are ρ (as `HandRules.fold` already does). Lemma (T): on `check`ed
   functions, `evalNode` of a pure node is `ok` whenever its operands are defined, and it does
   not depend on memory or on anything else in the frame (`stack_addr`/`symbol_value`: only on
   the frame's slot bases / the image's symbols, which no pass changes).
2. **Per-rule `simplify` correctness vs `Clif.Sem`** (PLAN: "prove each one before enabling
   it"). For each rule of the E closure (`Isle.Opt.Closure`, 1357 rules), the statement is:
   for all bindings satisfying the LHS pattern and if-lets, the RHS denotes the same value as
   the LHS, per type `i8`..`i64`; the proofs split on the type and close with `kbv`
   (kernel-checked bit-vector decision, `FV/Opt/Proof/KernelBV.lean`; until T6 `bv_decide`, like
   the isel proofs, `docs/contracts/backend-proof.md`), with the Lean transcriptions of the
   extern helpers (`FV/Isle/Opt/Helpers.lean`) specified by lemmas first. Then an
   *interpreter soundness* lemma for `Isle.Interp.runMultiTerm` (a returned value comes from a
   rule whose LHS matched with some bindings and whose RHS evaluated to it) lifts the per-rule
   lemmas to `Isle.Opt.simplify`: under a graph valuation ρ consistent with `enodes`/`make`,
   every candidate `w` has `ρ w = ρ v`. The same for `simplify_skeleton` with the skeleton
   equivalence (S3). Rules not yet proven can be disabled by a per-rule allow-list in the
   embedding (the `Isle.Opt.simplify` result carries rule names), so the proven subset can grow.
3. **Pass-level simulations.** One forward simulation per pass, for `check`ed inputs, on
   `Clif.step` states (frame stacks, since callees in the program are optimised too): frames
   are related when they are at corresponding statements of the same block (a statement map
   per block) and the target registers agree with the source registers through σ on the values
   *available* at that point; memory, slots and caller frames are equal. Deleted statements are
   source-only steps (a stuttering measure: remaining statements of the block), inserted ones
   (materialised or hoisted nodes) target-only steps; skeleton statements and terminators are
   lock-step. The pass invariants above are exactly the per-step obligations; (D) is proven
   once from the path characterisation of dominance. Refinement then reads: source `returned
   vs m` / `trapped c` within `fuel` ⇒ target the same within some `fuel'`.
   To avoid proving the dominator algorithm, `check` can additionally validate the computed
   tree with a local certificate: for every edge `u → b`, `idom b` is a tree ancestor of `u`;
   this implies that every tree ancestor of a block dominates it, which is the only direction
   used.
4. **Pipeline.** `optimizeReport` composes the passes with a `check` after each and falls back
   to the last checked function, so the pipeline theorem is the composition of the per-pass
   refinements (refinement is transitive; each pass is only needed on `check`ed input).
5. **Extending `backend_correct`.** `E2E.backend_correct_final` holds for the compiled
   `opt f` against `Clif.runLoop … (opt p)` for every fuel. Compose with step 4 at the entry
   state: `optimize` keeps the signature, the stack slots and the externs, so `ClifEntry`,
   `Rel.holds` and the slot layout of the source entry state carry over; `InSubset (opt f)`
   follows from `InSubset f` because of the E restriction on emitted nodes; `FormsCovered`
   stays a per-function decided premise (`formsCoveredB` of the optimised code, 934/934 now).
   The result: for `check`ed in-subset `f`, whenever `Clif.run p` returns or traps, the Arm run
   of the compiled `opt f` does the same.
6. **Optional M3b** (PLAN): with the same rules, the Lean- and Cranelift-optimised CLIF can be
   compared function by function; not attempted.

## Gaps

- Proven: the pipeline refines (every pass, see "Pass proofs"), end to end for the proven
  rule sets (`E2E.backend_correct_opt_proven`); only the allow-listed rules are proven, so the
  default configuration (all rules) still rests on the differential tests for the rule
  obligations (`SimplifySound`/`SkeletonSound` of the full rule set).
- Proven: the rule interpreter's soundness, 1154 `simplify` roots and all 37 `simplify_skeleton`
  roots ("Rule proofs").
- Missing Cranelift mid-end features: alias analysis (redundant-load elimination,
  store-to-load forwarding), merging of identical trapping instructions, elaboration-based
  sinking and general rematerialisation (only constants, optionally), full e-class visibility
  for later matches (see "Cost model").
- Rule candidate order differs from Cranelift's (ISLE rule order, no 8-result cap); when more
  than 5 rules fire, the kept candidates can differ.
- Constant placement is tuned for this backend, which lowers every `iconst` even when isel
  folds it into an immediate: constants are GVN'd across blocks and hoisted out of loops. This
  raises register pressure in some functions (`findIdx` code size +19%).
- `symbol_value` is not hoisted; `select_spectre_guard` is treated as skeleton.
- `opt-fuzz` generates E arithmetic, `select`, extends, divisions, diamonds and one loop shape;
  no memory, calls or `br_table`.

## Pass proofs (2026-09-28, MidPassProofs)

Proven (no `sorry`, no hand-written axioms; `#print axioms` = `propext`, `Classical.choice`,
`Quot.sound`; since T6 no `bv_decide` certificate, neither in the rule proofs nor inherited from
`backend_correct_final`):

| Theorem | File | Statement |
| --- | --- | --- |
| `Opt.runLoop_refines` | `FV/Opt/Proof/SemSim.lean` | pointwise `FunSim` between the functions of two programs ⇒ related states' runs: source returns/traps within `n` ⇒ target the same within some `n'` (calls, returns, tail calls, externs) |
| `Opt.FunSim.trans` | same | simulations compose |
| `Opt.wf_of_check` | `FV/Opt/Proof/Dom.lean` | `check` ⇒ the certificate facts `Wf` |
| `Inv.results/enter/entry` | `FV/Opt/Proof/DomInv.lean` | run-time invariant (dominance lemma (D)): available values hold typed values; pure definitions hold `evalNode` of their node |
| `evalInst_total` | `FV/Opt/Proof/SemFacts.lean` | lemma (T) |
| `Opt.removeUnreachable_sim` | `FV/Opt/Proof/Unreachable.lean` | `FunSim f (removeUnreachable f)` for every `f` |
| `Opt.editOk_sim` | `FV/Opt/Proof/GvnEdit.lean` | `check f`, `check g`, `editOk σ f g` ⇒ `FunSim f g` (GVN, DCE, LICM) |
| `Opt.optimize_sim`, `Opt.optimizeProgram_refines` | `FV/Opt/Proof/Pipeline.lean` | `FunSim f (optimize f cfg)` for every `f`; `Clif.run p` returns/traps ⇒ `Clif.run (optimizeProgram p)` the same |
| `E2E.backend_correct_opt` | `FV/E2E/Opt.lean` | Arm run of the compiled `optimize f` refines `Clif.runLoop env p fuel cs` from `f`'s entry state |
| `Opt.simpOk_sim` | `FV/Opt/Proof/SimpSim.lean` | `check f`, `simpOk f g fi cert` and the run's facts `SimpFacts f fi cert` ⇒ `FunSim f g` |
| `Opt.simplify_facts` | `FV/Opt/Proof/SimpLoop.lean` | `SimplifySound rules`, `SkeletonSound skel`, `check f` ⇒ every run of `simplify` has its facts |
| `Opt.simplifyPassSim`, `Opt.simplifyPassSim_proven`, `Opt.optimize_sim_proven` | `FV/Opt/Proof/SimpPass.lean` | `SimplifyPassSim` for sound rule sets; for `rules := .cranelift`, `ruleAllow := .proven`; hence `FunSim f (optimize f cfg)` unconditionally |
| `E2E.backend_correct_opt_proven` | `FV/E2E/OptProven.lean` | `backend_correct_opt` for `rules := .cranelift`, `ruleAllow := .proven` (every other option arbitrary), **without** a simplify hypothesis |

The pipeline theorems of `Pipeline.lean` and `E2E.backend_correct_opt` are stated for any
configuration given `Opt.SimplifyPassSim cfg.simplifyFn cfg.skeletonFn`; that hypothesis is
proven for sound rule sets (`Opt.simplifyPassSim`) and hence for the proven rule sets
(`simplifyPassSim_proven`), which gives `optimize_sim_proven` and
`E2E.backend_correct_opt_proven`. `#print axioms E2E.backend_correct_opt_proven` is exactly
the axiom set of `backend_correct_opt` (`propext`, `Classical.choice`, `Quot.sound`; T6); `simpOk_sim`, `simplify_facts`, `simplifyPassSim`,
`optimize_sim_proven`: `propext`, `Classical.choice`, `Quot.sound`.

### The executable compiler's mid-end (S1, #25: `call_indirect`, `try_call`)

`Opt.optimizeExe` (`FV/Opt/OptimizeX.lean`) is `optimize` with two guards, under which it refines
every program, indirect calls and `try_call`/`try_call_indirect` included
(`Opt.optimizeProgramExe_refines`, `FV/Opt/Proof/PipelineX.lean`; simulations `IsSimX`/`FunSimX`
in `FV/Opt/Proof/{SemSimX,SimWin,UnreachableX,GvnEditX,SimpSimX}.lean`). `lean-backend --opt`,
`clif-opt`, `opt-difftest` and `lean-e2e-check --opt` run it (`Opt.optimizeParsedFile`).

- **Fresh-value guard `freshOkB`.** A `try_call` binds its results at the function's fresh
  value (`Clif.Function.freshValue`, one above every *defined* value). `removeUnreachable` drops
  blocks, which can lower the fresh value; a reachable block that reads a value it never defines
  (ill-formed CLIF, rejected by Cranelift's verifier but given a meaning by `Clif.run`) then
  reads a different register. **`Opt.optimize` alone is unsound there**:
  `Opt.PipelineXWitness.optimize_not_refines` (`FV/Opt/Proof/PipelineXWitness.lean`): `%bad`
  (`try_call fn0(v0), sig0, block1, …`, `block1: return v2`, the unreachable `block2` defining
  `v1`) returns `8` on `5`, and no run of `Opt.optimizeProgram`'s program returns (it is stuck:
  the result lands in `v1`). `freshOkB` keeps such a function unchanged; on well-formed functions
  (`Opt.check`) it always holds (`freshOkB_of_check`). **Effect on earlier claims: none.**
  `Opt.optimizeProgram_refines` assumes `NoCallIndirect` (no `call_indirect`, no `try` terminator)
  and `E2E.backend_correct_opt_proven{,_cleanup}` assume `hci`/`hnt`, and `lean-backend
  --opt-proven-only` reported every `try_call`/`call_indirect` function unverified, so no earlier
  theorem or verified report covered such a function.
- **Shape guard `keepsShapeB`.** The result keeps the input's `try_call` callees and indirect-call
  signatures, and a `return_call`/indirect call/block if the input has one (what the backend's
  subset and the linking facts read); otherwise the input is returned.
- `Opt.check` rejects `call_indirect`, so such functions only get unreachable-block removal
  (DEFERRED, mid-end).
- **Measured** (`Opt.optimizeExe` with the proven rule sets on the decoded `cargo fv` dumps):
  fv-demo 1337 of 1352 functions changed, survey 3151 of 3179; `freshOkB` and `keepsShapeB`
  never reject (0 and 0 on both), and no optimised function falls back on the print/parse round
  trip (0 on both).

Theorems: `Opt.runLoop_refinesX`, `Opt.optimizeExe_simX`, `Opt.optimizeProgramExe_refines`
(witness `Opt.PipelineXWitness.optimizeProgramExe_witness`: a program with `call_indirect`,
`try_call` and `try_call_indirect`, all three functions changed, the run of `%main 5` returns `29`
before and after); `E2E.backend_correct_opt_exe{,_cleanup}` (`FV/E2E/OptX.lean`: no `hci`/`hnt`);
S2 (#26): `E2E.backend_correct_legal_opt{,_env}{,_cleanup}` (`FV/E2E/LegalOptX.lean`); the
optimising executable compiler `Link.{DeadCleanup.}compileExeOpt_*` (docs/contracts/e2e.md, "The
optimising executable compiler"). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

### Completeness of the validators (M1, #24)

The pipeline's checks (`check` after every stage, `unreachableOk` inside `removeUnreachable`,
`simpOk`, `editOk`, the final `keepsBackendSubset`; in `optimizeExe` also `freshOkB` and
`keepsShapeB`) all fall back safely, so they are not certificates. M1 proves that they never make
the optimiser skip a pass on well-formed input.

**Measured** (2026-10-18; a copy of `optimizeReport` that records every fallback point, run on
the decoded `cargo fv` dumps of fv-demo and the survey with the executable configuration
`exeConfig`, and on the corpus and runtests with both `exeConfig` and the default configuration):

| set | functions | `unreachableOk` rejects (input / after simplify) | ill-formed input (`check`) | stage `check` / validator rejects | `keepsBackendSubset` | `freshOkB` | `keepsShapeB` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| fv-demo | 1346 | 0 / 0 | 26 | 0 / 0 | 0 | 0 | 0 |
| survey | 851 | 0 / 0 | 4 | 0 / 0 | 0 | 0 | 0 |
| corpus | 174 | 0 / 0 | 0 | 0 / 0 | 0 | 0 | 0 |
| runtests (parsed) | 1507 | 0 / 0 | 4 | 0 / 0 | 0 | 0 | 0 |

The only rejections are of the input: on the crates every one is a `call_indirect` (`check` types
its results without the signature table; DEFERRED, mid-end), in the runtests four `bitcast`s
between integers and floats (`pureTyped`). These are genuine input restrictions: such functions get
only unreachable-block removal.

Proven so far (`FV/Opt/Proof/CompleteUnreachable.lean`, `CheckSpec.lean`, `CompleteDce.lean`,
`CheckComplete.lean`, `CompleteGvn.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`):

- `Opt.unreachableOk_raw`: `blocksOkB f = true → unreachableOk f (removeUnreachableRaw f) = true`,
  hence `Opt.removeUnreachable_eq_raw` (`removeUnreachable` never falls back). `blocksOkB` (unique
  block ids, every branch target a block) is decidable and follows from `wfCert` against any CFG
  (`Opt.blocksOkB_of_wfCert`, so from `check`: `Opt.blocksOkB_of_check`, and from `simpOk`). The
  core is the completeness of the depth-first search `Cfg.postorder` (`Opt.postorder_closed`: its
  fuel suffices, the entry is finished, the finished blocks are closed under successors). Witness
  `Opt.CompleteUnreachableWitness.witness`.
- `freshOkB`: `Opt.freshOkB_of_check` (S1).
- A declarative description of `check`: `Opt.checkCore_ok_iff` (`checkCore f = .ok i ↔ CoreOk f ∧
  i = coreInfo f`), `Opt.check_ok_iff`, and `Opt.wfCert_complete` (the converse of
  `wfCert_sound`: the certificate facts `Wf f (wfData f info)` make `wfCert` accept; via
  `Opt.ancB_complete`, the walk up the tree finds every ancestor within `idom.size` steps when ranks
  decrease along `idom`). `Opt.build_congr`: the CFG depends only on block ids and successors.
- DCE: `Opt.dce_complete : check g = .ok info → check (dce g).1 = .ok (coreInfo (dce g).1) ∧
  editOk id g (dce g).1 info (coreInfo (dce g).1) = true`. DCE filters each body with
  `dceKeep (dceLive g)` (`Opt.dce_eq`); the mark loop's fuel suffices and the live set is closed
  (`Opt.dceLive_closed`), so every operand of a kept statement or terminator is defined by a kept
  statement, at the filtered position (`Opt.dce_wf`); a deleted statement is removable and its
  results are defined nowhere in the output (values are defined once), which is `delOk`
  (`Opt.dce_delOk`, `Opt.align_filter`). Witness `Opt.CompleteDceWitness.witness`.
- `checkCore` from the certificate facts: `Opt.coreOk_of_wf` (CFG facts, definitions, entry
  parameters, branch argument and `br_table` index types, and `Wf f (wfData f (coreInfo f))` make
  `checkCore` accept; core: `Opt.dominates_complete`, the walk of `Cfg.dominates` finds every tree
  ancestor within its fuel). CFG facts: `Opt.postorder_nodup` (every block at most once in the
  postorder), `Opt.domChildren_spec` (the dominator-tree children lists are distinct blocks whose
  `idom` is the parent), `Opt.build_idom_size`.
- GVN: `Opt.gvn_complete : check g = .ok info → check (gvnFull g info local?).1 = .ok _ ∧
  editOk (gvnFull g info local?).2.2.find g (gvnFull g info local?).1 info _ = true`. What GVN
  does (`Opt.gvnFull_spec`): the walk over the dominator tree processes each block at most once
  (its stack and the processed blocks stay distinct, children have their parent processed), and
  every renaming `v ↦ w` deletes a pure `v = m` in favour of a kept pure `w = n` with
  `mapOperands S.find n = mapOperands S.find m`, `w` earlier in the block or in a strict tree
  ancestor (the scoped table holds only values of tree ancestors, `Opt.TblOk`); the substitution
  has no chains. So the output is the input with the renamed statements deleted and every operand
  renamed (`Opt.gvnF`); a renamed operand moves up the tree and keeps its type (both nodes have
  the same result types), so `Wf` holds (`Opt.gvn_wf`) and `check` accepts (`Opt.gvn_check`); a
  deleted statement is `delOk` through its replacement (`Opt.gvn_editOk`, `Opt.align_filter_map`).
  Witness `Opt.CompleteGvnWitness.witness`.

- LICM: `Opt.licm_complete : check g = .ok info → check (licm hk g info).1 = .ok _ ∧
  editOk id g (licm hk g info).1 info _ = true` (`FV/Opt/Proof/CompleteLicm.lean`,
  `CompleteLicmPass.lean`). Graph facts: the depth-first search is sound (`Opt.postorder_reach`),
  `preds` is the converse of `succs` (`Opt.build_preds_mem`), `Cfg.dominates` is sound, the
  dominator tree records blocks (`Opt.dominators_lt`), and every loop of `Cfg.loops` has the facts
  LICM needs (`Opt.loops_ok`: header in the body, body blocks tree descendants of the header, body
  closed under predecessors; the search's fuel suffices), so a block between the header and a
  loop block in the tree is in the loop (`Opt.loop_between`). `licmRound` is a fold over the
  loops (`Opt.licmRound_eq`); `Licm.lean` sorts `cfg.loops.attach` so every loop carries its
  membership in `cfg.loops` through `Array.qsort` (no reasoning about core's private sort
  internals). Each hoisted statement is one move to the end of the hoist block `idom header`
  (`Opt.hoistF_snoc`) with the preconditions of `Opt.MoveOk`: an operand outside the pass's
  `inside` set is defined in a strict tree ancestor of the header (or earlier in the hoist
  block), so it is available there (`Opt.hoist_step`). The moves keep the certificate facts
  (`Opt.Good`) and the relation to the input (`Opt.LRel`: same header, block ids, parameters,
  terminators and types; each body is the input body without the moved statements, followed by
  moved statements, each in a strict tree ancestor of its original block) across moves, loops
  and rounds (`Opt.licm_ok`); `editOk id` follows by `Opt.align_filter_append`, `check` by
  `Opt.coreOk_of_wf`. Witness `Opt.CompleteLicmWitness.witness`.

- `Cfg.dominators` computes the dominator tree within its `n + 2` rounds: `Opt.build_domFacts :
  DomFacts (Cfg.build f)` for every `f` (`FV/Opt/Proof/DomComplete.lean`; `Opt.DomFacts`,
  `FV/Opt/Proof/DomFacts.lean`: idom entries are blocks, the entry is the root, RPO numbers
  decrease towards the root, the edge certificate, and every dominator of a reachable block —
  every block on all paths to it, `Opt.ReachAvoid` — is a tree ancestor). Soundness is a property
  of each parent edge; completeness: after round `k` every path of fewer than `k` edges avoiding
  `a` to a block yields one to its parent, and paths of at most `|rpo|` edges suffice. Witness
  `Opt.DomCompleteWitness.witness` (an irreducible loop and nested loops).
- Re-checking after simplify: `Opt.check_removeUnreachable_of_wfCert'`
  (`FV/Opt/Proof/CompleteRecheck.lean`): if `f` passes `wfCert` against *any* CFG (as `simpOk`
  checks the simplify output against the input's tree), has unique definitions, entry parameters
  matching the signature, well-typed block-call arguments and `br_table` indices, then `check`
  accepts `removeUnreachable f`: tree ancestors of the given tree dominate in `f`'s graph,
  `removeUnreachableRaw` keeps exactly the reachable blocks (the new graph is the old one
  restricted), and the recomputed tree has every dominator as an ancestor (`build_domFacts`).
- The final guards (`FV/Opt/Proof/CompleteGuards.lean`): `keepsBackendSubset` follows from the
  transitive `Opt.KeepsB` (header, backend subset E, callees, no new `call_indirect`), kept by every
  stage (`keepsB_removeUnreachable`, `keepsB_dce`, `keepsB_gvn`, `keepsB_licm_of_check`, and for
  simplify `keepsB_simp'` from the stage facts `Opt.SimpGuard`). `keepsShapeB` really can reject:
  `Opt.CompleteGuardsWitness.counterexample` (branch folding makes the only `return_call` block
  unreachable; `optimizeExe` falls back to its input). On the decidable input condition
  `Opt.shapeSafeB` (no `return_call` resp. no indirect call, or one in the entry block, which no
  folding can remove) it accepts (`Opt.ShapeK`, `keepsShapeB_of_shapeK`).
- `allowedIn` (FV/Opt/Optimize.lean) no longer allows `symbol_value`: a `symbol_value` hash-consing
  hit in a block not dominated by its definition was cloned, and `simpOk` rejects an inserted
  `symbol_value` (`insOk`), so the whole simplify stage fell back on such functions (found by the
  completeness proof; `Opt.allowedIn_symbolValue`).
- The whole pipeline (`FV/Opt/Proof/CompleteOptimize.lean`): `Opt.runStages cfg f` is the stage
  loop of `optimizeReport` with every pass applied unconditionally (no `check`, no validator, no
  guard). `Opt.optimizeReport_complete : (∃ i, check (removeUnreachable f0) = .ok i) →
  (cfg.simplify = false ∨ SimpStageOk cfg) → (optimizeReport cfg f0).2.passError = none ∧
  (optimizeReport cfg f0).1 = runStages cfg (removeUnreachable f0)`, `Opt.optimize_complete`,
  `Opt.optimizeExe_complete` (with `shapeSafeB f0`), and the hypothesis-free instances for
  configurations with simplify off, `Opt.optimize_complete_noSimp` and
  `Opt.optimizeExe_complete_noSimp`. Witness `Opt.CompleteOptimizeWitness.witness` (GVN, DCE and
  LICM all change the function).

- Simplify (`FV/Opt/Proof/CompleteSimp*.lean`): `Opt.simpStageOk_of : SimpRulesProv cfg.simplifyFn →
  SkelRulesProv cfg.skeletonFn → SimpStageOk cfg`, from `Opt.simplify_complete` (`simpOk`, the
  re-check after `removeUnreachable`, and `SimpGuard` on the output of `simplify` with
  `allowedIn`/`skelAllowedIn`), hence `Opt.optimize_complete_of_rules`. The rule-set obligations
  (`FV/Opt/Proof/RulesProv.lean`) only say that the rules *pass values on*: for any set `Q` of
  values closed under node operands and any `make` returning `Q` values for nodes over `Q`, every
  candidate (and, for `simplify_skeleton`, every value of a candidate) is in `Q`. The pass's guards
  do the rest (`Opt.optimizeAt`, `Opt.skelMake`, `Opt.runSkel`): `make` hash-conses and simplifies
  only well-typed nodes over known values other than the root; another node over graph values
  becomes a *partial node* (`SState.partials`: it has its value but is outside the rules' graph,
  not hash-consed, never a candidate), a node over values outside the graph a fresh dummy value;
  candidates other than the root must be known values of its type (`SState.candOk`), skeleton
  candidates `skelCandOk` (known values; non-pure, non-symbol instructions; rewritten terminators
  are branches to the original's blocks with the same argument types — `SkelCandOk`). The pass layers:
  `materialize` (`mat_spec`), the rule driver (`opt_spec`, `runSkel_ok`), skeleton statements and
  terminators (`skelStmt_ok`, `skelTerm_ok`), pure statements (`pure_ok`), the run invariant
  (`SimpInv`, `RunDone`, `simplify_run_inv`) and the assembly (`simp_complete_of_run`). Witness
  `Opt.CompleteSimpWitness.witness` (hash-consing across dominating blocks, `noRules`). Also
  `Opt.simplify_incomplete_symbolValue`: with the former `allowedIn` (`isPure`), `simpOk` rejected
  a well-formed function with `symbol_value` in sibling blocks.

The obligations are discharged for every rule set a `Config` can select: the empty rule set
(`simpRulesProv_noRules`), the hand rules (`Opt.simpRulesProv_hand`, `Opt.skelRulesProv_hand`,
`FV/Opt/Proof/CompleteSimpHand.lean`) and the exported Cranelift rules with any allow-list
(`Opt.simpRulesProv_isle`, `Opt.skelRulesProv_isle`, `FV/Opt/Proof/IsleProv.lean`: an instance of
the program-generic value invariant of the ISLE interpreter, `Opt.Proof.runMultiTerm_prov` in
`FV/Opt/Proof/InterpProv.lean`; the rule data is never inspected). Hence, for **every**
configuration (`FV/Opt/Proof/CompleteSimpAll.lean`): `Opt.simpStageOk_cfg cfg : SimpStageOk cfg`
and `Opt.optimize_complete_cfg cfg f0 (h : ∃ i, check (removeUnreachable f0) = .ok i) :
(optimizeReport cfg f0).2.passError = none ∧ (optimizeReport cfg f0).1 = runStages cfg
(removeUnreachable f0)`, with the instances `Opt.optimize_complete_exe` (`exeConfig`) and
`Opt.optimize_complete_default`, and for `optimizeExe` (the executables' entry point, shape-safe
inputs) `Opt.optimizeExe_complete_cfg`/`Opt.optimizeExe_complete_exe`; witnesses
`Opt.CompleteSimpAll.witness_exe` and `witness_exe_entry` (`x + 0 ⇒ x` with
`exeConfig`), and `Opt.CompleteSimpWitness.witness_hand` for the hand rules
(`Opt.optimize_complete_hand`). The guards never fire on the inputs: `scripts/opt-compare.py`
against the binary without them, 2642 files (corpus+extrt 50, runtests 395, survey and fv-demo
dumps 2197) × default, `--opt-proven-only`, `--opt-rules hand`: all byte-identical, `--stats`
identical. The certificate carries the partial nodes (`SimpCert.partials`, part of the graph
`SimpCert.graph`) and `simpOk` checks that none is a leaf of the input.

Earlier step (the hand rules): `pureBest` no
longer puts `inst ↦ v` into the hash-consing table before the rules run (as in Cranelift's
`insert_pure_enode`, the node enters the table after its rules ran, mapped to the best value):
with the pre-insertion a nested `make` of the root's node returned `v` itself, which the
obligation excludes. Measured with `scripts/opt-compare.py` (both binaries, every input, default,
`--opt-proven-only` and `--opt-rules hand`): 2642 files (corpus+extrt 50, runtests 395, survey and
fv-demo dumps 2197); hand: all byte-identical; default and proven: 2497 byte-identical, 145 equal up
to a per-function renumbering of values with identical `--stats`, 0 other differences.


### Simplify pass proof (MidSimplify, MidSimplify2: done)

Design (validator + driver invariant): `Opt.simplify` returns a certificate `Opt.SimpCert`
(final graph `defs`/`types`, renaming `subst`, per-block `BlockLog`s: every statement's fate
`StmtLog.keep/repl/skel` with the emitted statements, every terminator's rewrite).
`optimizeReport` accepts the simplify output only if `Opt.simpOk f g info cert`
(`FV/Opt/Validate.lean`), which checks the *structure*: `g` is `wfCert`-well-formed over `f`'s
dominator tree with the certificate's types (which agree with `check f` on the leaves), every
block of `g` is the logged output renamed by a chain-free `subst`, kept statements and
replacement instructions have unrenamed results/operands, inserted statements are pure nodes
of the certificate graph (`D x = inst` for every pure single-result statement of `g`),
statements that are not single-result pure nodes define leaves (`initAvail f`, not graph
nodes), replacements are available where the replaced value was defined, skeleton rewrites
are of non-call, non-`symbol_value` statements into non-call, non-`symbol_value`
instructions, a rewritten terminator is a branch and its extra statements are inserted
nodes or conditional traps (`trapz`/`trapnz`, unrenamed).

The *semantics* is the pass's own theorem, split in two:

- `Opt.SimpFacts f info cert` (`FV/Opt/Proof/SimpFacts.lean`): for every valuation `ρ` of the
  leaves (typed as `check f` says), frame (globals/slots of `f`) and memory defining every
  symbol, in the certificate graph's valuation `V := den cert.graph ρ fr mem`: a replaced pure
  `v = n` has its replacement `w` with `n`'s value (`V w ⊇ evalNode n V`); a rewritten skeleton
  statement is refined by its outcome (`SkelFact`: `remove`/`removeWithVal` keep memory, do not
  trap and give the value; `replace i`/`two a b` refine as `ResRefines`); a rewritten
  terminator is refined by the conditional traps of `extra` then the new terminator, modulo
  the trap blocks of `f` (`BrRefines` over `effTerm`).
- `Opt.simplify_facts` (`FV/Opt/Proof/SimpLoop.lean`): every run has them, for rule sets
  satisfying `SimplifySound`/`SkeletonSound`. Loop invariant over `stepStmt`/`stepBlock`/the
  RPO fold: `GInv` and, for every record made so far, its fact in the current valuation with the
  values its source instruction reads known. A fact is made when the record is (`pureBest`:
  hash-consing hit or `optimizeAt_spec`; `pureEmit`: `materialize_spec`; `skelStmt_spec` /
  `skelTerm_spec`: `runSkel_spec` composed along the rewrite chain, through the renamings of
  `materializeAll` — `rename_spec`, `evalInst_rename`/`termEval_rename` up to stuck messages);
  it persists (`LogFact.grow`, `TermFact.grow`) because known values keep their value (`Mono`)
  and the valuation only grows (`gval_le`), so a refinement read from a not-stuck evaluation
  stays true. The final valuation is `den` of the certificate's graph.
- `Opt.simpOk_sim` (`FV/Opt/Proof/SimpSim.lean`): the simulation. Frames are related at
  corresponding positions (`SRel`: `Inv` of both functions, every available source value `v`
  has `σ v` available in the target with the same value and defined in a dominator of `v`'s
  definition, the target at the start of the record of the source's next statement). Each
  source statement is matched by its record (lock-step for kept statements and calls;
  inserted pure nodes are target-only steps that cannot fail; a replaced or removed statement
  is a source-only step; `replace`/`two` step against the fact). The facts are read in the
  target frame through `den_agree`: every value available in the target is the certificate
  graph's `den` of the leaves read off the target registers (`rhoAt`), evaluated in the memory
  with all symbols completed (`memPlus`; only `symbol_value` reads symbols, which the
  validator keeps out of skeleton rewrites). A branch redirected to a trap block traps at once
  in the target; the source still runs the trap block's pure body (`Frozen`).

Behaviour: the driver was only refactored (named `trapMap`, `initAvail`, `memoHit`,
`pureInsert`, `pureBest`, `pureEmit`, `pureAlts`, `StmtLog.rep`, `isTrapLike`) and the
validator strengthened. On all difftest inputs (corpus, extrt, runtests, survey: 474 files, default and
`--opt-proven-only`) `clif-opt` output and `--stats` are byte-identical to main 1553070 and
the validator accepts everything (`pass-errors 0`); the same for `opt-fuzz` seeds 1–3 (150 E
and 150 `--ext` functions each: 7 200/7 200 runs agree); `opt-difftest`: corpus 4 668 → 2 287
(proven-only 2 753), runtests 3 383 → 3 040, 0 fail.

Driver sanity checks added for the proof (MidSimplify; never fire on these inputs):
made nodes only over values of the graph (else a fresh dummy value); made nodes that are not
well-typed over known values other than the rewritten root are recorded as partial nodes
(`SState.partials`, see the completeness section above) and not simplified, top-level statements enter the graph only if new,
below `next`, well-typed over available operands (else kept outside the graph, which
`simpOk` rejects), clones must be well-typed and typed values, no cycle in `materialize`,
`chooseBest`'s sort result filtered by membership, `chooseSkel` as a recursive scan, the
alternatives' representative computed from the log, a terminator's `replaceWithTwo` prefix
must be `trapz`/`trapnz`.

Interface change (agreed with MidRulesInfra, commit 99341ce merged): `SimplifySound`'s `P`/`Le`
conclusion no longer requires `den st v = some a` (the class value is quantified after it).

Graph layer (MidSimplify): `FV/Opt/Proof/SimpDen.lean` — the graph valuation `den D ρ fr mem`
(least model of the node equations; `den_node`, `den_leaf`, `den_le_of`, `den_insert_fresh`,
`Twin`/`den_overwrite`), `evalInst_ops`/`evalInst_mono`; `SimpGraph.lean` — the invariant
`GInv` (closed graph over known values, fresh values above `next`, available and solid values
defined and typed, `alts`/`memo`/`classes` justified forward), `fresh_spec`/`insert_spec`,
`chooseBest_spec`, `optimizeAt_spec` (via `SimplifySound`), `skelMake_sound`, `runSkel_spec`
(via `SkeletonSound`); `SimpMat.lean` — `materialize_spec`, `materializeAll_spec`,
`rename_spec`.

Remaining E2E premises (stated, not derived): `EnvKeepsSymbols env` (a property of the extern
environment), `TrapsExplicit` of the optimised program's run from `optEntry` (the forward
simulation says nothing about the optimised run once the source gets stuck, so it is not
derived from the source's), `FormsCovered` of the compiled optimised code (decided per function).

Build note: `FV/Opt/Proof/RuleImm.lean` imports `FV.Backend.Proof.IselCmpExt`; while both
called `bv_decide` (before T6) this let them share one generated `Clif.Ty.enumToBitVec` (otherwise
no module could import the rule proofs and the backend together).

Design decisions (approved by the integrator):

- **Validators instead of proofs of the imperative loops.** `check` also runs the declarative
  certificate `wfCert` (definition-site map, idom tree with decreasing RPO numbers and the edge
  certificate "for every edge `u → b`, `idom b` is a tree ancestor of `u`", typing).
  `removeUnreachable` validates itself (`unreachableOk`, else returns its input).
  `optimizeReport` accepts GVN/DCE/LICM output only if `editOk` holds (`FV/Opt/Validate.lean`;
  `gvnFull` returns its substitution), else stops like a `check` failure (`passError`). A final
  guard `keepsBackendSubset` keeps the input if the output would leave E or call new callees.
  On every difftest input all validators accept: corpus 4 668 → 2 287, runtests 3 383 → 3 040,
  survey 116 996 → 67 395, `pass-errors 0`, `ill-formed 0`; `opt-fuzz` seeds 1–2 (E and
  `--ext`) 3 200/3 200 agree.
- Extra E2E premises: `EnvKeepsSymbols env` (externs keep the link-time symbols, so
  `symbol_value` is a constant), `TrapsExplicit` about the optimised program's run
  (`optEntry`), `FormsCovered` of the optimised code (decided, as before).

## Rule proofs (MidRulesFoundation, branch `agent/mid-rules`)

Status: the framework is complete and proven; **1154 `simplify` roots proven** (see below),
allow-list embedding done. Files `FV/Opt/Proof/{Sem,InterpMatch,InterpState,InterpEval,RuleBase,
RuleData,RuleNode,RuleEmbed,RuleTactic,RuleImm,RuleCtor,RuleSkel,RuleAuto,RuleArith,RuleCprop,
RuleAll}.lean`; generator
`FVTest/Opt/Proof/GenData.lean` (`lake env lean --run FVTest/Opt/Proof/GenData.lean >
FV/Opt/Proof/RuleData.lean`, 33 s build). No `sorry`; axioms of every theorem below
(`RuleAll.simplifyRulesCorrect_proven` and the rule theorems): `propext`, `Classical.choice`,
`Quot.sound` only. No `bv_decide`, `native_decide` or `Lean.ofReduceBool` under `FV/Opt` (T6;
before, the `*._native.bv_decide.ax_*` certificates of the `bv_decide` calls). Full build of
the rule modules: see the build note under "Proven rules" (`RuleArith.lean` dominates).

**`kbv`** (T6, `FV/Opt/Proof/KernelBV.lean`): kernel-checked decision for the concrete-width
bit-vector goals of the rule proofs, in place of `bv_decide`. It restates the goal over its
bit-vector context (bit-vector/`Bool`/`Nat`/`Int` locals and facts) and tries, under heartbeat
budgets (`kbv_guard`: 20 000 to 2 000 000 `maxHeartbeats` units per method, 4 000 000 for the
whole search of a goal), kernel-checked methods: `bv_normalize`
(`bv_decide`'s `simp` preprocessing), bit extensionality + a Boolean tautology over the bits
(`decide`), case splits on `if`/`bif` conditions, `toNat`/`toInt` arithmetic with `omega`,
minterm decomposition + `grind`, case splits on constant shift amounts, sign-mask lemmas
(`sshiftRight` by `w-1`, `(x ||| -x).msb`), per-index bit evaluation. The shift and spaceship
modules (`RuleShifts1`..`5`, `RuleSpaceship`) first try a targeted method on each goal
(`kbv_amt`/`kbv_cmp`, `FV/Opt/Proof/RuleInfraShiftAmt.lean`, through a module-`local`
`elab_rules` for `kbv`): shift amounts as `Nat` arithmetic, rotations as `rotateLeft`, comparison
results by case split. Some lemmas are proved by hand instead (bswap/popcount, pow2
`sdiv`/`srem`, the immediate specs of `RuleImm.lean`).

**Interface** (`Sem.lean`, owned by MidPassProofs, copied byte-identical): `Opt.evalNode`,
`Opt.Valuation`, `GraphModel` (A1 nodes, A2 types), `MakeSound` (A3), `SimplifySound`,
`SkeletonSound`.

**Theorems.**
- `InterpMatch.matchPatN_sound`: every environment of the multi-matcher satisfies `PatRel`
  (relational reading of a pattern: one existential per extractor value).
- `InterpState.pres_single` / `pres_multi`: if every extern constructor keeps an invariant and
  moves along a preorder, so does every interpreter function (single and multi) at every fuel;
  `bindAll_run_mem`: a result of `bindAll` comes from one call between reachable states.
- `RuleBase.RuleOk p r`: the per-rule obligation (for all bindings the LHS relates to
  `[.value v]`, all if-let environments and every RHS value, from any later state: the made
  class has `v`'s value); `SimplifyRulesCorrect p allow`.
- `RuleBase.applyMulti_sound`, `RuleBase.simplifySound` (**interpreter soundness + lifting**):
  `SimplifyRulesCorrect program allow → SimplifySound (Isle.Opt.simplify · allow)`.
- `RuleAll.simplifyRulesCorrect_proven`, `RuleAll.simplifySound_proven :
  SimplifySound (RuleSetId.fnWith .proven .cranelift)` — the obligation `simplify`'s pass proof
  takes with `Config.ruleAllow := .proven`.

**Embedding changes** (`FV/Isle/Opt/Simplify.lean`, behaviour-preserving except the first):
`ofInst` no longer presents `iconst.i128` (its `Imm64` presentation truncated; Cranelift rejects
`iconst.i128`), so no rule can match it; `ctorFn` split into `ctorPure` (state-preserving
helpers) + the three state-changing constructors (makes the state lemma a 4-way split);
`simplify`/`simplifySkeleton` take `allow : RuleId → Bool := fun _ => true` and drop
candidates of other rules (the rules still run: their `make`s stay, which `MakeSound` covers).
Driver: `Opt.RuleAllow` (`all` default | `proven` | `ids`), `RuleSetId.fnWith`/`skeletonFnWith`,
`Config.ruleAllow`, `Config.simplifyFn`/`skeletonFn` (the only change in `optimizeReport` is
the `simplify` call's arguments), option `--opt-proven-only`. Corpus difftest: default 114/114
agree, 4321 → 2018 insts; `--opt-proven-only` 114/114, 4321 → 2475 (skeleton rules off).

**Proven rules** (MidRulesInfra2, RulesBitops, RulesIcmpSel, RuleAllScale, RulesShiftsExt, RulesRest, R0–R5, R7–R8): **1154 `simplify` roots** = `Opt.provenSimplifyRules` —
`arithmetic.isle` 258 of 258 (`RuleArith.lean`, `RuleArith2..8.lean`, `RuleArithMulHi`,
`RuleArithOdd`, `RuleArithCancel`, `RuleArithProducts`, with `MulHiSem`/`OddSem` helpers),
`cprop.isle` 68 of 68 (`RuleCprop.lean`, `RuleCprop2..4.lean`), `remat.isle` 12 of 12 (`RuleRemat.lean`),
`bitops.isle` 450 of 450 (`RuleBitops1..10.lean`, tactics/lemmas in `RuleBitopsEmbed.lean`:
`rule_auto` 393, `rule_auto_b` 18, `rule_auto_i` 2, `rule_auto_z` 31; R0: `rule_auto_t`/`_tt` 3; R7: masked-OR and byte-swap proofs 3). **All 37 `simplify_skeleton` roots**
(`Opt.provenSkeletonRules`, `RuleSkeleton.lean`, `RuleSkeleton2..6.lean`, see "Skeleton rules" below).
`icmp.isle` 124 of 124 (`RuleIcmp1..10.lean`, `RuleIcmp12.lean`, `RuleIcmp13.lean`,
`RuleIcmpIdentity.lean`, `RuleIcmpBounds.lean`, `RuleIcmpArithmetic.lean`,
`RuleIcmpSelects.lean`, `RuleIcmpCompose.lean`) and `selects.isle` 100 of 100 (`RuleSelects1..12.lean`),
with the template variants of `RuleIcmpEmbed.lean` (`rule_auto_c`/`_ci`: `arr_step` for a value
variable bound twice, `opt_split_typeof` for a made `icmp` under `subsume`; `_d`/`_di`: `Int`
literals of if-lets reduced, `ty_smin`/`ty_smax` specs passed as extra lemmas) and
`RuleIcmpEmbed2.lean` (`extractMulti_uem`: the `uextend_maybe` multi-extractor; `_e`/`_ei`:
signed immediates as sign-bit facts; `_f`/`_fi`/`_fz`/`_fiz`: the left-hand side without
`simp_all`, which rewrites a literal-match fact such as `asU64 imm = 0` away with a copy of itself;
`_g`: `_f` plus the `P s0`-guarded model facts and `opt_den_merge`). Each theorem names the
`first` chain it was checked with.
`extends.isle` 29 of 29 (`RuleExtends.lean`, `RuleExtends2.lean`), `shifts.isle` 73 of 75
(`RuleShifts1..5.lean`, `RuleShiftsConst`, `RuleShiftsRotate`, `RuleShiftsDistribution`,
with `ConstSem`/`RotateSem` helpers), `spaceship.isle` 40 of 40
(`RuleSpaceship.lean`, `RuleSpaceshipSelects.lean`), with the templates of
`RuleExtEmbed.lean` (`rule_auto_x`: width side conditions of made `ireduce`/extends, `Val` type
equalities substituted, `int_bv` turning `Int` immediates/if-let conditions into `BitVec`;
`_xr`: if-let results of internal constructors such as `iconst_u` split; `_xz`: `Val`s split and
types split on `i128` so `ty_mask` evaluates; `_cat`: shift amounts given by `iconcat`; `_y`:
`typeOf` reads split eagerly; `imm64_shl ty -1 k`/`imm64_ushr ty ty_mask k` specs).
RulesRest templates (`RuleRestEmbed.lean`): `rule_auto_v` (`rule_auto_xz` whose if-lets unfold
`matchAllN`/`bindAll`, keeping the conditions of internal constructors' rule matches such as
`shift_amt_to_type`; `imm64Masked_i128`; `i64SextendU64_spec` for `iconst_s ty k` under a type
variable), `rule_auto_w` (`rule_auto_y` plus `opt_rw_typeof`, `opt_heq_typeof`, `opt_beq_subst`,
`opt_ty_facts` for the later `value_type` reads of `iadd_uextend`/`isub_uextend`), `rule_finish_w`
(closed type side facts decided, width side conditions of made extends, `bif`/conjunction facts
split, `val_congr` after the type split); helper specs `imm64_sshr`, `imm64_rotl`, `imm64_rotr`
(`opt_imm`).
**R0 (RuleInfra, 2026-10-07): shared infrastructure, 43 `simplify` + 10 skeleton roots.** The
helpers live in new `RuleInfra*.lean` files (or in the new rule module) that no older rule module
imports, so the older modules did not rebuild.
- `iabs` (`RuleInfraAbs.lean`): `iabs_bif` (`Sem.iabs x = bif x.msb then -x else x`) in
  `sem_simp_a`; `rule_bits_a` cancels products of negations (`BitVec.neg_mul_neg`) before the type
  split and drops `rule_bits_b`'s `rfl`/`ac_rfl` attempts (they hit the maximum recursion depth,
  which `first` does not catch); `rule_auto_a`. Proves `arithmetic.isle` 38, 42, 46
  (`RuleArith6.lean`) and `selects.isle` 97–100 (`RuleSelects7.lean`).
- `truthy` in an if-let (`RuleInfraAbs.lean`): `truthy_iflets` lifts `truthy_sound`
  (`RuleSkelEmbed.lean`) to `(if-let x (truthy v))` at any variable indices followed by further
  if-lets (each result class has the truthiness of `v`); `rule_auto_t`, `rule_auto_tt` (with the
  `value_type (ty_int_ref_scalar_64_extract ty)` if-let). Proves `bitops.isle` 126, 127, 129
  (`RuleBitops8.lean`).
- Constants made under a type variable (`RuleInfraConst.lean`): `makeInst` was not stuck; the
  right-hand side reduces once the type is split on `i128` (at `i128`, `iconst_u`/`iconst_s` build
  an extend of an `i64` constant). The old templates failed at the finish (`ac_rfl` recursion
  depth, `bv_decide` after the `Val` split, symbolic products). `rule_bits_tv` (no `Val` split,
  impossible `i128` cases by `contradiction`, `BitVec.neg_mul`/`mul_neg`/`neg_neg` first, then
  `kbv`), `rule_auto_tv`; `imm64Neg_ofInt` (`imm64_neg` of any immediate, for the sign-cast
  immediate of `cprop.isle` 269), `asI64_asU64_cast`, `ofInt_asI64_low`. Proves `arithmetic.isle`
  50, 333, 334, 343, 349, 587, 590, 593, 596, 603 (`RuleArith7.lean`) and `cprop.isle` 269
  (`RuleCprop4.lean`).
- `u64_bswap16/32/64` (`RuleCprop3.lean`): `bswap16_spec`/`bswap32_spec`/`bswap64_spec`
  (`BitVec.ofInt w (asI64 (Rust.bswap k b.toNat)) = Sem.bswap b`), `rule_auto_bswap`. Proves
  `cprop.isle` 375, 377, 379; 320, 322, 324 by `rule_auto_xr` (first run with the current
  templates). `cprop.isle` is complete.
- icmp/selects module memory (`RuleInfraIcmp.lean`, `RuleInfraI128.lean`): the old proofs kept the
  model facts guarded by `P s0` (`rule_lhs_f`), so the types stayed free and the finish split every
  type under `simp_all`/`bv_decide`; the made `iconcat` went through `binaryOfIdx? 155`, a literal
  match `simp` does not reduce, copied into every later state. Now `rule_lhs_g` opens the guards,
  `↓binaryOfIdx?_iconcat` removes the stuck match, `evalNode_iconcat_i64` evaluates the made
  `iconcat`, `cat128_*` (`select (eq ah bh) (icmp cc_lo al bl) (icmp cc ah bh) = icmp cc (ah ++ al)
  (bh ++ bl)`, by `cat_bits` on the 64-bit halves; until T6 `bv_decide`) closes the 128-bit comparisons, and
  `intcc_complement`/`icmp_eq_uext_icmp_zero`/… close the complemented comparisons without
  splitting the compared type (`rule_pre_k`, `fin_icmp_not_k`, `fin_bits_k`, `fin_sel_bmask_k`,
  `rule_auto_i128cmp`). Lean elaborates the theorems of a file in parallel whatever
  `LEAN_NUM_THREADS` is; modules with heavy rules set `set_option Elab.async false`. Proves
  `icmp.isle` 63, 70, 160, 175, 365, 368 (`RuleIcmp10.lean`), 254–269 (`RuleIcmp12.lean`), 274–289
  (`RuleIcmp13.lean`) and `selects.isle` 20 (`RuleSelects8.lean`), each in 8–40 s and ≤ 5.3G.
- Powers of two (`RuleInfraPow2.lean`, names `pow2_*`): `pow2_imm64PowerOfTwo_ty`
  (`imm64PowerOfTwo (imm64OfBits b) = some e ↔ ∃ k < min w 63, b = twoPow w k ∧ e = k`), the
  `i64_is_*_power_of_two`, `ctz`, `u64_ilog2`, `u64_shl`/`i64_shl` specs, division by `±2^k` as
  shifts and masks (`pow2_sdiv_twoPow`, `pow2_umod_twoPow`, `pow2_srem_*`), per-rule sequence lemmas
  with the exponent as a `BitVec` (per width; until T6 `bv_decide`), templates `pow2_auto_simp`,
  `pow2_auto_div`. Proves `arithmetic.isle` 181 (`RuleArith8.lean`) and the skeleton rules
  `arithmetic.isle` 83, 87, 102, 135 and `skeleton.isle` 80 (`RuleSkeleton2.lean`), 142
  (`RuleSkeleton4.lean`, 6 min / 6.3G alone).
- `div_const` magic numbers (`RuleInfraDivConst.lean`, namespace `Opt.Proof.DivConst`):
  `magicU_spec` (for `2 ≤ d < 2^w`, `d` not a power of two: `magicU w d = (m, add, s)`, and the
  emitted sequence, `x*m/2^w/2^s` or `((x - x*m/2^w)/2 + x*m/2^w)/2^(s-1)`, is `x / d` for every
  `x < 2^w`) and `magicS_spec` (the signed sequence with its add/sub fix-up and sign correction is
  `x.tdiv d` for every signed `w`-bit `x`), by invariant proofs of the Rust loops
  (`loopU`/`loopS`, Granlund–Montgomery / Hacker's Delight 10-9 bounds). Proves the unsigned skeleton
  rules `arithmetic.isle` 114, 117, 157, 160 (`RuleSkeleton3.lean`, `skel_auto_dcu32/64`).

Integration verification (2026-10-08): the full FV/FVTest/tool build and crate proofs pass.
Proven-only differential tests have zero failures: corpus 4668 → 2289 instructions, runtests
3389 → 3010, survey 355 → 190; the verifier rejects no optimized files. Direct CLI smoke on
`runtests/urem.clif` replaces constant i32/i64 remainders with the proven multiply/shift
sequence; the optimized file passes all 82 run expectations. The E2E and crate axiom checks
contain only the permitted axioms; `magicU_spec` and `magicS_spec` use only `propext`,
`Classical.choice` and `Quot.sound`. The four signed `div_const` rule applications were still
disabled at that checkpoint; R9 completes them below.

**False under the CLIF semantics (findings):** `shifts.isle` 84 and 88 (`sshr`/`ushr (ishl x k) k` to
`s/uextend ty (ireduce ty_small x)`): `u64_wrapping_sub (ty_bits ty) shift_u64` wraps for shift
constants above the type width, e.g. `ishl.i8 x, v` / `sshr.i8 _, v` with `v = iconst.i64 -8`
(or `-24`; `i16` with `-16`): `ty_small` becomes `i16`/`i32`, wider than `ty`, so the rule builds
`ireduce.i16` of an `i8` value and `sextend.i8` of it — ill-typed IR with no value, while the
original is `x` (shift amount `-8 mod 8 = 0`). The proof fails exactly in these cases.
All arithmetic roots are now proven. R1 closes the remaining RulesRest/R0 gaps:
200/206 (high products), 251–288 (eight odd-multiplier comparisons), 410–421
(eight repeated-operand cancellations), 427/428 (negated products), and 615–622
(squared signed/unsigned maxima). Exact guard normalization and symbolic identities
replace the earlier heartbeat, type-unification and wide-product SAT failures.
The original `RuleOk` statements and fuel premises are unchanged. See "R1" below.
R8 proves the remaining `extends.isle` roots 40, 42, 44 (`eq`/`ne`/signed `icmp` of a
`sextend` against `iconst_s 0`), completing that family. R4 proves every sound original
shift root left by RulesShiftsExt: 161, 170, 184, 193, 239–242, 244–247, 259, 261,
264, 266 and 315. Exact masked-sum guards, modular amount arithmetic, symbolic
rotation indices and shift/subtraction distribution replace the earlier recursion,
heartbeat and SAT failures. Original `RuleOk` statements and fuel are unchanged.
Only the documented false roots 84 and 88 remain disabled. Proven by RulesRest:
`shifts.isle` 41, 50, 61, 71, 152, 270, 280, 285.
All `spaceship.isle` roots are now proven. R5 factors the two comparison constructors and
`sextend_maybe` into shared typed RHS proofs, avoiding the earlier per-root term explosion.
All `selects.isle` roots are now proven. R3 closes 15, 81, 85, 188, 189, 193–196 and
199–202 in `RuleSelects9..12.lean`, preserving the original `RuleOk` premises.
Early denotation substitution, unsigned-literal normalization and width-parametric
select identities replace the earlier timeout-prone case splitting; see "R3" below.
Removed from the icmp/selects modules (RuleAllScale, 2026-10-01) because the modules ran out of
memory: `icmp.isle` 63, 70, 160, 175, 254–289, 365, 368, `selects.isle` 20 — all proven again by
R0 in their own modules at ≤ 5.3G (see above). R2 now proves all remaining icmp roots:
49, 77, 91, 155, 165, 170, 180, 184, 205, 295, 296, 386, 394, 402 and 410.
The earlier unification failures, timeouts and solver counterexamples were proof-tooling
failures, not counterexamples to these original rules; no `RuleOk` premise was added.
All `bitops.isle` roots are now proven. R7 closes 79 (the masked-OR immediate guard) and
157/170 (32/64-bit byte-swap trees) using bounded fixed-width identities and an opcode-indexed
decoder that avoids the earlier graph-matching branch explosion. R0 proved 126/127/129
(`truthy` in an if-let). Build note: changing
`FV/Opt/Rules.lean` (or anything under `RuleBase`) rebuilds every rule module; the allow-list lives
in `FV/Opt/RuleAllow.lean`, which no rule module imports, so extending it rebuilds only
`Optimize`, `RuleAll` and their dependents. Build the rule modules one at a time (`lake build
FV.Opt.Proof.RuleArith`, …, `RuleSelects6`; `LEAN_NUM_THREADS=2`, 16G cap; with `bv_decide`, 2026-10-01: `RuleArith`
14 min / 15.4G, `RuleBitops1..7` 1–11 min / 3–11.7G, `RuleCprop` 3 min / 7.4G, icmp/selects
modules 0.3–5 min / ≤5.2G; 2026-10-07, R0 modules: `RuleCprop3` 5 min / 11.4G, `RuleSkeleton3`
13.5 min / 7.6G, `RuleSkeleton4` 6 min / 6.6G, `RuleSkeleton2` 4.3 min / 3.6G, `RuleIcmp12`/`13`
3 min / 5.3G, the others < 2.5 min / ≤ 4.6G), then `RuleAll`/`FV.E2E.OptProven` (parallel builds of the rule modules
OOM). Since T6 the `kbv`-based rule modules (`FV.Opt.Proof.Rule*`) are heavier, and `lake build`
(it has no `-j` option) runs many of them at once, which exceeds a 22G `scripts/memcap.sh` cap.
Build the `FV.Opt.Proof` modules (203 with their imports) first, in import order, one memcapped
`lake build FV.Opt.Proof.<Module>` per module: `scripts/lake-serial-build.py --budget 16G FV.Opt.Proof.`
(docs/TO-PROVE.md §7; caps from recorded peaks, modules above 12 GB alone); the full target build then
replays them. Measured 2026-10-12 (`maxrss`, three at a time): `RuleBitops7` 16.5 GB / 4 min
(alone at 22G), `RuleArith` 14.0 GB / 6 min, `RuleBitops2`..`5` 9–11 GB / 5–6 min, `RuleExtends2`
10 GB / 14 min, `RuleShifts2`/`3` 9.7/10 GB / 8/18 min, `RuleIcmp2` 22 min, `RuleSkeleton3`
18 min, `RuleSkeleton5` 34 min, the others less; all 317 in 2 h 4 min. Since 2026-10-22 the seven
heaviest (`RuleBitops7`, `RuleArith`, `RuleBitops2`, `RuleBitops5`, `RuleShifts2`, `RuleShifts3`,
`RuleRestEmbed`) are split into part modules (`<Module>P1`.., `RuleRestEmbedBase`/`Sshr`/`Rotl`/`Rotr`);
each old module only imports its parts, so importers are unchanged. Standalone peaks, before → max part:
`RuleBitops7` 19.3 → 6.1 GB, `RuleArith` 15.2 → 4.5 GB, `RuleRestEmbed` 15.8 → 8.6 GB, `RuleBitops2`
12.7 → 5.2 GB, `RuleBitops5` 11.0 → 6.3 GB, `RuleShifts2` 9.5 → 6.1 GB; `RuleShifts3P1` (`shifts_41`)
stayed at about 10 GB until `kbv_amt` learned the shift identities its goals need (LEARNINGS.md,
"Close recurring goal shapes before the general `kbv` search"). Check the log for "Build completed successfully": `memcap.sh` under `/usr/bin/time` can
report rc=0 for an OOM-killed build. `RuleAll` itself: 16 s, 3.6G (`LEAN_NUM_THREADS=1`; kernel
check of the `allowed_ok%` term, ~0.3 s to build it). Its previous form (`rfl` on the
`List.filter` of the 1281 `simplify` rules by `provenSimplifyRules.contains`, elaborated by
`Meta.isDefEq`, then an `AllOk` conjunction) cost 74 s, 11.4G at the same 842 rules (33 s elaborator `rfl`, 40 s kernel); the 32G OOMs
seen when building `RuleAll` at 872 rules came from the icmp/selects modules it imports.
Helper specifications (`RuleImm.lean`, simp set `opt_imm`): `imm64_add/sub/mul/and/or/xor/not/neg/
umin/umax/smin/smax/icmp/masked/clz/ctz/shl/ushr` at every non-`i128` type, in the normal form
`Rust.imm64X (ofClif t) (imm64OfBits b) … = .ok (imm64OfBits (<BitVec op> b …))` (proof: `imm_pre`
unfolds the helper, `imm_cases` splits the widths, `imm_solve` turns `Int` arithmetic into
`BitVec 64` and runs `kbv`, until T6 `bv_decide`; some specs are proved by hand; `clz`/`ctz` bridge `Nat.log2`/the Rust loop to `BitVec.clz`/`ctz`).

**Skeleton rules** (SkeletonProof, 2026-10-01). *Framework fix:* `SkelRuleOk` could not be met:
the left-hand side's node facts hold in the start state, but `SkelRefines` is checked in later
valuations, and a class undefined at the start may become defined later with a value unrelated to
the matched nodes. Now `Opt.skelReads i` (every operand of an instruction; the condition of
`brif`, the index of `br_table`) must be defined when the rules run: `SkeletonSound` concludes the
refinement only under `∀ y ∈ skelReads i, ∃ a, den st y = some a`, and `SkelRuleOk` gets it as
the invariant `SkelReadsDef` of `RuleSpec` (defined reads keep their value in every later state).
The pass discharges the undefined case itself (`runSkel_spec`, new premise: the reads are known):
known values never change their valuation (`Grow.fix`), so an undefined read stays undefined and
the original is stuck (`skelRefines_of_undef`, via `evalInst_ops`). `simplify_facts`,
`simplifyPassSim`, `optimize_sim_proven` and `E2E.backend_correct_opt_proven` keep their
statements. `RuleBase`: `RuleSpecAt fm` / `applyMulti_genAt` (fuel-general lifting; `RuleSpec`,
`applyMulti_gen` are the `fuelMin` instances) so a multi term called from an if-let can be lifted.
*Template* (`RuleSkelEmbed.lean`): `inst_data`/`ofSkel` inversion, outcome lemmas per shape
(`skel_div_rwv`, `skel_trapz_remove`, `skel_brif_jump_then/else`, `skel_brTable_jump`,
`skel_brif_cond`, `skel_trapz/trapnz_cond`, `skel_brif_two_then/else`), `skel_auto_div`,
`skel_auto_div_i`, `skel_auto_br`, `skel_auto_truthy`; `imm64_udiv/urem/sdiv/srem` specs;
`truthy` soundness (`TruthyOk` for its 11 rules, `truthy_sound`, `truthy_iflet`).
*Proven* (all 37): `arithmetic.isle` 79, 80, 130, 131, 132, and by R0 83, 87, 102, 135, 142
(power-of-two `div`/`rem`), 114, 117, 157, 160 (unsigned `div_const`); `cprop.isle` 32, 38, 44,
50; `skeleton.isle` 7, 9, 22, 26, 33, 37, 44, 50, 53, 56, and by R0 80. R9 adds
`arithmetic.isle` 122, 125, 165, 168 and `icmp.isle` 461, 466, 471, 475.

**R9 (2026-10-09, `agent/skeleton-r9`):**
- `RuleSkeleton5.lean` connects `magicS_spec` to the four signed i32/i64 division/remainder
  rules. The `sdc_*` lemmas prove signed high-half multiplication, range-preserving
  add/subtract corrections, arithmetic shifts, truncation toward zero, and remainder
  reconstruction. Concrete witnesses cover signed minima and all multiplier/divisor sign
  branches. The rule statements and their input premises are unchanged.
- `RuleSkeleton6.lean` proves the four count-based branch rewrites, including optional
  `ireduce`. Shared local definitions prevent duplicated graph-constructor states; width-aware
  denotation supplies the i128 constant extensions. Generic count-zero and bounded-reduction
  lemmas close branch truthiness directly, without reflecting the generated graph context.
  A count is at most 128, so even reduction to i8 preserves its zero/nonzero distinction.
- CLI smoke: all eight roots fire in 66 functions; 798 exact interpreter expectations pass,
  the Cranelift verifier accepts all 66 optimized functions, and all 798 AArch64 executions
  agree with Cranelift-native, with no unsupported cases. Coverage includes signed extrema,
  both divisor signs, all correction branches, and count branches at i8/i16/i32/i64/i128.
- Proven-only differential run: corpus 4668 → 2289 instructions, runtests 3389 → 3071;
  zero refinement failures, pass errors or verifier rejections, and no worse file summaries.
  The optional `/tmp/rust-clif-survey` data was absent. The instruction-count increase from
  R0's 3010 runtest instructions comes with replacing division/remainder by multi-instruction
  sequences; it is not a measured latency result.
- Integration gates: full compiler build (1290 jobs) and crate-proofs build (958 jobs)
  completed successfully. All 13 audited root/aggregate/E2E/crate theorems use only permitted
  axioms. Encoding comparison: 1292/1292 identical functions, 54842 words and 1332 relocations.
  E2E lowering: 1150 accepted, zero rejected, 97 out of scope. Native filetests: corpus
  136 passed; runtests 4672 passed, zero failed and zero native disagreements (unsupported
  and out-of-scope cases remain reported separately).

**R8 (2026-10-09, `agent/extends-r8`, merged in [#206](https://github.com/eth-act/clifv/pull/206)):**
- `RuleExtends2.lean` proves roots 40, 42 and 44 with their original `RuleOk` statements
  and premises. Masked zero and signed re-extension normalize before graph construction.
  Early width specialization preserves the non-i128 facts needed by `fitsIn64_ofClif`.
  Specializing the condition code before evaluating its if-let preserves the state identity
  needed by the valuation chain; the existing graph-denotation and bitvector tactics finish.
- Concrete witnesses cover zero, signed extrema and all four signed conditions. The matched
  wide constant is non-i128, so the new roots cover the six widening pairs among i8/i16/i32/i64.
- CLI smoke: all three roots fire in 100 functions spanning all ten comparisons and widening
  pairs through i128 (the latter provides non-matching controls). All 700 executions agree,
  with zero unsupported inputs, ill-formed functions, pass errors or rule errors. Instructions
  fall from 340 to 268, versus 304 with the new roots disabled.
- The optimized smoke passes all 700 exact interpreter expectations, the Cranelift verifier
  accepts all 100 functions, and all 700 AArch64 executions agree with Cranelift-native.
- Full compiler and crate-proofs builds completed successfully (1291 and 958 jobs).
  All 11 audited helper/root/aggregate/E2E/crate theorems use only permitted axioms.
  Encoding comparison: 1292/1292 identical functions, 54842 words and 1332 relocations.
  E2E lowering: 1150 accepted, zero rejected, 97 out of scope. Native filetests: corpus
  136 passed; runtests 4672 passed, zero failed and zero native disagreements; unsupported
  and out-of-scope cases remain reported separately.
- Proven-only differential run: corpus 4668 → 2289 instructions, runtests 3389 → 3071.
  Zero refinement failures, pass errors or verifier rejections; all 445 file summaries are
  no worse than their unoptimized baselines. Existing interpreter/oracle expectation failures
  and unsupported cases remain reported, not counted as new regressions.
  The optional `/tmp/rust-clif-survey` data was absent.

**R7 (2026-10-09, `agent/bitops-r7`, merged in [#207](https://github.com/eth-act/clifv/pull/207)):**
- `RuleBitops9.lean` proves root 79 by relating the 64-bit immediate mask/complement guard
  to bit-vector complementation at i8/i16/i32/i64. The i128 case is excluded by the existing
  matcher, not by a new theorem premise.
- `RuleBitops10.lean` proves roots 157/170 with their original `RuleOk` statements. Its
  opcode-indexed `ofInst` inversion retains both binary and `iconcat` instructions, but
  resolves the opcode before splitting alternatives. The ordinary matcher then terminates
  without the former product of impossible branches. Immediate casts and intermediate
  shift results normalize before applying the two closed-width byte-swap identities.
- Concrete witnesses cover complement guards, both decoder alternatives, distinct bytes,
  high-bit boundaries and both word widths. The proof module builds with a 4M-heartbeat
  limit per root; all 450 bitops roots are now enabled.
- The 82-function CLI smoke includes wrong-mask and i128 controls. Roots 79/157/170 fire
  24/1/1 times; all 766 executions agree, with no unsupported inputs, ill-formed functions,
  pass errors or rule errors. Instructions fall from 392 to 250, versus 336 before enablement.
  All 766 optimized interpreter expectations pass, the Cranelift verifier accepts all 82
  functions, and all 766 AArch64 executions agree with Cranelift-native.
- Full compiler/crate builds completed successfully (1293/958 jobs). All 15 audited
  helper/root/aggregate/E2E/crate theorems use only permitted axioms. Encoding: 1292/1292
  identical functions, 54842 words and 1332 relocations. E2E: 1150 accepted, zero rejected,
  97 out of scope. Native filetests: corpus 136 passed; runtests 4672 passed, zero failed
  and zero native disagreements, with errors and not-compiled cases reported separately.
- Proven-only differential results: corpus 4668 → 2289 instructions; runtests 3389 → 3069
  (3071 before R7). No refinement failures, pass errors or verifier rejections; all 445
  file summaries are no worse than their unoptimized baselines. Existing interpreter/oracle
  expectation failures and unsupported cases remain reported. The optional survey was absent.

**R3 (2026-10-09, `agent/selects-r3`, merged in [#208](https://github.com/eth-act/clifv/pull/208)):**
- `RuleSelects9..12.lean` proves the remaining thirteen roots: comparison-to-one/zero,
  matching extension lifting, redundant OR operands, conditional subtraction and
  select-of-equality factoring. All 100 selects roots are enabled, without changing
  the original `RuleOk` statements or premises.
- Duplicate denotation facts are substituted before RHS type reads. Literal-match
  facts survive until constant normalization; symbolic select identities avoid
  unnecessary width enumeration. The comparison RHS resolves the typed constant
  constructor's optional if-let before the enclosing equality's `typeOf` reads.
- Concrete witnesses cover both condition outcomes, signed/high-bit values, equal-width
  semantic boundaries and strict widening guards. The CLI smoke covers all ten integer
  comparisons and widths through i128, with mixed-extension and mixed-source-width controls.
- All thirteen roots fire across 682 functions. All 4438 original/optimized interpreter
  expectations and AArch64/Cranelift-native comparisons agree, with no unsupported cases,
  ill-formed functions, pass errors or rule errors. The Cranelift verifier accepts all
  682 optimized functions. Instructions fall from 3146 to 1884, versus 3050 before enablement.
- Full compiler/crate builds completed successfully (1297/958 jobs). All 35 audited
  helper/root/witness/aggregate/E2E/crate theorems use only permitted axioms.
  Encoding: 1292/1292 identical functions, 54842 words and 1332 relocations.
  E2E: 1150 accepted, zero rejected, 97 out of scope. Native filetests: corpus 136 passed;
  runtests 4672 passed, zero failed and zero native disagreements; existing errors and
  not-compiled cases remain reported separately.
- Proven-only differential results: corpus 4668 → 2289 instructions; runtests 3389 → 3063
  (3069 before R3). No refinement failures, pass errors or verifier rejections; all 445
  file summaries are no worse than their unoptimized baselines. The existing runtest
  interpreter/oracle totals remain seven expectation failures, ten disagreements and
  two oracle errors. The optional survey was absent.

**R5 (2026-10-10, `agent/spaceship-r5`, merged in [#209](https://github.com/eth-act/clifv/pull/209)):**
- `RuleSpaceshipSelects.lean` proves all twenty remaining select roots, IDs 1379–1398,
  with unchanged `RuleOk` statements and premises. The spaceship family is complete at 40/40.
- `RuleSpaceshipUnsigned.lean` and `RuleSpaceshipSigned.lean` prove width-parametric
  three-way comparison identities by unsigned/signed order trichotomy.
  `RuleSpaceshipInfra.lean` proves each common RHS once, with direct subtraction/poison
  decoding and reuse of established `typeOf` equations. ISLE's comparison result type
  remains separate from the operands' actual width; the four negation forms return i8
  but accept operands of every integer width.
- Concrete witnesses cover less/equal/greater, signed extrema, high bits, zero-width
  semantic boundaries, widening and truncation. The CLI smoke covers input/output widths
  8–128 and distinct-operand controls. All twenty roots fire across 426 functions.
  All 4236 exact interpreter expectations and AArch64/Cranelift-native comparisons agree;
  no unsupported cases, ill-formed functions, pass errors or rule errors occur.
  The Cranelift verifier accepts all 426 optimized functions. Instructions fall from
  2682 to 1702, versus 2602 before enablement.
- Full compiler/crate builds completed successfully (1301/958 jobs). All 47 audited
  semantic-helper/RHS/root/aggregate/E2E/crate theorems use only permitted axioms.
  Encoding: 1292/1292 identical functions, 54842 words and 1332 relocations.
  E2E: 1150 accepted, zero rejected, 97 out of scope. Native filetests: corpus 136 passed;
  runtests 4672 passed, zero failed and zero native disagreements. Existing runtest
  errors (7) and not-compiled cases (9054) remain reported separately.
- Proven-only differential counts remain corpus 4668 → 2289 and runtests 3389 → 3063.
  No refinement failures, pass errors or verifier rejections; all 445 file summaries are
  no worse than their unoptimized baselines. Existing interpreter/oracle totals remain
  seven expectation failures, ten disagreements and two oracle errors. The optional survey
  was absent.

**R2 (2026-10-10, `agent/icmp-r2`, merged in [#210](https://github.com/eth-act/clifv/pull/210)):**
- `RuleIcmpIdentity`, `RuleIcmpBounds`, `RuleIcmpArithmetic`, `RuleIcmpSelects` and
  `RuleIcmpCompose` prove all fifteen remaining roots with their original statements
  and premises. The icmp family is complete at 124/124; total coverage is 1146/1193.
- Composition proofs separate exact interpreter evaluation from arithmetic.
  `RuleIcmpComposeEval` proves twenty fixed-code lookup facts and two generic dispatchers.
  `RuleIcmpComposeGuard` proves compatibility, including failed-guard state/trace rollback.
  `RuleIcmpComposeRhs` proves all eight relation masks with operand width independent of
  the i8 result. The root tactic holds only the outer composition function opaque while
  evaluating its arguments, then uses the typed RHS theorem. Predicate identities
  remain width-parametric. Neither the heartbeat limit nor the original fuel premise
  is increased.
- Every new theorem has a concrete non-vacuity witness. `RuleIcmpComposeWitness` supplies
  sixteen full-premise RHS fixtures, including actual interpreter success and result
  membership, over a genuine fresh-allocation graph with proved `GraphOk` and invariant.
  Signed/unsigned modes, high-bit ordering and equality/inequality are covered.
- CLI smoke: all fifteen roots fire across 1890 functions and widths 8–128, including
  every condition-code pair, incompatible-class and distinct-operand controls.
  All 15740 exact interpreter expectations, differential runs and AArch64/Cranelift-native
  comparisons agree, with no unsupported cases or pass/rule errors. The Cranelift verifier
  accepts all 1890 optimized functions. Instructions fall from 6597 to 3595, versus 6127
  before enablement.
- Full compiler/crate builds completed successfully (1310/958 jobs). All 66 audited
  helper/root/aggregate/E2E/crate theorems use only permitted axioms. Encoding:
  1292/1292 identical functions, 54842 words and 1332 relocations. E2E: 1150 accepted,
  zero rejected, 97 out of scope. Native filetests: corpus 136 passed; runtests 4672 passed,
  zero failed and zero native disagreements. Existing runtest errors (7) and not-compiled
  cases (9054) remain reported separately.
- Proven-only differential instructions improve to corpus 4668 → 2287 (matching all rules)
  and runtests 3389 → 3055, from 2289/3063 before R2. No refinement failures, pass errors
  or verifier rejections; all 445 file summaries are no worse than unoptimized baselines.
  Existing interpreter/oracle totals remain seven expectation failures, ten disagreements
  and two oracle errors. The optional survey was absent.

**R1 (2026-10-10, `agent/arithmetic-r1`, merged in [#211](https://github.com/eth-act/clifv/pull/211)):**
- `RuleArithMulHi`, `RuleArithOdd`, `RuleArithCancel` and `RuleArithProducts` prove
  all twenty-eight remaining roots with unchanged `RuleOk` statements and fuel premises.
  Arithmetic is complete at 258/258; total coverage is 1174/1193.
- `RuleArithMulHiSem` derives signed/unsigned high products from high-half extraction,
  without expanding multiplication. The root tactic splits only the matched extensions'
  output type before interpreting the half-width guard, rather than every operand type.
- `RuleArithOddSem` proves odd multiplication injective modulo powers of two and connects
  exact unsigned division to the signed Imm64 representation. The width bound comes from
  the original constant's presentation: `iconst.i128` is not presented. No new rule guard
  or premise is assumed. Pure guard results and their unchanged states are normalized
  before constructing the RHS.
- Product identities remain width-parametric, including signed minima and wrapping
  multiplication. Repeated-operand comparisons handle the i128 zero constructor.
  Every new theorem has a concrete non-vacuity witness.
- All twenty-eight roots fire across 610 functions and widths 8–128, including both
  comparison/multiplication orders, all max operand orders, distinct-operand controls,
  exact/inexact division, odd/even/zero multipliers, negative Imm64 values, and high-product
  width/shift controls. All 7124 exact interpreter expectations, differential runs and
  AArch64/Cranelift-native comparisons agree. All 610 optimized functions pass the
  Cranelift verifier. Instructions fall from 2430 to 1626, versus 2154 before enablement.
- Full compiler/crate builds completed successfully (1307/958 jobs). All 50 audited
  helper/root/aggregate/E2E/crate theorems use only permitted axioms. Encoding:
  1292/1292 identical functions, 54842 words and 1332 relocations. E2E: 1150 accepted,
  zero rejected, 97 out of scope. Native filetests: corpus 136 passed; runtests 4672 passed,
  zero failed and zero native disagreements. Existing runtest errors (7) and not-compiled
  cases (9054) remain separately reported.
- Proven-only differential instructions remain corpus 4668 → 2287 and improve runtests
  from 3055 to 3043 (3389 before optimization). All 445 file summaries are no worse;
  no refinement failures, pass/rule errors or verifier rejections. Existing interpreter
  totals remain seven expectation failures, ten disagreements and two oracle errors.
  The optional survey was absent.

**R4 (2026-10-10, `agent/shifts-r4`, merged in [#212](https://github.com/eth-act/clifv/pull/212)):**
- `RuleShiftsConst`, `RuleShiftsRotate` and `RuleShiftsDistribution` prove all seventeen
  sound remaining roots with unchanged `RuleOk` statements, guards and fuel.
  Shifts reach 73/75; total coverage is 1191/1193. False originals 84/88 stay disabled;
  the exported ISLE data is unchanged.
- `RuleShiftsConstSem` normalizes unsigned masking and wrapping addition to the exact
  sum of two reduced amounts. Symbolic right-shift composition and shift-to-zero
  identities cover both sides of the width guard, including i128 data and its
  extension-produced zero.
- `RuleShiftsRotateSem` proves rotation composition by bit indices. Every scalar data
  width divides the modulus of every scalar amount type: even an i8 amount may rotate
  i128 data. Wrapping amount addition/subtraction therefore preserves rotation modulo
  the data width; zero extension preserves the amount. Root tactics select the exact
  composition theorem and close impossible equal-type extension branches before
  arithmetic, avoiding speculative unification and variable-shift bit-blasting.
- Distribution315 is multiplication/subtraction modulo `2^width`. Every new
  helper and root has a concrete non-vacuity witness.
- All seventeen roots fire across 3990 functions and widths 8–128. The smoke includes
  independently typed constants, masked/high-bit counts, sums below/at/above width,
  every rotate orientation and constant position, equal/unequal dynamic amount types,
  wrapping addition, subtraction underflow, and shared/distinct SSA shift amounts.
  All 41430 exact interpreter expectations, differential runs and AArch64/Cranelift-native
  comparisons agree; all 3990 optimized functions pass the Cranelift verifier.
  Instructions fall from 13950 to 9629, versus 12766 before enablement. Proven-only
  statistics exactly match the full-rule diagnostic on this fixture.
- Full compiler/crate builds completed successfully (1312/958 jobs). All 40 audited
  helper/root/aggregate/E2E/crate theorems use only permitted axioms. Encoding:
  1292/1292 identical functions, 54842 words and 1332 relocations. E2E: 1150 accepted,
  zero rejected, 97 out of scope. Native filetests: corpus 136 passed; runtests 4672 passed,
  zero failed and zero native disagreements. Existing runtest errors (7) and not-compiled
  cases (9054) remain separately reported.
- Full proven-only differential counts remain corpus 4668 → 2287 and runtests
  3389 → 3043. All 445 file summaries are no worse; no refinement failures, pass/rule
  errors or verifier rejections. Existing interpreter totals remain seven expectation
  failures, ten disagreements and two oracle errors. The optional survey was absent.

**Proven rule lines** (`rule_<file>_<line>`, ISLE source lines):
- `arithmetic.isle` (258): 8, 13, 18, 24, 26, 28, 31, 35, 38, 42, 46, 50, 53, 59, 65, 69, 73, 75,
  173, 181, 200, 206, 226, 233, 236, 239, 240, 243, 244, 247, 251, 256, 261, 266, 273, 278, 283, 288,
  295, 296, 297, 298, 301, 302, 303, 304, 307,
  308, 311, 312, 313, 314, 317, 318, 319, 320, 323, 324, 327, 328, 329, 330, 333, 334, 337, 338,
  339, 340, 343, 346, 349, 352, 353, 354, 355, 356, 357, 358, 359, 362, 363, 364, 365, 366, 367,
  368, 369, 372, 373, 374, 375, 378, 379, 380, 381, 384, 385, 388, 389, 390, 391, 404, 405, 406,
  407, 410, 411, 414, 415, 418, 419, 420, 421, 424, 427, 428, 431, 432, 433, 434, 435, 436, 437, 438,
  441, 442, 443, 444, 445, 446, 447, 448, 451,
  452, 453, 454, 457, 458, 459, 460, 461, 462, 463, 464, 467, 468, 469, 470, 471, 472, 473, 474,
  477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 495, 496, 497,
  498, 500, 501, 502, 503, 505, 506, 507, 508, 510, 511, 512, 513, 515, 516, 517, 518, 520, 521,
  522, 523, 525, 526, 527, 528, 530, 531, 532, 533, 536, 537, 538, 539, 541, 542, 543, 544, 546,
  547, 548, 549, 551, 552, 553, 554, 556, 557, 558, 559, 561, 562, 563, 564, 566, 567, 568, 569,
  571, 572, 573, 574, 577, 578, 579, 580, 581, 582, 583, 584, 587, 590, 593, 596, 599, 603, 607,
  610, 611, 612, 615, 616, 617, 618, 619, 620, 621, 622.
- `cprop.isle` (68): 3, 9, 14, 20, 26, 56, 62, 68, 74, 79, 84, 89, 94, 99, 104, 109, 114, 119, 125,
  130, 132, 135, 147, 152, 155, 159, 162, 165, 169, 170, 171, 172, 174, 183, 193, 197, 201, 205,
  209, 214, 217, 220, 223, 227, 229, 232, 235, 238, 241, 247, 249, 252, 254, 257, 259, 269, 320,
  322, 324, 333, 337, 341, 345, 349, 375, 377, 379, 521.
- `icmp.isle` (124): 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 21, 23, 25, 27, 29, 31, 33, 35, 41, 43, 49, 63,
  70, 77, 84, 91, 96, 104, 108, 112, 116, 120, 125, 130, 135, 140, 145, 150, 155, 160, 165, 170, 175, 180, 184, 190, 193, 196, 199,
  202, 205, 254, 259, 264, 269, 274, 279, 284, 289, 295, 296, 299, 300, 303, 304, 306, 307, 310, 311, 312, 313,
  314, 315, 316, 317, 325, 329, 333, 337, 341, 345, 349, 353, 359, 362, 365, 368, 371, 374, 377,
  380, 386, 394, 402, 410, 438, 442, 447, 451, 479, 482, 485, 486, 489, 490, 491, 492, 495, 498, 501, 502, 505, 506,
  509, 510, 513, 514, 517, 520, 523, 526, 529, 532, 535.
- `selects.isle` (100): 4, 9, 15, 20, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 40, 41, 42, 43,
  81, 85, 91,
  95, 97, 98, 99, 100, 103, 109, 110, 113, 114, 115, 116, 117, 118, 119, 120, 124, 125, 126, 127,
  130, 131, 132, 133, 137, 138, 139, 140, 141, 142, 143, 144, 148, 149, 150, 151, 152, 153, 154,
  155, 159, 160, 161, 162, 163, 164, 165, 166, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179,
  180, 181, 182, 183, 184, 185, 188, 189, 193, 194, 195, 196, 199, 200, 201, 202, 205, 209, 213.
- `remat.isle` (12): 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26.
- `spaceship.isle` (40): 13, 19, 25, 32, 39, 46, 55, 59, 65, 69, 78, 84, 90, 97, 104,
  111, 120, 124, 130, 134, 146, 148, 151, 153, 157, 159, 162, 164, 167, 169, 172, 174,
  179, 181, 183, 185, 187, 189, 191, 193.
- `shifts.isle`, added by RulesRest: 41, 50, 61, 71, 152, 270, 280, 285.
- `shifts.isle`, added by R4: 161, 170, 184, 193, 239, 240, 241, 242, 244, 245,
  246, 247, 259, 261, 264, 266, 315.

**Template** (`RuleAuto.lean`): `rule_auto r` = `rule_intro` (fuel `k+1000`), `rule_no_iflets`,
`rule_lhs hG`, `rule_rhs`, `rule_finish`.
- `rule_lhs`: fixpoint of `lhs_step` (`simp_all` over `opt_match`/`opt_data`, wrapped in
  `opt_guard`, which turns the maximum-recursion failure `simp_all` hits on the contradictory
  hypotheses of dead branches into an ordinary failure), `opt_destruct` + `subst`, `opt_model hG`
  (model facts for `(node|type, class value)` pairs matched on the syntax of `(state, class)`:
  4× faster than trying every pair) and the fallback `lhs_step'` (`simp … at *`).
- `rule_rhs`: `opt_eval hev` (interpreter equations + `opt_monad` + `opt_imm`), then `split` on
  every stuck `match` (a made `icmp` reads its operand type from the graph: `toInst_icmp`,
  `none` = poison, no obligation), `opt_types` (the operand type read in a later state is the
  value's type, `GraphOk.typeOf_eq`).
- `rule_finish`: a matched class (`Valuation.Le` chain) or a made node (`GraphOk.make_val`,
  `opt_node` operand by operand, made operands recursively), then `rule_bits`: `val_congr`
  (not `simp`: `BitVec 8` vs `BitVec Ty.i8.width`), `ac_rfl` for AC identities (64-bit `*`
  commutation timed out in `bv_decide`), else `opt_cases_ty` (types and `IntCC`s),
  `opt_widths` (locals to literal widths), `sem_simp` (`bif` forms of `select`/`bmask`/`icmp`/
  min/max — an `if` would carry a stale `Decidable` instance; shifts as `<<< (y &&& (w-1))`,
  `ishl_mask` etc.), `kbv` (until T6 `bv_decide` with a 120 s SAT timeout). The context is never `simp_all`ed in `rule_bits`.
- Embedding lemmas added: `evalNode` of `select`/`bitselect`/`bmask`/`uextend`/`sextend`/
  `ireduce`; `ofInst` inversion of `icmp`/ternary; type predicates on `ofClif t` and forward
  `extractFn` lemmas (internal-constructor rule selection); `CTy.ofName?` matches `I8`..`I128`
  literally (behaviour-preserving) so `$I64` patterns reduce by `rfl`.

**Cost** (32 cores, `lake env lean` on one file): `cprop` 68 roots 3 m 18 s wall / 62 CPU-min;
`arithmetic` 258 roots 21 m wall. A passing rule costs 5-30 s (LHS unfolding dominates:
~1 s per `simp_all` pass, 5-10 passes for two-level patterns); failing rules cost most of the CPU
(then `bv_decide` timeouts, heartbeat limit). Use `maxHeartbeats 4000000` per declaration.

**Fan-out recipe** (one agent per opts file; ids come from `Isle.Opt.Closure.rules`, roots of
term 177 = `simplify`):
1. Generate `FV/Opt/Proof/Rule<File>.lean` with one `theorem ok_rule_<file>_<line> {p} (hd :
   Data p) : RuleOk p rule_<file>_<line> := by rule_auto rule_<file>_<line>` per root (header as
   `RuleCprop.lean`), run `FV_MEMCAP=16G scripts/memcap.sh lake env lean -DmaxErrors=100000
   <file>`, keep the theorems without errors.
2. For the failures, debug one rule with the phases spelled out (`rule_intro r; rule_no_iflets;
   rule_lhs hG; all_goals rule_rhs; trace_state`): a stuck `hev` names the missing evaluation
   lemma (helper spec → `RuleImm.lean` in the normal form above; extractor/type predicate →
   `RuleEmbed.lean`; `evalNode` form → `RuleNode.lean`); the goal a failing `kbv` (formerly
   `bv_decide`) reports names the missing `sem_simp` normal form.
3. Append the proven ids to `Opt.provenSimplifyRules` (`FV/Opt/RuleAllow.lean`, rule ids from
   `Closure.rules`) and import the new file in `RuleAll.lean`; nothing else in `RuleAll.lean`
   names rules (`allowed_ok%` fails with "`rule_X` is allow-listed but there is no theorem
   `ok_rule_X`" if an id has no proof). Shared files
   (`RuleAuto`, `RuleEmbed`, `RuleNode`, `RuleImm`) need one owner or serialized merges.

Historical gaps from the first fan-out (arithmetic 86, cprop 16 — both now complete; R0 closed items 2 and 3, R1 completes arithmetic guard/product proofs, and R9 completes item 5):
1. If-lets (`rule_no_iflets` only handles `[]`; 30+ arithmetic roots): evaluate `hil` like `hev`
   and split on the `Bool` condition — the right-hand side then runs under that fact.
2. Internal constructors with if-lets on the right (`iconst_u`/`iconst_s ty k` with `k ≠ 0`,
   `cmp_true`): same evaluation of the constructor's if-let (`u64_lt_eq c (ty_umax ty)`,
   `ty_umax` = `tyMask_ofClif`), then the `Int` immediate through `imm_solve`'s lemmas.
3. Missing helper specs: `imm64_sshr`, `imm64_rotl/rotr` (the `Nat` subtraction `b - s` as a
   `BitVec` amount), `u64_bswap16/32/64`, `imm64_power_of_two`, `u64_*` arithmetic.
4. `bv_decide` limits: 64-bit multiplication identities that are not AC (`x*(-1)`, `x*2`),
   `iabs` (needs `Sem.iabs` in `bif` form).
5. Skeleton rules: **complete**, all 37 roots proven and enabled, including signed `div_const`
   and leading/trailing-zero branch conditions ("Skeleton rules").
