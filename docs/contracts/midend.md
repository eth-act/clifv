# Lean mid-end (`FV/Opt`), M7

`Opt.optimize : Clif.Function → Clif.Function` (and `Opt.optimizeProgram`) is the FV
compiler's CLIF → CLIF optimiser (PLAN.md §4 M7, "Lean mid-end"). It runs Cranelift 0.136.1's
own `simplify` / `simplify_skeleton` rules (exported as data, `docs/contracts/isle.md` "Mid-end
export") inside a small, separately provable pipeline of passes. Correctness criterion:
`Clif.run` refinement — whenever the input returns (values) or traps (code), the output does
the same; stuck or out-of-fuel input runs carry no obligation.

## Status

- [x] Passes (`FV/Opt/*.lean`), all **unproven** (working first, proofs after, as for the
  backend): well-formedness check, unreachable-block removal, rule-based simplification of pure
  nodes and of skeleton instructions (Cranelift's rules via the ISLE interpreter), GVN, DCE,
  LICM. No `sorry`, no axioms (there are no theorems yet).
- [x] Drivers: `clif-opt` (optimised CLIF out; accepted by `clif-oracle check`), `--opt` for
  `lean-backend`, `lean-backend-armrun`, `lean-e2e-check`, `scripts/lean-backend-filetests.sh`.
- [x] Differential tests: `scripts/opt-difftest.sh` (corpus, runtests, cg_clif survey),
  `opt-fuzz` (random functions); backend with `--opt`: corpus 114/114 (+22/22 extrt), runtests
  3270/0/0, `lean-e2e-check --opt` 914/914 accepted and `formsCoveredB`-covered.
- [x] Metrics (`scripts/lean-backend-metrics.sh`): Lean no-opt / `--opt` vs Cranelift
  `opt_level=none` / `speed` ("Results").
- [ ] Proofs: architecture below ("Planned proof architecture").

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
  Nothing about the rules or helpers is proven yet.

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
| cg_clif survey, all `*.unopt.reader.clif` (no run lines) | 2 326 | — | 116 713 → 67 268 | 30 files, 0 rejected |
| `opt-fuzz`, seeds 1–4, 11, 12, 21, 22 (±`--ext`, `--opt-remat-const`) | 2 850 | 22 800 / 0 / 0 | — | seeds 21, 22 files: ok |

No function was ill-formed and no pass ever produced an ill-formed function. The optimised
corpus and runtests files also meet their run lines under the Cranelift interpreter wherever
the originals do (one file improves: `div-checks` agrees more often after constant folding
avoids a known interpreter deviation).

**Backend with `--opt`** (`scripts/lean-backend-filetests.sh --opt`, native under qemu vs
Cranelift-native): corpus 114/114, extrt 22/22, runtests **3 270** pass / 0 fail / 0 disagree
(3 085 without `--opt`: rewrites turn 17 functions with `i128` shift amounts —
`iconcat`/`ireduce` of the amount — into E functions); `opt-fuzz --seed 21` file: 1 166/1 166.
`lean-e2e-check --opt`: `lowerCheck` and `prepCheck` accept 914/914, `formsCoveredB` 914
covered / 0 not covered — the optimised code uses no instruction form outside the proven set.

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
   the LHS, per type `i8`..`i64`; the proofs split on the type and close with `bv_decide`, like
   the isel proofs (`docs/contracts/backend-proof.md`), with the Lean transcriptions of the
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
   stays a per-function decided premise (`formsCoveredB` of the optimised code, 914/914 now).
   The result: for `check`ed in-subset `f`, whenever `Clif.run p` returns or traps, the Arm run
   of the compiled `opt f` does the same.
6. **Optional M3b** (PLAN): with the same rules, the Lean- and Cranelift-optimised CLIF can be
   compared function by function; not attempted.

## Gaps

- Nothing is proven yet (rules, interpreter, passes, pipeline); the differential tests are the
  only evidence.
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
