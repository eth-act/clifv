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

- [x] Passes (`FV/Opt/*.lean`), all **unproven** (working first, proofs after, as for the
  backend): well-formedness check, unreachable-block removal, rule-based simplification of pure
  nodes and of skeleton instructions (Cranelift's rules via the ISLE interpreter), GVN, DCE,
  LICM. No `sorry`, no axioms (there are no theorems yet).
- [x] Drivers: `clif-opt` (optimised CLIF out; accepted by `clif-oracle check`), `--opt` for
  `lean-backend`, `lean-backend-armrun`, `lean-e2e-check`, `scripts/lean-backend-filetests.sh`.
- [x] Differential tests: `scripts/opt-difftest.sh` (corpus, runtests, cg_clif survey),
  `opt-fuzz` (random functions); backend with `--opt`: corpus 114/114 (+22/22 extrt), runtests
  3270/0/0, `lean-e2e-check --opt` 934/934 accepted and `formsCoveredB`-covered.
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
  1055 `simplify` roots, 29 `simplify_skeleton` roots and their helpers are proven (see "Rule
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
- Proven: the rule interpreter's soundness, 1055 `simplify` roots and 29 `simplify_skeleton`
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
`Quot.sound`, plus for `E2E.backend_correct_opt` the `bv_decide`/`native_decide` trust axioms
inherited from `backend_correct_final`):

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
the axiom set of `backend_correct_opt` (`propext`, `Classical.choice`, `Quot.sound` and the
backend's `bv_decide` trust axioms); `simpOk_sim`, `simplify_facts`, `simplifyPassSim`,
`optimize_sim_proven`: `propext`, `Classical.choice`, `Quot.sound`.

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
made nodes only over *known* values (graph nodes or available values; else a fresh dummy
value), made nodes that are not well-typed over solid values are recorded as `partialVals`
and not simplified (no e-class recorded), top-level statements enter the graph only if new,
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

Build note: `FV/Opt/Proof/RuleImm.lean` imports `FV.Backend.Proof.IselCmpExt` so that both
`bv_decide` users share one generated `Clif.Ty.enumToBitVec` (otherwise no module can import the
rule proofs and the backend together).

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

Status: the framework is complete and proven; **1055 `simplify` roots proven** (see below),
allow-list embedding done. Files `FV/Opt/Proof/{Sem,InterpMatch,InterpState,InterpEval,RuleBase,
RuleData,RuleNode,RuleEmbed,RuleTactic,RuleImm,RuleCtor,RuleSkel,RuleAuto,RuleArith,RuleCprop,
RuleAll}.lean`; generator
`FVTest/Opt/Proof/GenData.lean` (`lake env lean --run FVTest/Opt/Proof/GenData.lean >
FV/Opt/Proof/RuleData.lean`, 33 s build). No `sorry`; axioms of every theorem below:
`propext`, `Classical.choice`, `Quot.sound`, plus the `*._native.bv_decide.ax_*` certificates of
the `bv_decide` calls (as in the backend proofs); `RuleAll` uses no `native_decide`. Full build of
the rule modules: see the build note under "Proven rules" (`RuleArith.lean` dominates).

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

**Proven rules** (MidRulesInfra2, RulesBitops, RulesIcmpSel, RuleAllScale, RulesShiftsExt, RulesRest, R0): **1055 `simplify` roots** = `Opt.provenSimplifyRules` —
`arithmetic.isle` 230 of 258 (`RuleArith.lean`, `RuleArith2..8.lean`), `cprop.isle` 68 of 68 (`RuleCprop.lean`, `RuleCprop2..4.lean`), `remat.isle` 12 of 12 (`RuleRemat.lean`),
`bitops.isle` 447 of 450 (`RuleBitops1..8.lean`, tactics/lemmas in `RuleBitopsEmbed.lean`:
`rule_auto` 393, `rule_auto_b` 18, `rule_auto_i` 2, `rule_auto_z` 31; R0: `rule_auto_t`/`_tt` 3). **29 `simplify_skeleton` roots**
(`Opt.provenSkeletonRules`, `RuleSkeleton.lean`, `RuleSkeleton2..4.lean`, see "Skeleton rules" below).
`icmp.isle` 109 of 124 (`RuleIcmp1..10.lean`, `RuleIcmp12.lean`, `RuleIcmp13.lean`) and `selects.isle` 87 of 100 (`RuleSelects1..8.lean`),
with the template variants of `RuleIcmpEmbed.lean` (`rule_auto_c`/`_ci`: `arr_step` for a value
variable bound twice, `opt_split_typeof` for a made `icmp` under `subsume`; `_d`/`_di`: `Int`
literals of if-lets reduced, `ty_smin`/`ty_smax` specs passed as extra lemmas) and
`RuleIcmpEmbed2.lean` (`extractMulti_uem`: the `uextend_maybe` multi-extractor; `_e`/`_ei`:
signed immediates as sign-bit facts; `_f`/`_fi`/`_fz`/`_fiz`: the left-hand side without
`simp_all`, which rewrites a literal-match fact such as `asU64 imm = 0` away with a copy of itself;
`_g`: `_f` plus the `P s0`-guarded model facts and `opt_den_merge`). Each theorem names the
`first` chain it was checked with.
`extends.isle` 26 of 29 (`RuleExtends.lean`), `shifts.isle` 56 of 75 (`RuleShifts1..5.lean`), `spaceship.isle` 20 of 40 (`RuleSpaceship.lean`), with the templates of
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
  `bv_decide`), `rule_auto_tv`; `imm64Neg_ofInt` (`imm64_neg` of any immediate, for the sign-cast
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
  (bh ++ bl)`, by `bv_decide` on 64-bit halves) closes the 128-bit comparisons, and
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
  with the exponent as a `BitVec` (`bv_decide` per width), templates `pow2_auto_simp`,
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
`Classical.choice` and `Quot.sound`. The four signed `div_const` rule applications remain
disabled, as listed under "Skeleton rules".

**False under the CLIF semantics (findings):** `shifts.isle` 84 and 88 (`sshr`/`ushr (ishl x k) k` to
`s/uextend ty (ireduce ty_small x)`): `u64_wrapping_sub (ty_bits ty) shift_u64` wraps for shift
constants above the type width, e.g. `ishl.i8 x, v` / `sshr.i8 _, v` with `v = iconst.i64 -8`
(or `-24`; `i16` with `-16`): `ty_small` becomes `i16`/`i32`, wider than `ty`, so the rule builds
`ireduce.i16` of an `i8` value and `sextend.i8` of it — ill-typed IR with no value, while the
original is `x` (shift amount `-8 mod 8 = 0`). The proof fails exactly in these cases.
Not proven after RulesRest (proof-tooling limits unless stated; R0 proved 38, 42, 46, 50, 181, 333,
334, 343, 349, 587, 590, 593, 596, 603 and all of `cprop.isle`, see above): `arithmetic.isle` 200,
206 (heartbeat timeout), 251–288 (the 8 `eq`/`ne` of `imul` by an odd constant: timeout), 410–421,
427, 428 (`icmp` of `isub`/`iadd` with a variable bound twice: `simp` type mismatch at the icmp
result width with every template), 615–622 (64-bit products: SAT timeout); `icmp.isle` 196, 199,
202 are now proven (`rule_auto_v`). Skeleton rules: see "Skeleton rules" below.
Still not proven from the RulesShiftsExt list: `extends.isle` 40, 42, 44 (`eq`/`ne`/signed
`icmp` of a `sextend` against `iconst_s 0`: timeout also at 16M heartbeats); `shifts.isle` 161
(killed after 5 min at 16M, twice), 170 (maximum recursion depth), 184, 193 (unsolved goals), 239–242,
244–247, 259, 261, 264, 266 (rotate regrouping through `iadd_uextend`/`isub_uextend`: `rule_auto_w`
now evaluates the right-hand side and closes most type combinations; about 50 of the 125 per-type
goals still fail — `bv_decide` timeouts on 128-bit rotations and nested made operands left
unreduced), 315 (SAT timeout); `spaceship.isle` 13–137 (the 20 `select` rules: the right-hand
side's two made `icmp`s under `sextend_maybe` blow up the term; >10 min per rule even with eager
`typeOf` splitting). Proven by RulesRest: `shifts.isle` 41, 50, 61, 71, 152, 270, 280, 285.
Not proven (proof-tooling limits; none is false under the CLIF semantics): `selects.isle` 15 (`select(icmp, 1, 0)` to `uextend_maybe`: its `simp_all`-free proof passed
once and then failed deterministically in the full build; left out), 81, 85 (`select` of two `uextend`/`sextend`s with `value_type`: heartbeat timeout at
4M), 188, 189, 193–196, 199–202 (literal-match facts lost under `simp_all`, and the
`simp_all`-free variants exceed 12G / 50 min per rule); 97–100 are proven by R0.
Removed from the icmp/selects modules (RuleAllScale, 2026-10-01) because the modules ran out of
memory: `icmp.isle` 63, 70, 160, 175, 254–289, 365, 368, `selects.isle` 20 — all proven again by
R0 in their own modules at ≤ 5.3G (see above). Still
failing — `icmp.isle` 49, 77, 91 (`GraphOk.make_val` does not unify with the goal), 155, 165,
170 (`bv_decide` counterexample after the earlier alternatives time out), 180, 184, 386, 394, 402,
410 (heartbeat timeouts), 205 (`simp` made no progress), 295, 296 (no hypothesis in the
`bv_decide` fragment).
Not proven in `bitops.isle` (proof-tooling limits; none is false under the CLIF semantics): rule 79
(`or(and(x, k), z)` mask condition: needs 64-bit and/not immediate specs), 157 and 170 (32/64-bit
byte-swap patterns: time out at 12–20M heartbeats); 126/127/129 (`truthy` in an if-let) are proven
by R0. Build note: changing
`FV/Opt/Rules.lean` (or anything under `RuleBase`) rebuilds every rule module; the allow-list lives
in `FV/Opt/RuleAllow.lean`, which no rule module imports, so extending it rebuilds only
`Optimize`, `RuleAll` and their dependents. Build the rule modules one at a time (`lake build
FV.Opt.Proof.RuleArith`, …, `RuleSelects6`; `LEAN_NUM_THREADS=2`, 16G cap; 2026-10-01: `RuleArith`
14 min / 15.4G, `RuleBitops1..7` 1–11 min / 3–11.7G, `RuleCprop` 3 min / 7.4G, icmp/selects
modules 0.3–5 min / ≤5.2G; 2026-10-07, R0 modules: `RuleCprop3` 5 min / 11.4G, `RuleSkeleton3`
13.5 min / 7.6G, `RuleSkeleton4` 6 min / 6.6G, `RuleSkeleton2` 4.3 min / 3.6G, `RuleIcmp12`/`13`
3 min / 5.3G, the others < 2.5 min / ≤ 4.6G), then `RuleAll`/`FV.E2E.OptProven` (parallel builds of the rule modules
OOM). Check the log for "Build completed successfully": `memcap.sh` under `/usr/bin/time` can
report rc=0 for an OOM-killed build. `RuleAll` itself: 16 s, 3.6G (`LEAN_NUM_THREADS=1`; kernel
check of the `allowed_ok%` term, ~0.3 s to build it). Its previous form (`rfl` on the
`List.filter` of the 1281 `simplify` rules by `provenSimplifyRules.contains`, elaborated by
`Meta.isDefEq`, then an `AllOk` conjunction) cost 74 s, 11.4G at the same 842 rules (33 s elaborator `rfl`, 40 s kernel); the 32G OOMs
seen when building `RuleAll` at 872 rules came from the icmp/selects modules it imports.
Helper specifications (`RuleImm.lean`, simp set `opt_imm`): `imm64_add/sub/mul/and/or/xor/not/neg/
umin/umax/smin/smax/icmp/masked/clz/ctz/shl/ushr` at every non-`i128` type, in the normal form
`Rust.imm64X (ofClif t) (imm64OfBits b) … = .ok (imm64OfBits (<BitVec op> b …))` (proof: `imm_pre`
unfolds the helper, `imm_cases` splits the widths, `imm_solve` turns `Int` arithmetic into
`BitVec 64` and runs `bv_decide`; `clz`/`ctz` bridge `Nat.log2`/the Rust loop to `BitVec.clz`/`ctz`).

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
*Proven* (29): `arithmetic.isle` 79, 80, 130, 131, 132, and by R0 83, 87, 102, 135, 142
(power-of-two `div`/`rem`), 114, 117, 157, 160 (unsigned `div_const`); `cprop.isle` 32, 38, 44,
50; `skeleton.isle` 7, 9, 22, 26, 33, 37, 44, 50, 53, 56, and by R0 80. *Not proven* (proof
effort; none is known to be false): `arithmetic.isle` 122, 125, 165, 168 (signed `div_const`:
the magic numbers are proven, `magicS_spec`; the rule wiring — the `iconst_s` range checks of the
made constants, a `magicS` wrapper taking the rule's facts, and the `smulhi`/`sshr`/`sdiv`/`srem`
`toInt` finish — is not), `icmp.isle` 461, 466, 471, 475 (the `i128` cases of the made
`iconst_u`/`band` blow up the term).
These rewrites replace one instruction by several, so they do not lower the instruction counts.

**Proven rule lines** (`rule_<file>_<line>`, ISLE source lines):
- `arithmetic.isle` (230): 8, 13, 18, 24, 26, 28, 31, 35, 38, 42, 46, 50, 53, 59, 65, 69, 73, 75,
  173, 181, 226, 233, 236, 239, 240, 243, 244, 247, 295, 296, 297, 298, 301, 302, 303, 304, 307,
  308, 311, 312, 313, 314, 317, 318, 319, 320, 323, 324, 327, 328, 329, 330, 333, 334, 337, 338,
  339, 340, 343, 346, 349, 352, 353, 354, 355, 356, 357, 358, 359, 362, 363, 364, 365, 366, 367,
  368, 369, 372, 373, 374, 375, 378, 379, 380, 381, 384, 385, 388, 389, 390, 391, 404, 405, 406,
  407, 424, 431, 432, 433, 434, 435, 436, 437, 438, 441, 442, 443, 444, 445, 446, 447, 448, 451,
  452, 453, 454, 457, 458, 459, 460, 461, 462, 463, 464, 467, 468, 469, 470, 471, 472, 473, 474,
  477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 495, 496, 497,
  498, 500, 501, 502, 503, 505, 506, 507, 508, 510, 511, 512, 513, 515, 516, 517, 518, 520, 521,
  522, 523, 525, 526, 527, 528, 530, 531, 532, 533, 536, 537, 538, 539, 541, 542, 543, 544, 546,
  547, 548, 549, 551, 552, 553, 554, 556, 557, 558, 559, 561, 562, 563, 564, 566, 567, 568, 569,
  571, 572, 573, 574, 577, 578, 579, 580, 581, 582, 583, 584, 587, 590, 593, 596, 599, 603, 607,
  610, 611, 612.
- `cprop.isle` (68): 3, 9, 14, 20, 26, 56, 62, 68, 74, 79, 84, 89, 94, 99, 104, 109, 114, 119, 125,
  130, 132, 135, 147, 152, 155, 159, 162, 165, 169, 170, 171, 172, 174, 183, 193, 197, 201, 205,
  209, 214, 217, 220, 223, 227, 229, 232, 235, 238, 241, 247, 249, 252, 254, 257, 259, 269, 320,
  322, 324, 333, 337, 341, 345, 349, 375, 377, 379, 521.
- `icmp.isle` (109): 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 21, 23, 25, 27, 29, 31, 33, 35, 41, 43, 63,
  70, 84, 96, 104, 108, 112, 116, 120, 125, 130, 135, 140, 145, 150, 160, 175, 190, 193, 196, 199,
  202, 254, 259, 264, 269, 274, 279, 284, 289, 299, 300, 303, 304, 306, 307, 310, 311, 312, 313,
  314, 315, 316, 317, 325, 329, 333, 337, 341, 345, 349, 353, 359, 362, 365, 368, 371, 374, 377,
  380, 438, 442, 447, 451, 479, 482, 485, 486, 489, 490, 491, 492, 495, 498, 501, 502, 505, 506,
  509, 510, 513, 514, 517, 520, 523, 526, 529, 532, 535.
- `selects.isle` (87): 4, 9, 20, 26, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 40, 41, 42, 43, 91,
  95, 97, 98, 99, 100, 103, 109, 110, 113, 114, 115, 116, 117, 118, 119, 120, 124, 125, 126, 127,
  130, 131, 132, 133, 137, 138, 139, 140, 141, 142, 143, 144, 148, 149, 150, 151, 152, 153, 154,
  155, 159, 160, 161, 162, 163, 164, 165, 166, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179,
  180, 181, 182, 183, 184, 185, 205, 209, 213.
- `remat.isle` (12): 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26.
- `shifts.isle`, added by RulesRest: 41, 50, 61, 71, 152, 270, 280, 285.
- Not proven in `arithmetic.isle`: the 28 roots listed under "Not proven after RulesRest" that R0
  did not prove.

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
  commutation times out in `bv_decide`), else `opt_cases_ty` (types and `IntCC`s),
  `opt_widths` (locals to literal widths), `sem_simp` (`bif` forms of `select`/`bmask`/`icmp`/
  min/max — an `if` would carry a stale `Decidable` instance; shifts as `<<< (y &&& (w-1))`,
  `ishl_mask` etc.), `bv_decide`. The context is never `simp_all`ed in `rule_bits`.
- Embedding lemmas added: `evalNode` of `select`/`bitselect`/`bmask`/`uextend`/`sextend`/
  `ireduce`; `ofInst` inversion of `icmp`/ternary; type predicates on `ofClif t` and forward
  `extractFn` lemmas (internal-constructor rule selection); `CTy.ofName?` matches `I8`..`I128`
  literally (behaviour-preserving) so `$I64` patterns reduce by `rfl`.

**Cost** (32 cores, `lake env lean` on one file): `cprop` 68 roots 3 m 18 s wall / 62 CPU-min;
`arithmetic` 258 roots 21 m wall. A passing rule costs 5-30 s (LHS unfolding dominates:
~1 s per `simp_all` pass, 5-10 passes for two-level patterns); failing rules cost most of the CPU
(`bv_decide` timeouts, heartbeat limit). Use `maxHeartbeats 4000000` per declaration.

**Fan-out recipe** (one agent per opts file; ids come from `Isle.Opt.Closure.rules`, roots of
term 177 = `simplify`):
1. Generate `FV/Opt/Proof/Rule<File>.lean` with one `theorem ok_rule_<file>_<line> {p} (hd :
   Data p) : RuleOk p rule_<file>_<line> := by rule_auto rule_<file>_<line>` per root (header as
   `RuleCprop.lean`), run `FV_MEMCAP=16G scripts/memcap.sh lake env lean -DmaxErrors=100000
   <file>`, keep the theorems without errors.
2. For the failures, debug one rule with the phases spelled out (`rule_intro r; rule_no_iflets;
   rule_lhs hG; all_goals rule_rhs; trace_state`): a stuck `hev` names the missing evaluation
   lemma (helper spec → `RuleImm.lean` in the normal form above; extractor/type predicate →
   `RuleEmbed.lean`; `evalNode` form → `RuleNode.lean`); a failing `bv_decide` names the
   missing `sem_simp` normal form.
3. Append the proven ids to `Opt.provenSimplifyRules` (`FV/Opt/RuleAllow.lean`, rule ids from
   `Closure.rules`) and import the new file in `RuleAll.lean`; nothing else in `RuleAll.lean`
   names rules (`allowed_ok%` fails with "`rule_X` is allow-listed but there is no theorem
   `ok_rule_X`" if an id has no proof). Shared files
   (`RuleAuto`, `RuleEmbed`, `RuleNode`, `RuleImm`) need one owner or serialized merges.

Known gaps, by frequency in the failed roots (as of the first fan-out; arithmetic 86, cprop 16 — now 28 and 0, see above; R0 closed items 2 and 3, item 4 for `iabs` and products of negations, and item 5 except the signed `div_const` wiring):
1. If-lets (`rule_no_iflets` only handles `[]`; 30+ arithmetic roots): evaluate `hil` like `hev`
   and split on the `Bool` condition — the right-hand side then runs under that fact.
2. Internal constructors with if-lets on the right (`iconst_u`/`iconst_s ty k` with `k ≠ 0`,
   `cmp_true`): same evaluation of the constructor's if-let (`u64_lt_eq c (ty_umax ty)`,
   `ty_umax` = `tyMask_ofClif`), then the `Int` immediate through `imm_solve`'s lemmas.
3. Missing helper specs: `imm64_sshr`, `imm64_rotl/rotr` (the `Nat` subtraction `b - s` as a
   `BitVec` amount), `u64_bswap16/32/64`, `imm64_power_of_two`, `u64_*` arithmetic.
4. `bv_decide` limits: 64-bit multiplication identities that are not AC (`x*(-1)`, `x*2`),
   `iabs` (needs `Sem.iabs` in `bif` form).
5. Skeleton rules: 29 proven ("Skeleton rules"); `magicU_spec`/`magicS_spec` are proven, the signed
   `div_const` rules (`arithmetic.isle` 122, 125, 165, 168) are not wired yet.
