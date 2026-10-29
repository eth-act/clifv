# Lean module system: prototype (parked)

Status: **parked** (2026-10-29). Branch `parithosh/module-system`, off main `22f3190e`, never to be
merged as is. The port is scripted (`scripts/module-port.py`) and can be regenerated on any main.
Measured in an Amp orb: 16 vCPU, 31 GiB RAM, no swap, Lean v4.34.1.

## Decision

A −12 % projected rebuild time for the lean-backend closure (best variant, below), after a full
day of work and with an un-expose fix loop that was not converging, does not justify a
4,700-file port now. Removing unused imports on main (no port) cuts 19 % of the dependency pairs
with none of the churn. Revisit under the conditions at the end.

## What was ported and what builds

* **Mechanical port, whole tree** (`scripts/module-port.py`): 4,624 files get `module`,
  `public import` for every import, and `@[expose] public section` (every declaration public,
  every definition body unfoldable, theorem proofs private). Generators emit the same form:
  `rust/crates/isle2lean` (FV/Isle/Generated), `FVTest/Backend/*Gen*.lean`,
  `FVTest/Backend/Proof/Probe/GenData.lean`, `FVTest/Opt/Proof/GenData.lean` (via
  `FVTest/ModuleHeader.lean`), `FVTest/Opt/Proof/gen_ctor.py` (output byte-identical to the
  checked-in `RuleCtor.lean`). Import parsers accept `import all`
  (`scripts/lake-serial-build.py`, `scripts/check-stock-mixed-integration.py`; `ci-build-plan.py`
  reuses the former). `lakefile.toml` sets `-Dbackward.privateInPublic=true`.
* **Builds:** the 429-module `lean-backend` closure (`FVTest.Backend.Main`) builds, with fix-ups,
  in two states: mechanical (`cbcb4cfc`) and with private imports (`fda50413`). The rest of the
  tree is mechanically ported but was never built clean (a whole-tree fix loop was started, then
  stopped to focus on the closure).
* **Private imports:** `lake shake --force` over the closure, applied by
  `scripts/module-port.py privatize`: 406 of the 895 local `public import`s became private
  (135 needed privately, 271 unused, kept as private imports so the graph is unchanged); shake
  also added 995 imports (things previously seen only through re-exports).
* **Same output:** `lean-backend` on all 42 `corpus/clif` files with `--regalloc lean` and
  `--regalloc spill` (84 objects) is byte-identical to the unported binary, for both states.
* **Axiom sets:** `collectAxioms` of every theorem in the closure (14,289 theorems,
  `scripts/module-system/axdump.lean`), unported vs mechanical port: identical, except that
  three auto-generated lemmas `Arm.ArmState.mk.inj`, `.injEq`, `.sizeOf_spec` no longer exist
  publicly (`ArmState` has private fields and had to leave the exposed section). No theorem gained
  an axiom; no `sorryAx`. `scripts/axiom-audit.py` was not run: its files import E2E modules
  outside the closure, which needs the whole tree built.
* **Un-exposed definitions (WIP, not building):** `public section` without the blanket
  `@[expose]`, re-exposing what fails, in the closure. Best state: 283 of 429 modules building.

## Fix-up categories (closure; files differing from the mechanical port at `fda50413`)

| kind | files | how found / fixed |
|---|---|---|
| imports (private imports step) | 302 | `lake shake`, scripted (`privatize`) |
| `meta` (elaboration-time code: `elab`/`macro` helpers, simprocs, tactic files as `public meta section`, `meta import` for `native_decide`/`#eval`) | 55 | error text names the declaration or import; `autofix.py` |
| `import all` of core (`Init.*`, `Std.*`) so `decide`/`rfl`/kernel reduction can unfold core definitions that core does not expose (`Array.qsort`, `Std.Range`, …) and of `FV.Arm.State` (private `ArmState.mk`) | 24 | `coreall.lean` computes the needed core modules from the unported build |
| sections / `@[expose]` structure (`ArmState` outside the exposed section; `deriving` cannot expose private fields) | 18 | by hand |
| proof / declaration edits | 33 (13 of them generator edits) | by hand: `IselCtlTbz`, `IselCovSound`, `RegLevelEmit` (two matchers no longer reduce each other: `generalize` / case on the list), `Arm.Insts.Common` (bit-mask functions split into `CommonBits` so its dsimprocs can `meta import` them), builtin simprocs in simp sets (`FV/SimprocAttr.lean`: core's builtin simprocs are not `meta`, so `attribute [s] Nat.reduceAdd` is rejected in a module) |

Un-expose added more categories: definitions unfolded by `simp [f]`/`unfold f`/`rw [f]` in other
modules (447, 225 of them found statically), kernel/`decide`/`rfl` reductions (351 directly plus
2,589 through the definitions they reach), `:= rfl` on exported theorems (term-mode `rfl`
elaborates in the public scope; `by rfl` does not), matcher renumbering (`gen_match_split …
.match_27` became `.match_29` because un-exposing changes which auxiliary matchers are
generated), derived `DecidableEq`/`BEq` instances (`@[expose] section` around the type), and
match exhaustiveness through un-exposed definitions. Log: `scripts/module-system/data/exposed-log.tsv`.

## Numbers

### Rebuild sets per commit (last 14 days of main, 347 commits)

Three counting methods give the two sets of numbers that were reported:

| method | median | p75 | max | > 2,000 |
|---|---|---|---|---|
| A: each commit on the import graph of its own time | 10 | 72 | 3,968 | 14 |
| B: changed files incl. added ones + importers, on today's graph | 116 | 303 | 4,406 | 25 |
| **C: as B, but an added file counts only itself** (it had no importers when added) | 30 | 164 | 4,397 | 23 |

B over-counts: importers of a file added by the commit were mostly written later. C is used below.

Projection, method C, whole tree (`project.py`; a module's public interface estimated
statically): unported sum 129,281 modules / 3,832,883 recorded CI seconds; mechanical port
128,126 / 3,828,520 (−0.1 %). No commit is proof-only; 456 of the 1,918 edits to existing modules
(24 %) keep the module's interface.

Projection, lean-backend closure (93 commits touch it):

| variant | median | p75 | sum (modules) | sum (CI s) |
|---|---|---|---|---|
| unported | 26 | 54 | 6,438 | 161,696 |
| mechanical port | 26 | 54 | 6,435 | 161,674 |
| + private imports | 26 | 49 | 6,048 (−6 %) | 153,939 (−4.8 %) |
| + private imports + un-exposed defs | 26 | 37 | 5,724 (−11 %) | 142,721 (−11.7 %) |

### Measured replays (closure built at main; edit applied; rebuild without the cache)

| edit | unported | mechanical | private imports |
|---|---|---|---|
| proof-only edit in `FV.Clif.Syntax` (300 importers in the closure) | 300 (cone) | **1 module, 21.9 s** | 1, 22.6 s |
| proof-only edit in `FV.Arm.State` (249) | 249 (cone) | 2, 24.3 s | 2, 24.5 s |
| proof-only edit in `FV.Backend.MInst` (267) | 267 (cone) | 1, 24.8 s | 1, 23.3 s |
| comment line in `FV.Clif.Syntax` | 300 (cone) | 1, 21.4 s | 1, 22.7 s |
| `424a2bac49` (reverted) | 3, 17.1 s | 3, 13.1 s | 3, 13.1 s |
| `fcdaefe001` (reverted) | 7, 14.8 s | 7, 12.7 s | 7, 12.7 s |
| `2dafec2e20` (reverted) | 113 (cone) | 113, 419 s | 113, 433 s (projected 37) |
| `f13c70a8b3` (reverted) | 85 (cone) | 84, 2,722 s (machine shared with the fix loop) | — (merge conflict) |

The first replay (`rp-test`, mechanical port, `FV.Clif.Syntax` proof edit) rebuilt 1 module in
24.6 s. Unported counts marked "cone" are the exact importer cones; their time is close to the
cold build. About 20 s of each small replay is the scheduler's batch checks.

### Why statement edits still rebuild everything on Lean v4.34.1

`2dafec2e20` rebuilt 113 modules instead of 37: `FV.Backend.Proof.LowerRename` imports the changed
`LowerSeq` *privately*, did not change, and still got a new public `.olean`. The difference is the
`sineQueNon` entry (library-suggestion trigger weights): Lean v4.34.1 computes it at export time
from symbol frequencies over **all** imports, so any theorem-statement change upstream changes
the public `.olean` of every downstream module whose theorem statements share a symbol, and Lake
rebuilds their importers. Proof-only edits do not change the frequencies, hence the 1-module
replays. Lean fixed this in leanprover/lean4#15159 (2026-09-15, in **v4.35.0**): the index is
computed on demand and no longer stored in `.olean` files. Not measured here on v4.35.0.

### Cold build and memory

Unported lean-backend closure, cold (`lake-serial-build.py --budget 26G --max-jobs 8`): 3,281 s
wall + 79 s to link `lean-backend`; 427 modules, 6,663 module-seconds; largest module
`RegallocAtomic` 2,071 s, 8.1 GB cgroup peak; machine peak 13.6 GiB. The ported cold build was
not measured cleanly (cancelled); in the fix runs `RegallocAtomic` took 2,291 s at 8.0 GB, and
with un-exposed definitions `LoopRun` needed more than 8 GB (0.6 GB unported). The whole-tree cold
baseline was started and aborted.

## Why un-exposing does not converge

* Each round re-exposes definitions in base modules (`FV.Isle.Syntax`, `FV.Backend.MInst`,
  `FV.Backend.Isel`, `FV.Arm.State`), which rebuilds most of the closure (`RegallocAtomic` alone is
  35 min), so a round takes 45–90 min; 13 rounds left 146 modules failing.
* Errors name the stuck term, not the definition to expose: `decide`/`rfl`/kernel failures need
  the transitive closure of definitions a reduction passes through (2,589 of the ~3,900
  exposures), found by heuristics that over-expose (wrong same-named definitions, whole closures).
* The fallback `import all` in the consumer makes `simp`/`whnf` time out (`CSemRename`); auxiliary
  matchers are renumbered; `LoopRun` grew past 8 GB.
* What survives is the projected −11.7 % above; on v4.34.1 the measured gain for statement edits is
  nil anyway (previous section).

## Reproducing / resuming

* `scripts/module-port.py` — mechanical port (`--check`), `regen OLD_MAIN OLD_PORT` (port a new
  main, merge the branch's fix-ups 3-way; on origin/main `c533c22a`: 30 s, 4,674 files, fix-ups
  merged into 449 files, 6 conflicts kept as the mechanical port; not built), `privatize`
  (`lake shake` → private imports), `unexpose`, `list-exposed` / `apply-exposed`.
* `scripts/module-system/`: the fix loop and measurement scripts as used in the orb (paths under
  `/home/user/ms` and `/home/user/workspace/*` are hard-coded): `driver.py` (build, fix, repeat),
  `autofix.py` (`meta`, `meta import`, `:= rfl` → `:= by rfl`), `coreall.lean` + `addall.py`
  (`import all` of core), `metamirror.py`, `expose.py` / `preexpose.py` / `declidx.lean` /
  `defdeps.lean` (un-expose), `replay.py` / `state.py` (measured replays), `analyze.py` /
  `project.py` (method C projections), `axdump.lean` (axiom sets), `classify.py`.
  Data in `scripts/module-system/data/`.
* Commits: `cbcb4cfc` mechanical port + fix-ups (closure builds), `fda50413` + private imports
  (closure builds), later commits: un-expose WIP (does not build).

## When to revisit

* After moving to Lean ≥ v4.35.0 (no import-dependent library-suggestion data in `.olean`s):
  re-measure `2dafec2e20` and a few statement edits; the private-imports projection (−6 %
  modules) becomes reachable, and proof-only edits already rebuild 1 module instead of the cone.
* After the unused-imports cleanup and the chain restructuring on main: smaller cones leave less
  for the module system to save, but a cleaner graph also makes `lake shake` and private imports
  cheap to keep.
* Port incrementally rather than in one cutover: a non-module file may import modules (it sees
  their private parts), so a closure such as lean-backend can be ported alone, the rest left as
  is. Keep blanket `@[expose]`; un-exposing is the expensive, non-converging part.
* Rules contributors would need: `meta` on anything run at elaboration time (Lean's error names
  it), `import all` for proofs that reduce non-exposed definitions, `public import` only when a
  public statement needs it (`lake shake` in CI can check this).
