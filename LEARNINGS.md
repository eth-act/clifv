# Learnings

Tricks that made clifv's Lean proofs and builds faster, lighter or more robust, with the measured effect.
Add an entry when a change you made shows a measurable gain (or a measurable regression worth avoiding).
Keep each entry short: the problem, the trick, the numbers, where it is used.

None of these weaken what is proven: every compiler theorem still prints only `propext`,
`Classical.choice` and `Quot.sound`, and the kernel checks every proof.

## Kernel evaluation (`decide +kernel`, `rfl`)

### Scan Lists, not Arrays, in kernel-evaluated code
- **Problem:** `Array` combinators (`find?`, `foldl`, …) are well-founded recursive. The kernel evaluates them very slowly. Every Stock module that runs `Stock.lower` under `decide +kernel` looked up `"lower"` in the 2,483-term ISLE program with `Array.find?`.
- **Trick:** define the lookup as a `List` scan and add an `@[csimp]` theorem that swaps the `Array` version back in for compiled code, so runtime is unchanged.
- **Effect:** a 700-element scan went from 4.3 GB / 17–30 s to 0.48 GB / 0.25 s; `program.termByName? "lower"` from 4.65 GB / 17 s to 0.79 GB / 2.6 s (BuildDiet, `FV/Isle/Syntax.lean`; branch `agent/build-diet`, being merged).

### Prefer structural recursion to well-founded recursion
- **Problem:** the kernel cannot reduce well-founded definitions efficiently (or at all, in practice). `fitsCl`/`fitsTy` in `DefGenDom` used well-founded recursion, and every `decide +kernel` check over them failed.
- **Trick:** rewrite them with structural recursion (fuel or the list itself), with the same equations.
- **Effect:** the failing `DefGen` certificates now pass (T6).

### Avoid `rfl`-based simp steps on big concrete terms
- **Problem:** `StockCmpWithFlags` elaborated in 1.9 GB, but the kernel needed 23 GB to re-check one `simp` step of `isel_eval`: monad-law lemmas proved by `rfl`, applied to a large concrete state.
- **Trick:** use copies of the monad laws proved by `rw` instead of `rfl` (a local `isel_eval_k`).
- **Effect:** 23.6 GB / 128 s → 2.1 GB / 21 s (branch `agent/build-diet`, being merged). The same change did not help three other heavy Stock modules, so measure before changing a shared tactic.

### Never reduce the whole generated program in the kernel
- **Trick:** compute table properties with an untrusted generator that writes literal data, then check the data with small leaf-wise `decide +kernel` certificates (e.g. `TermSetData.lean` + `KillTab.lean`, `IselPrgTab.lean`). Split each conjunction and check one entry per leaf.
- **Why:** whole-table `decide`/`native_decide` hit 20+ GB or needed compiled evaluation. Leaf-wise checks stay small and need no extra axioms (T6 removed every `native_decide` from the compiler theorems this way).

### `assumption` at reducible transparency
- **Problem:** after `ArmState` gained a field, `stlxr_congr` in `LoopRun.lean` ran out of heartbeats even at 8M: `assumption` was unfolding the state structure.
- **Trick:** run the tactic's `assumption` with reducible transparency.
- **Effect:** the file compiles in about 30 s.

### No `first | exact a | exact b …` over goals mentioning a big definition
- **Problem:** in `synthTable_le` (`FV/Link/Ld/RelocTotal.lean`), `first | exact a | exact b …` over goals that mention lean-ld's planner `layPre o st g` ran out of heartbeats (over 200000): each failed `exact` tried to unify by unfolding the whole planner.
- **Trick:** one explicit tactic per goal (the right lemma named for each case), no `first` fallback chain.
- **Effect:** the file checks in about 9 s (A1c, #409).

## Module structure and imports

### Don't import umbrella modules from hub files
- **Problem:** the generated `IselData.lean` imported the whole `FV.Backend` umbrella but used only `Isel`/`MInst`. Nearly every isel proof and every Stock module sat downstream of it.
- **Trick:** import only the modules actually used.
- **Effect:** a change to `Unwind`, `Regalloc`, `DeadCleanup`, … rebuilds about 330–445 modules instead of 1,630–1,690 (Stock: 1,116 → 78–112), about 12.3 h → 2 h of module time (#323).
- Similarly, `FV.Opt.Proof.*` no longer imports `FV.Backend` (#257), so backend changes don't rebuild the 317 rule modules. Don't add such imports back.

### Split heavy modules
- Lean builds one module per process and a module's peak is roughly its heaviest declarations together. Splitting a heavy file into parts (keeping the old module as a file that imports the parts, so importers don't change) lowers the peak and lets the parts build in parallel.
- **Effect** (standalone `lean`, same session, peak RSS before → heaviest part): `RuleBitops7` 19.3 → 6.1 GB, `RuleArith` 15.2 → 4.5 GB, `RuleRestEmbed` 15.8 → 8.6 GB, `RuleBitops2` 12.7 → 5.2 GB, `RuleBitops5` 11.0 → 6.3 GB, `RuleShifts2` 9.5 → 6.1 GB. `RuleShifts3` did not improve (the part with `shifts_41` alone is ~10 GB): splitting helps when the peak is several declarations together, not one big one. Statements unchanged (all 7,998 `FV.Opt` constants hash-identical). (BuildDiet, `FV/Opt/Proof/Rule*P<n>.lean`.)
- Don't over-split: evm.fast-dev found larger checkpoint groups built faster warm (see below).

### Don't depend on private library internals
- A proof that reached into the private internals of `Array.qsort` would break on a toolchain update. Sorting `cfg.loops.attach` instead carries the membership fact through the sort, with the same output (#318).

## Build infrastructure

### Threads per Lean process don't help us
- Going from 2 to 8 threads gave no measurable gain on the slow modules: they spend their time in one declaration on one thread. Across 4,198 recorded module builds the median CPU/wall ratio was 1.01 (BuildAccel).
- **Exception:** `Elab.async` matters for `bv_decide`-heavy modules (`RuleExtends`: 1,652 s off vs 174–186 s on, at about twice the memory).

### Memory-cap every Lean process; share one Lake cache
- `scripts/memcap.sh` runs each command in a memory-capped cgroup (with a `/proc` watchdog fallback when the systemd user manager is down, #325). Without caps, one runaway `lean` triggered global OOM kills.
- `FV_LAKE_CACHE` points every worktree at one shared Lake artifact cache (hard links; same filesystem as the worktrees): a fresh worktree at a built commit needs no rebuild (#253).
- `scripts/lake-serial-build.py` builds module by module with caps from recorded peaks, runs light modules packed and heavy ones alone (#258).

### Wrapper tools don't make cold builds faster
- [turbo-lean](https://github.com/Th0rgal/turbo-lean) is not a Lean build: `turbo-lean build` runs the project's own `lake build` and caches the outputs. Its fast paths are cache hits and per-theorem checks against `sorry`-stubbed prefixes, which a gate cannot accept.
- Measured on 7 heavy modules, run at the same time with the same caps: +4.1% wall, +1.4% CPU (a fixed ~35–50 s per call for hashing and ingest), same peak RSS, identical statements and axioms for all 22,322 constants. Not adopted (TurboLean, `docs/research/turbo-lean.md`). Our cost is kernel checking of single large declarations; only proof changes reduce it.

### Linter warnings put the worktree path into the `.olean`
- **Problem:** `IselTermFactsCall` and `IselCtlTry` gave different `.olean` bytes on every build (three builds, three hashes; TurboLean). Rebuilding `IselTermFactsCall` outside the cache therefore rebuilt 30 downstream modules, including `KillTab` (~1,930 s).
- **Cause:** not nondeterminism but the source path. Lean 4.34 stores every linter warning in the `.olean` (`lintLogExt`, `Lean/Linter/PersistentLintLog.lean`, for `lake lint`) together with the file name Lake passed, which is absolute. In one worktree the bytes are identical (9 builds of the two modules: plain `lean` with 1, 2 and 8 threads, `lake build` twice); in another worktree they differ. 337 of 1,922 `FV` `.olean`s contained a worktree path (linters `unusedSimpArgs` 1,250 warnings, `unusedVariables` 157, `unnecessarySimpa`, `unusedSectionVars`, `defProp`, `constructorNameAsVariable`). When several agents rebuild the same module at once (e.g. after a shared change), each gets its own bytes and all their dependents miss the shared cache.
- **Fix:** `lakefile.toml` `weakLeanArgs` turns those six linters off for builds only. `weakLeanArgs` is not part of the module trace, so nothing rebuilt and cached modules stay valid; the editor still shows the warnings. Rebuilt `IselCtlTry`: no path in the `.olean` (BuildDiet).

### Merge first, verify on main
- When main moves faster than a full rebuild, a branch that passed its full checks on a recent main and rebases cleanly needs only a targeted build; a continuous main gate runs the full list afterwards and failures are fixed forward. A wrong merge can make main fail to build; it cannot make a false theorem pass, because the kernel checks every proof.

## Compiled checkers (`lean-link`, `link-check`)

### Hash maps behind a lookup parameter, not `List.lookup`/`P.func?` per element
- **Problem:** `lean-link --verified` took 2 h 26 min on fv-demo with std in the program (28,550 functions, 25,868 data objects; T3, `docs/plans/std.md` §2.2). gdb stack sampling (no `perf` on the machine) showed list scans repeated per element: `P.func?` (a scan of `P`) at every declaration/call site in `progScopeB`, `List.lookup` of the image symbols per (function, function) pair in `indB`, `reachSet` making `|data| + 1` passes over all data objects, a membership test against each unit's `localNames` list per name, `symTable` rebuilt per outside name.
- **Trick:** keep the checked definitions, add a variant taking the lookup as a function (`progScopeWithB F`, `= progScopeB` at `F = P.func?` by `rfl`), build a `Std.HashMap` once (`funcMap`, `assocMap`) and prove `(funcMap P)[n]? = P.func? n` / `(assocMap l)[n]? = l.lookup n` (foldr of `insert`, `HashMap.getElem?_insert`); the evaluated `inScopeInPar` uses the hash-map variant and `inScopeInPar_eq` stays a `simp` proof. Worklists instead of fixpoint passes; hoist tables out of `filterMap`.
- **Numbers:** `lean-link` 2 h 26 min → 11 min 55 s (715 s, max RSS 2.3 GB), no statement changed (`FV/E2E/LinkScopeFast.lean`, `FV/Front/Bundle.lean`).

### Classify once per section, not per relocation; sum sizes once
- **Problem:** `lean-link --ld` deciding `compileExe_total_ldIn`'s premises took 12–122 s per survey/fv-demo executable (A1, #409). Per-check timing (`IO.lazyPure` around each `Bool`) showed `relsInB` at 10–11 s (each relocation's `tgtOf` scanned every output section's parts, `secsOf`) and `reachOkB` at up to 108 s (`List.lookup` of the link map and the region's size `span sizes` recomputed per referenced name).
- **Trick:** decision variants proven equal to the statements' definitions: `relsInFastB` reads the per-section classification from a `Std.HashMap` built once (`secCls`, `secCls_getD`: its entry is `secsOf`'s answer; `relsInFastB_eq` by `simp` then `rfl`), `reachOkPar` uses `addrMap` and the size computed once (`reachOkPar_eq`, `simp` with `addrMap_get`).
- **Numbers:** the larger fv-demo executable 121,956 ms → 2,889 ms (`relsInB` 10,493 → 88 ms, `reachOkB` 108,454 → 303 ms); the other 17,232 → 1,130 ms (`FV/Link/Ld/RelsFast.lean`, `FV/Link/ExeLdIn.lean`). Same mistake in the link spec's symbol lookups (`symHint`/`firstVals` rebuilt per link-map entry in `inSymsB`/`pinAddr`; fix: `inSymsWith`/`pinAddrWith` taking the tables, built once by `let` outside the `all`/`filterMap`): deps executables (about 20,000 functions) 890–1,321 s → 29–36 s (`specPreB` 254–571 s → 3.8–5.5 s; `FV/Link/Ld/SpecTotal.lean`).

## From other projects (not yet measured in clifv)

From [Th0rgal/evm.fast-dev](https://github.com/Th0rgal/evm.fast-dev) (`docs/PROOF-PERFORMANCE.md`). All keep ordinary kernel checking and standard axioms. Move an entry up into the sections above once it has been measured here.

- **Kernel-opaque checked caches:** `opaque boxedValue (v : α) : {r : α // r = v} := ⟨v, rfl⟩`, used through its checked equation; full-transparency kernel reduction cannot reopen it. Reported: a 49 GiB timed-out monolith → 3–4 GiB checkpoint certificates. Candidates here: large intermediate states in Stock certificates.
- **Rewrite at the outer boundary:** prove a structural/pure evaluator equal to the executable one once, rewrite at the top, then `rfl`. Unfolding the concrete result and rewriting inside instead was 2× slower (8.8 → 19.9 s).
- **Remove repeated indexing:** proving repeated indexed extraction equal to one linear `flatMap` took a check from an unfinished 5 minutes to 39 s.
- **Compact certificates:** `of_decide_eq_true (by kernel_rfl)` (with `kernel_rfl` = `goal.refl (check := false)`) instead of `decide_cbv` shrank a 30.6 MB `.olean` to 33 KB and halved replay. clifv's `RuleAll` already uses the `check := false` idea.
- **Compact generated data:** typed DAG literals with small single-use nodes inlined shrank 9 MB ASTs to 0.3 MB (61 → 15 s).
