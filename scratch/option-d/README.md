# Option D measurement scripts (scratch, #1017 / #1119 / #140; never merged)

Branch `agent/BaselineD3` = `agent/NightlyPin1` f45d533eb (main 5e21e6bfe + the cg_clif-on-Cranelift-0.136.1
patch) + the SCRATCH `FV_SCRATCH_CLIF=opt` cargo-fv switch (ReleaseScope1; Lean compiles cg_clif's `.opt.clif`)
+ these scripts. It is the tree of the measurement worktree `BaselineD1-meas`. The prototype drop of unused
`notrap` loads is branch `agent/BaselineD1` 79f2b9f89 (draft PR #1140, DO NOT MERGE).

Paths are those of clifv-remote: `~/clifv/wt/BaselineD1-meas` (this tree, `W`), `~/clifv/wt/BaselineD1`
(the prototype, `P`), scripts in `~/clifv/tmp/BaselineD{1,2,3}/` (the three subdirectories here), crate
sources and lockfiles of the release report in `~/clifv/tmp/CrateSurvey2`. Tools: in both trees
`cargo build --release` of `rust/` (cargo-fv) and `lake build lean-backend link-check lean-link`;
in `W`, `scripts/build-cg-clif.sh` for Cranelift 0.135.0 (`target/cg_clif`) and with
`scripts/patches/cg-clif-cranelift-0.136.1.patch` for 0.136.1 (`target/cg_clif-cl0.136.1`).
Both cg_clif builds are copied to ONE path before each run (the backend path feeds cargo's metadata
hash, hence the symbol names). Remote env: `LEAN_NUM_THREADS=16 FV_JOBS=16`.

| what | command (cwd = the tree named) | output |
|---|---|---|
| debug lines, both Cranelifts (gate mode; bigframe-unwind plain as the gate) | `W=$W ACT=$W/target/cg_clif-active bash BaselineD3/debug4.sh OUT fv-demo survey bigframe-unwind deps fv-demo+std` | `OUT/<line>-<cl>.{compare.log,parity.txt}`, `s2s-<line>.txt`, `notrap-<line>.txt` |
| prototype off / on, 0.136.1, plain | `NOBC=1 FV_SCRATCH_NOTRAP_OFF=1 W=$P PLAIN=1 CLS=0.136.1 bash BaselineD3/debug4.sh OFF <line>` then `NOBC=1 W=$P PLAIN=1 CLS=0.136.1 REF=OFF bash BaselineD3/debug4.sh ON <line>` | `ON/s2sref-<line>-0.136.1.txt` |
| per-function join, prototype | `notrap-dead.py --s2s ON/s2sref-L-0.136.1.json --json notrapP-L.json ON/keep-L-0.136.1`; `BaselineD3/join2.py L` | `join2-L.txt` |
| release, 9 crates, unopt + opt input, both Cranelifts | `bash BaselineD2/release2.sh <crate> <version>` | `BaselineD1/rel-<cl>/<crate>/parity-{fv,optfv}.txt`, dumps |
| release with the prototype drop (0.136.1) | `bash BaselineD3/relp2.sh <crate> <version> …` | `BaselineD2/relp-0.136.1/<crate>/parity-{fv,optfv}.txt` |
| validator (3 checkers × 2 Cranelifts) + projection | `bash BaselineD2/mv.sh` (`midval-check --cert`, binaries built at 5e21e6bfe, 0a42dc718 (#1136), d1fc25665 (#1138)); `analyze.py mv-0.136.1-<bin> relp-0.136.1` for the drop | `analysis-<cl>-<bin>.txt` |
| release table | `python3 BaselineD2/sum.py` | markdown |
| stock comparison with the prototype | in `P`: `scripts/stock-compiler-comparison.sh` as CI, and with `FV_SCRATCH_NOTRAP_VERIFIED=1` (projection: dropped functions counted as proved) | `summary.md` |

Projection (`analyze.py`): a function the validator accepts is compiled from the optimised CLIF (g),
a rejected one from the unoptimised CLIF (f); the projected parity counts the byte-identical functions
of that mix, from the two plain runs' per-function parity.
