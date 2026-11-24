# Agent coordination

All human contributors (GitHub accounts), including new collaborators, and their
agents must follow this discipline.

- Each contributor has one status issue: reuse theirs or create
  `<github-login>: current work and intentions`. [codygunton #44](https://github.com/eth-act/clifv/issues/44).
  Contributors or their agents create their own issue, never another contributor's.
  Edit only your contributor's issue body; keep it open.
- Before starting work, read all contributor statuses and relevant task claims; update yours.
  After each commit, scope change, or stop, update it again: current goal, task/PR,
  branch/commit (mark local if unpublished), likely modules, tentative next task,
  active/waiting/idle, UTC timestamp. Next is not a reservation; stale status is uncertain.
- For overlapping behaviour, interfaces, or proof assumptions, flag the specific
  conflict in a task/status issue, mention the other contributor, and propose a
  boundary. Pause only conflicting work until resolved.
- Follow `docs/TO-PROVE.md` §§7–8 for proof-work rules and task claims.
- Stock parity (output identical to stock Cranelift) is measured two ways. The
  filetest comparison is the target; crate parity is a holdout.
  - The filetest comparison (target): every function of Cranelift's own filetests,
    under their declared settings. A function that Lean does not compile counts as
    a miss. CI measures it on every PR and main push and comments on the PR.
    See `docs/STOCK-COMPILER-COMPARISON.md`. Choose and rank parity work by this
    metric only.
  - Crate parity (holdout): every function of real Rust crates that cg_clif
    compiles. The full gate measures it on main (fv-demo, survey); the daily
    digest (#46) reports it with lost matches. Do not use it to choose, rank or
    tune parity causes, and do not measure it per PR. A loss on main is
    investigated as a bug in the change that caused it.
  - A parity PR reports the CI line "gained N, lost M" and loses no filetest match.
- All merges must be squash merges (`gh pr merge --squash`). This grants no
  permission to push or merge.

# Verification tooling

- Before changing anything that decides what counts as proved (axiom audit, statement
  diff, caches of proof results, gates, agent check loops), apply LEARNINGS.md
  "Verification tooling" and get an independent review, with a regression test per finding.
