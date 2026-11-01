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
- Stock parity (output identical to stock Cranelift) has two metrics. Both count.
  - The filetest comparison: every function of Cranelift's own filetests, under
    their declared settings. A function that Lean does not compile counts as a
    miss. CI measures it on every PR and main push and comments on the PR.
    See `docs/STOCK-COMPILER-COMPARISON.md`.
  - Crate parity: every function of real Rust crates that cg_clif compiles.
    Run `scripts/stock-crate-parity.py` (`docs/USAGE.md`); the overview is #557.
  - A parity PR reports both results: the CI line "gained N, lost M" and the crate
    counts before and after. It loses no match on either metric. When you choose
    between parity causes, prefer the ones that move both metrics.
- All merges must be squash merges (`gh pr merge --squash`). This grants no
  permission to push or merge.

# Verification tooling

- Before changing anything that decides what counts as proved (axiom audit, statement
  diff, caches of proof results, gates, agent check loops), apply LEARNINGS.md
  "Verification tooling" and get an independent review, with a regression test per finding.
