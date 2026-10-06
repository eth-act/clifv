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
- Keep all linked worktrees under `~/clifv/.worktrees/<name>` (the primary
  checkout's `.worktrees/` directory), including worktrees for pinned upstream
  sources. Create agent worktrees with the primary checkout's
  `scripts/agent-worktree.sh <name> [base]`;
  do not create sibling `clifv-wt` directories or nested worktree roots. Keep
  `.worktrees/` ignored by Git.
- All merges must be squash merges (`gh pr merge --squash`). This grants no
  permission to push or merge.
