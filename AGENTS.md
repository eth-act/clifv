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
- Keep the disk footprint bounded: check free space and existing worktree/cache
  usage before creating worktrees or running large/parallel builds. Target at
  least 100 GiB free on the shared filesystem; keep at least 50 GiB free after
  projected build growth. If headroom is insufficient, clean this project's
  expendable outputs or reduce build concurrency before proceeding.
- At each batch/PR completion or stop, remove unneeded clean worktrees and
  obsolete build caches/artifacts. Preserve dirty/unpublished source, branches,
  validation evidence and recovery backups; archive unique ignored evidence
  before removing a worktree. Retain one warm build cache by default; additional
  caches must serve active work and be removed when that work ends. Parallel
  agents share the disk budget; do not clean other projects to meet it. The
  worktree helper must not copy build caches automatically into each new tree.
- Budget aggregate CPU, memory and I/O across all agents, builds and cleanup
  jobs so other projects remain responsive. Use bounded build concurrency and
  low-priority, bounded compression for large archives; reduce concurrency when
  resource pressure appears. Recheck disk usage after each batch, PR and stop.
  For validation scripts that choose worker counts through `nproc`, set
  `OMP_NUM_THREADS=2 OMP_THREAD_LIMIT=2`; `LEAN_NUM_THREADS` alone does not
  limit those subprocesses. Verify the effective count before starting.
- Every worktree and additional build cache must have a current owner and
  purpose recorded in that contributor's status issue. Delegating work also
  delegates cleanup: when the task ends, remove its unneeded clean worktree and
  expendable outputs after preserving unpublished work and unique evidence.
  Agent count does not increase the shared disk or build resource budget.
- Cleanup is required even when disk headroom is ample; do not wait for a
  low-space alert. Before delegating, include cleanup ownership and the shared
  resource limits in each task. Reclaim expendable outputs when work ends,
  before starting another batch; keep only caches with a current active purpose.
- All merges must be squash merges (`gh pr merge --squash`). This grants no
  permission to push or merge.
