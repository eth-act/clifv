# Agent coordination

Use GitHub issues in `eth-act/clifv` to give the other contributor a short,
current account of your work. This is a heads-up, not a second task tracker.

## Contributor status issues

- Cody: [Cody: current work and intentions](https://github.com/eth-act/clifv/issues/44).
- Kev: search for the exact title `Kev: current work and intentions`. If it does
  not exist, **Kev's agent creates it** when adopting this workflow. Cody's agents
  must not create or maintain Kev's status issue.

Reuse the existing issue. Keep it open and edit its body rather than posting a
comment after every commit. Each agent updates only its contributor's status.
Use this short format:

```text
Current: <work package and intended result, or none>
Task: <task issue / PR links, or none>
Branch / latest commit: <reference; mark unpublished commits as local>
Likely changes: <modules or interfaces>
Next, tentatively: <likely next task, or not selected>
State: active / waiting / idle
Updated: <UTC timestamp>
```

## Required discipline

1. Before starting a work package or other substantial task, read both status
   issues, the relevant task claims, and the applicable parts of `docs/PLAN.md`
   and `docs/TO-PROVE.md`. If overlap is plausible, inspect the other active
   branch. A missing status issue does not block unrelated work; use the existing
   claims and branches and note the uncertainty.
2. Before starting, update your status with the intended result, likely changes,
   and tentative next task. Follow the existing work-package claim protocol in
   `docs/TO-PROVE.md` §8; a status issue does not replace a task claim.
3. After **each commit**, update your status before continuing work. Also update
   it when scope changes, work stops, or a task finishes, even without a commit.
   State the remaining work or that you are waiting/idle; do not leave finished
   work marked active.
4. If work overlaps in behaviour, interfaces, or proof assumptions, explain the
   specific conflict in the relevant task issue (or your status issue if there
   is no task issue). Mention the other contributor using the GitHub account
   shown on their status issue and propose a boundary. Pause only the conflicting
   part until the boundary is clear; continue independent work.
5. Treat `Next` as a forecast, not a reservation. Treat stale status as uncertain,
   not as permission or a permanent lock. Never edit the other contributor's
   status or present an inferred plan as their commitment.

Task issues retain completion criteria and claim/release/close tracking. Status
issues stay open. The worktree, proof, resource, and verification rules in
`docs/TO-PROVE.md` §7 still apply to proof work packages. Status updates do not
authorize a Git push or merge.

## Merging

All merges must be squash merges. For GitHub pull requests, use the squash merge
option (`gh pr merge --squash`); do not use merge commits or rebase-and-merge.
This sets the merge method, not permission to merge: existing restrictions on
agent pushes and merges still apply.
