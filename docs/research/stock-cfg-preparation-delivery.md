# Stock CFG and preparation proof delivery

This draft depends on [#246](https://github.com/eth-act/clifv/pull/246). It proves correspondence between the actual Stock output and its successor graph, derives raw and checked preparation success under the original source scope, transports indexed argument/parameter shapes, and connects actual spill-copy execution. The supporting source-order, entry, branch, return, TryCall, critical-edge and complete pipeline witnesses are included.

The principal roots are `stock_lower_cfg`, `stock_prepare_total`, `stock_prepare_copy_metadata` and `stock_spillArgMovesAt_runs`. Graph and copy metadata are derived from successful Stock lowering and the existing source conditions. Existing theorem variants and production defaults are preserved. Whole-driver source simulation and completeness, allocation/checker completeness, and compiler/checker/linker/generated-proof production cutover remain required by #140.

This is one dependency-closed proof unit: 83 existing Lean modules from remotely backed-up recovery snapshot b74ffb957ef0026dae0771206058705d999fdafd, stacked on #246 at44abfd79cbe4cda5ed868054b7f9e166152cf709. No worktree or build cache was created. All other unpublished work remains in the canonical recovery workspace and remote backups.

Historical backlog-tree full gates passed, but those results do not establish exact-current-PR gates after published-upstream changes. The canonical rebuild is running with source and validation scripts frozen. Exact proposed-tree validation, transitive trust review, required full local gates and CI remain pending. Keep draft until those gates pass; squash merge only.
