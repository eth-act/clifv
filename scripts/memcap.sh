#!/usr/bin/env bash
# Run a command in its own memory-capped cgroup scope. If it (and its children, e.g. every
# `lean` process lake starts) exceed the cap, only this scope is killed (exit 137). The global
# OOM killer never fires, so the agent harness and the other agents survive.
#
# usage: scripts/memcap.sh <cmd> [args...]     cap: $FV_MEMCAP (default 16G)
#
# Why: runaway Lean elaboration or kernel reduction (e.g. `decide`/`rfl` over the exported ISLE
# rule data) has reached 37-58 GB RSS on this 62 GB machine, which triggered global OOM kills.
# Those kills aborted the agent harness, which kills every running agent.
set -euo pipefail
exec systemd-run --user --scope --quiet \
  -p MemoryMax="${FV_MEMCAP:-16G}" -p MemorySwapMax=0 -p TasksMax=infinity "$@"
