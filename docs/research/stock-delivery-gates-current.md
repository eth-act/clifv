# Exact delivery validation

The full original #140 goal is active and production uses the legacy driver.

PR #246 is being validated at its exact commit44abfd79 in the clean `stock-delivery-gates` worktree. The active recovery checkout and its source/script freeze are unchanged. The large original IselPrgTab kernel finished successfully;285 completed canonical targets are reused. The original controller PID1233457 is deliberately queue-held while worker PID3247835 uses the SAME warm cache, crate build and Rust target through symbolic links. No cache copy or extra warm cache was created. This is validation scheduling, not a paused goal or a kernel restart.

The worker restores the original controller on failure. On successful local gates it leaves the cache exclusively held for receipt/MCP review; release with `python3 /tmp/stock-pr246-gates.py --release`. Do not start another compiler against either view while this lease is held. Check the live worker handle and `/tmp/stock-delivery-cache-lease.json` before changing this schedule.

The full exact-PR module build, --rehash full library/tools build, crates, public/compiler audits, runtime, encoder and both E2E modes are pending. A completion reviewer checks all rejection/failure summaries, every original identity/stage list, all changed-module constants, old axiom sets and current main/CI. One MCP bundle retains the complete statements of all public roots and documented compiler theorem variants. Neither draft is merge-ready yet; squash only after required evidence passes.

[Live-handle checkpoint and required checks](stock-delivery-gates-current.json). [Source preservation review](stock-pr246-source-review.json). All previous FV library bytes are unchanged;55changed Lean files match the historical validated snapshot, which is not a substitute for these current gates.

Finish#246 and#247 in dependency order, archive unique evidence and remove the clean validation worktree after the batch, then resume the same canonical controller and every remaining whole-driver proof/cutover obligation.
