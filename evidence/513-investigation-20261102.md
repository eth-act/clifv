# PR #513 historical investigation

Reviewed 2026-11-02. This investigation used read-only GitHub and Git evidence. It is not a correctness review.

- PR: https://github.com/eth-act/clifv/pull/513
- Owner: codygunton. Head: 5aae55c32030e3e9f15ab6515a2cccf268751646.
- The author last updated the PR on 2026-10-22T23:39:24Z. GitHub records no reviews or comments.
- The body still states that author gates run or remain pending. It explicitly prohibits merging before those gates pass.
- The latest-head CI run concluded cancelled. Its annotation states: “The job has exceeded the maximum execution time of 30m0s”. The job lasted 30m21s. This is not evidence of a Lean proof failure.
- CI: https://github.com/eth-act/clifv/actions/runs/39872906710/job/120151767598
- The reporting and lost-match jobs skipped after cancellation.
- The GitHub comparison reports 299 main commits since divergence and four unmerged PR commits. GitHub currently reports MERGEABLE/UNSTABLE.

## Preserved local evidence

Commit 385dc1fc stores `evidence/outcome-and-mixed-recovery.tar.gz`. Read the archive without extracting build outputs.

- `state/stock-outcome-final-normal-check.json`: exact PR head, exit 143. It does not establish a complete normal build.
- `state/stock-outcome-final-normal-drain.json`: the controller stopped after healthy optimizer workers finished. The receipt explicitly labels the overbroad full replay partial.
- `state/stock-outcome-interface-axiom-check.json`: six moved declarations passed at the earlier 9f16daa5 head. Full affected audits remained pending.
- `state/stock-outcome-value-boundary-check.json`: the isolated two-lemma provider and complete LowerSim copy passed. Elaborated types and axiom sets matched.
- `state/stock-div-current-status.md`, timestamp 2026-10-23T01:00:17Z: the 197-root/1203-import witness chunk still ran. The status required all final applicable gates before merge.

These records show unfinished verification and delivery. They do not show a completed author gate that the merge queue ignored.

## Replacement check and disposition

Current `origin/main` lacks `FV/Backend/Proof/LowerOutcomes.lean` and `LowerValueRelations.lean`. `PrepareSound.lean` still imports `LowerSim`.

Parithosh's merged #769 explicitly protected 204 files belonging to #513. Its import cleanup did not replace this extraction.

Reference: https://github.com/eth-act/clifv/pull/769

The extraction remains unlanded. Reconcile it onto current main and finish the applicable gates. Do not mark it superseded without a new comparison. No correctness or merge approval is implied.

The execution coordinator separately checked all 207 PR files against the pending binary, executable, generated-proof, and source-adapter packets. Those packets have no direct file overlap. Shared dependency interfaces still require fresh import-context checks. #513 is not a prerequisite for #887.
