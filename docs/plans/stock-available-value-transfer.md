# Availability-guarded constant transfer

Part of #140, following merged record noninterference #158. Production still
uses the legacy driver; this proof slice changes no compiler behavior.

1. Restrict required values at each source boundary to demanded values that are
   source-available there. Frames may retain stale values across loop iterations.
2. Prove that crossing a statement adds only its results to availability. Allow
   the required set to change without assuming the new result was already held.
3. Reuse the existing selected constant root, binder and alias-resolved execution
   proof. Derive fragment write bounds from its existing CodeShape; combine these
   with the before/after availability relation.
4. Inhabit all premises with the existing mapped constant fixture: parameter11,
   stale result77, selected MOVZ9, and the actual finite-fuel alias resolver.
5. Validate normal builds, runtime/encoding/E2E gates, unchanged identities and
   inherited axiom sets, using Lean MCP for the new roots. Publish a bounded PR.

Remaining boundary: the constant transfer takes internal selection observations,
the final result resolution and other-value interval exclusion as premises.
Connect those to actual whole-driver records and the merged structural theorems,
then cover other families, reserved writes, memory/traps, complete simulation and
completeness before production cutover. No added source restriction or accepted
program certificate is authorized by this helper slice.
