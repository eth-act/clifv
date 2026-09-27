import FV.Backend.Proof.IselExclBase
open Backend Backend.Proof Isle Isle.Aarch64

/-! Untrusted helper for `FV/Backend/Proof/IselExclBase.lean` (run:
`lake env lean --run FVTest/Backend/Proof/Excl/Gen.lean`) after regenerating the ISLE data:
prints the literal `closureRootIds` (the ids of `Closure.rules` root rules; `closureRootIds_eq`
re-checks it in the kernel) and every root rule of `lower` that `exclOk` rejects (must be none,
else `exclOk_program` fails: extend the checker or move the rule into the closure). -/

def main : IO Unit := do
  let ids := (Closure.rules.toList.filter (·.isRoot)).map (·.rule)
  IO.println s!"closureRootIds ({ids.length}): {ids}"
  let rs := program.rulesOf TId.lower
  let bad := rs.filter fun r => !exclOk program r
  IO.println s!"lower rules {rs.length}, closure roots {(rs.filter closureRoot).length}, rejected {bad.length}"
  for r in bad do IO.println s!"  rejected: {r.id} {r.name}"
