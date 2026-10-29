import Lean
open Lean

/-! `name<TAB>axioms` for every theorem of the FV/FVTest modules imported by ROOT (axioms
sorted; `Lean.collectAxioms`, as `#print axioms`). usage: lean --run axdump.lean ROOT -/

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := args[0]!.toName}] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "", fileMap := default, maxHeartbeats := 0 }
  let mut names := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless m.getRoot == `FV || m.getRoot == `FVTest do continue
    if n.isInternal then continue
    if let .thmInfo _ := ci then names := names.push n
  names := names.qsort (·.toString < ·.toString)
  let r ← (do
      let mut out := #[]
      for n in names do
        let ax ← collectAxioms n
        out := out.push s!"{n}\t{" ".intercalate ((ax.map toString).qsort (· < ·)).toList}"
      return out : CoreM (Array String)).toIO' ctx { env }
  for l in r do IO.println l
