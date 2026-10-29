module

public import FV.Link.ReachCheckEq

@[expose] public section

namespace Link
open E2E.LinkCheck
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def reachFixture (first second : Nat) : LinkSpec :=
  { (default : LinkSpec) with
    funcs := [{ clif := "function %reach_caller() system_v {\nfn0 = %target() system_v\nblock0:\n return\n}\n", ra := "" }]
    names := ["reach_caller"]
    sizes := [0]
    outside := [("target",first),("target",second)] }

/-- A real parsed external declaration checks the first duplicate address:
the nearby target passes, while the strict branch-range boundary fails. -/
theorem LinkSpec.reachOkMap_duplicates :
    (reachFixture 4 (2^27)).reachOkMap = true ∧
    (reachFixture (2^27) 4).reachOkMap = false := by
  native_decide

end Link
