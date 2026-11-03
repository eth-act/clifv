import FV.E2E.UnwindReachSource
import FV.Clif.LinkClifXN

namespace E2E
set_option autoImplicit false

theorem ReachX.to_reachesX {env : Clif.XEnv} {p : Clif.Program}
    {xs target : Clif.XState} (reached : ReachX env p xs target) :
    Clif.ReachesX env p xs target := by
  induction reached with
  | refl => exact .refl _
  | step next _ ih => exact .next next ih

theorem ReachX.of_reachesX {env : Clif.XEnv} {p : Clif.Program}
    {xs target : Clif.XState} (reached : Clif.ReachesX env p xs target) :
    ReachX env p xs target := by
  induction reached with
  | refl => exact .refl _
  | next next _ ih => exact .step next ih


end E2E
