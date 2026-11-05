import FV.E2E.UnwindStatement

namespace E2E
set_option autoImplicit false

theorem ReachX.trans {env : Clif.XEnv} {p : Clif.Program}
    {xs middle target : Clif.XState}
    (first : ReachX env p xs middle) (rest : ReachX env p middle target) :
    ReachX env p xs target := by
  induction first with
  | refl => exact rest
  | step next _ ih => exact .step next (ih rest)

/-- Reuse the original unwind admission after an actual same-function continuation. -/
theorem TrapsExplicitX.at_reached {env : Clif.XEnv} {p : Clif.Program}
    {initial current : Clif.State} (admitted : TrapsExplicitX env p initial)
    (reached : ReachX env p initial.toX current.toX)
    (sameFunction : current.frame.func = initial.frame.func) :
    TrapsExplicitX env p current := by
  constructor
  · intro xs code statement rest path trapped body
    exact admitted.stmt xs code statement rest (reached.trans path) trapped body
  · intro xs code fn args table path trapped body term block member
    exact admitted.tryCall xs code fn args table (reached.trans path) trapped body term
      block (by simpa only [sameFunction] using member)
  · intro xs code callee args table path trapped body term block member
    exact admitted.tryCallInd xs code callee args table (reached.trans path) trapped body term
      block (by simpa only [sameFunction] using member)
  · intro xs statement rest signature callee args path body inst member value found
    exact admitted.indirect xs statement rest signature callee args (reached.trans path)
      body inst (by simpa only [sameFunction] using member) value found
  · intro xs callee args table path body term member value found
    exact admitted.tryIndirect xs callee args table (reached.trans path) body term
      (by simpa only [sameFunction] using member) value found

end E2E
