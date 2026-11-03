import FV.E2E.LinkGoodBoundedW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual return bounds every caller step in unbounded linked reachability. -/
theorem reachLB_of_return (L : LinkSys) {n M M' : Nat} {f g : Clif.Function}
    {initial c' t : Arm.ArmState}
    (returned : RetL (L.A f) initial (runX (L.mach M f) n initial))
    (reached : L.ReachL M f initial M' g c' t) :
    L.ReachLB n M f initial M' g c' t := by
  cases reached with
  | act noReturn =>
    rename_i k
    have before : k < n := Nat.lt_of_not_le (fun bound => noReturn n bound returned)
    exact .inl ⟨k,before,noReturn,rfl,rfl,rfl,rfl⟩
  | nest noReturn called errorFree nested =>
    rename_i M0 k h
    have before : k < n := Nat.lt_of_not_le (fun bound => noReturn n bound returned)
    exact .inr ⟨M0,k,h,rfl,before,noReturn,called,errorFree,nested⟩

/-- The actual return converts bounded W facts to the complete linked W relation, including callees. -/
theorem runGoodLW_of_bounded_return (L : LinkSys) {n M : Nat} {f : Clif.Function} {initial : Arm.ArmState}
    (returned : RetL (L.A f) initial (runX (L.mach M f) n initial))
    (good : L.RunGoodLBW n M f initial) : L.RunGoodLW M f initial := by
  intro M' g c' t reached errorFree
  exact good M' g c' t (L.reachLB_of_return returned reached) errorFree

end E2E.LinkSys
