import FV.E2E.LinkGood

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
namespace LinkSys
variable (L : LinkSys)

/-- **The states of the activation of `f` at depth `M` entered at `c` before its step `n`**, and
of the activations it calls before its step `n` (`ReachL` with the entry activation's index below
`n`). -/
def ReachLB (n M : Nat) (f : Clif.Function) (c : Arm.ArmState) (M' : Nat) (g : Clif.Function)
    (c' t : Arm.ArmState) : Prop :=
  (∃ k < n, (∀ j ≤ k, ¬ RetL (L.A f) c (runX (L.mach M f) j c)) ∧ M' = M ∧ g = f ∧ c' = c ∧
      t = runX (L.mach M f) k c) ∨
  (∃ M0 k h, M = M0 + 1 ∧ k < n ∧ (∀ j ≤ k, ¬ RetL (L.A f) c (runX (L.mach (M0 + 1) f) j c)) ∧
      L.CallsAtL f (runX (L.mach (M0 + 1) f) k c) h ∧
      Arm.r .ERR (runX (L.mach (M0 + 1) f) (k + 1) c) = .None ∧
      L.ReachL M0 h (enterAt (L.A h) (runX (L.mach (M0 + 1) f) k c)) M' g c' t)


end LinkSys
end E2E
