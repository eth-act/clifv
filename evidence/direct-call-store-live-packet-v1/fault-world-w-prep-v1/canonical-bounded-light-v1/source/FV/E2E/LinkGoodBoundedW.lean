import FV.E2E.LinkGoodBounded
import FV.E2E.LinkGoodW

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
namespace LinkSys
variable (L : LinkSys)

/-- **The per-state facts before step `n`** (`RunGoodL` bounded): at every `ReachLB n` state
whose step ends without error. -/
def RunGoodLBW (n M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g c' t, L.ReachLB n M f c M' g c' t → Arm.r .ERR (L.mach M' g t) = .None → L.GoodAtW M' g c' t


end LinkSys
end E2E
