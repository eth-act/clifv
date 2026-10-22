import FV.Link.ReachCheck
import FV.Link.ExeInputReach
import FV.Link.PlacedEq

namespace Link
open E2E E2E.LinkCheck E2E.BinCheck Backend.Proof.RelocProv

/-- The executable map check retains the original reach condition on every
input, including duplicate names and out-of-range addresses. -/
theorem LinkSpec.reachOkMap_eq (P : LinkSpec) : P.reachOkMap = P.reachOkB := by
  have h : ∀ n, P.input0.addrOf n = ((addrMap P.addrs)[n]?).getD 0 := fun n => by
    rw [addrMap_get]; rfl
  simp only [reachOkMap, reachOkB, refsReachB, callReachB, pageReachB, LinkInput.symAddr, h]

/-- An actual empty region inhabits both sides of the universal equality. -/
theorem LinkSpec.reachOkMap_empty :
    (default : LinkSpec).reachOkMap = true ∧ (default : LinkSpec).reachOkB = true := by
  exact ⟨rfl,rfl⟩

end Link
