import Crates.DLoopsIters.Input

/-! Slice 2 of `Crates.DLoopsIters`'s checks (generated; see there). -/

namespace Crates.DLoopsIters

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 2 (`staticChks`, the validators, and `linkChks`). -/
theorem slice2_ok : fnsB input slice2 = true := by native_decide

end Crates.DLoopsIters
