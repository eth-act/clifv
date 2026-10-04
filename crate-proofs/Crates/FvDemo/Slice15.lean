import Crates.FvDemo.Input

/-! Slice 15 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 15 (`staticChks`, the validators, and `linkChks`). -/
theorem slice15_ok : fnsB input slice15 = true := by native_decide

end Crates.FvDemo
