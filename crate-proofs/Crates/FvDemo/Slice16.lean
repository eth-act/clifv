import Crates.FvDemo.Input

/-! Slice 16 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 16 (`staticChks`, the validators, and `linkChks`). -/
theorem slice16_ok : fnsB input slice16 = true := by native_decide

end Crates.FvDemo
