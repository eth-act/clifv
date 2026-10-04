import Crates.FvDemo.Input

/-! Slice 7 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 7 (`staticChks`, the validators, and `linkChks`). -/
theorem slice7_ok : fnsB input slice7 = true := by native_decide

end Crates.FvDemo
