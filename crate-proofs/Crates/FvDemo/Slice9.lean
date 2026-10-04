import Crates.FvDemo.Input

/-! Slice 9 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 9 (`staticChks`, the validators, and `linkChks`). -/
theorem slice9_ok : fnsB input slice9 = true := by native_decide

end Crates.FvDemo
