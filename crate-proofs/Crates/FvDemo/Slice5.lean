import Crates.FvDemo.Input

/-! Slice 5 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 5 (`staticChks`, the validators, and `linkChks`). -/
theorem slice5_ok : fnsB input slice5 = true := by native_decide

end Crates.FvDemo
