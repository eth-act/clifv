import Crates.FvDemo.Input

/-! Slice 14 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 14 (`staticChks`, the validators, and `linkChks`). -/
theorem slice14_ok : fnsB input slice14 = true := by native_decide

end Crates.FvDemo
