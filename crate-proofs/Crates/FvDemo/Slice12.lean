import Crates.FvDemo.Input

/-! Slice 12 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 12 (`staticChks`, the validators, and `linkChks`). -/
theorem slice12_ok : fnsB input slice12 = true := by native_decide

end Crates.FvDemo
