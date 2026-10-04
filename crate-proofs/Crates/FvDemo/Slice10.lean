import Crates.FvDemo.Input

/-! Slice 10 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 10 (`staticChks`, the validators, and `linkChks`). -/
theorem slice10_ok : fnsB input slice10 = true := by native_decide

end Crates.FvDemo
