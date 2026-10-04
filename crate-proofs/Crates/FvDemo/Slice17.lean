import Crates.FvDemo.Input

/-! Slice 17 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 17 (`staticChks`, the validators, and `linkChks`). -/
theorem slice17_ok : fnsB input slice17 = true := by native_decide

end Crates.FvDemo
