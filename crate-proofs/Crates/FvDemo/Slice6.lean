import Crates.FvDemo.Input

/-! Slice 6 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 6 (`staticChks`, the validators, and `linkChks`). -/
theorem slice6_ok : fnsB input slice6 = true := by native_decide

end Crates.FvDemo
