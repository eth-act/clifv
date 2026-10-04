import Crates.FvDemo.Input

/-! Slice 4 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 4 (`staticChks`, the validators, and `linkChks`). -/
theorem slice4_ok : fnsB input slice4 = true := by native_decide

end Crates.FvDemo
