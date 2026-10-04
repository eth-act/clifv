import Crates.FvDemo.Input

/-! Slice 3 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 3 (`staticChks`, the validators, and `linkChks`). -/
theorem slice3_ok : fnsB input slice3 = true := by native_decide

end Crates.FvDemo
