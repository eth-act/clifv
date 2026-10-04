import Crates.FvDemo.Input

/-! Slice 11 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 11 (`staticChks`, the validators, and `linkChks`). -/
theorem slice11_ok : fnsB input slice11 = true := by native_decide

end Crates.FvDemo
