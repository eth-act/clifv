import Crates.FvDemo.Input

/-! Slice 13 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 13 (`staticChks`, the validators, and `linkChks`). -/
theorem slice13_ok : fnsB input slice13 = true := by native_decide

end Crates.FvDemo
