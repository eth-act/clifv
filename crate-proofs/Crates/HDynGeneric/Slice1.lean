import Crates.HDynGeneric.Input

/-! Slice 1 of `Crates.HDynGeneric`'s checks (generated; see there). -/

namespace Crates.HDynGeneric

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 1 (`staticChks`, the validators, and `linkChks`). -/
theorem slice1_ok : fnsB input slice1 = true := by native_decide

end Crates.HDynGeneric
