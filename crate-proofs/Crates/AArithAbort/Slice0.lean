import Crates.AArithAbort.Input

/-! Slice 0 of `Crates.AArithAbort`'s checks (generated; see there). -/

namespace Crates.AArithAbort

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 0 (`staticChks`, the validators, and `linkChks`). -/
theorem slice0_ok : fnsB input slice0 = true := by native_decide

end Crates.AArithAbort
