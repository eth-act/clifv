import Crates.FvDemo.Input

/-! Slice 8 of `Crates.FvDemo`'s checks (generated; see there). -/

namespace Crates.FvDemo

open E2E E2E.LinkCheck

/-- The checks of the functions of slice 8 (`staticChks`, the validators, and `linkChks`). -/
theorem slice8_ok : fnsB input slice8 = true := by native_decide

end Crates.FvDemo
