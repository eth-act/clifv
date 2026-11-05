import FV.Backend.StockCallStoreCheck
import FV.Backend.Lowering.StockCheckedWith

namespace Backend.Stock.CallStore
set_option autoImplicit false

private def failure : String := "Stock call-result store failed source and retained-binding checks"
abbrev candidate := CheckedWith.candidate (accept := check) (failure := failure)
abbrev lowerWithPrevious := CheckedWith.lowerWithPrevious (accept := check) (failure := failure)
abbrev lowerWithPrevious_retry := @CheckedWith.lowerWithPrevious_retry check failure
abbrev lowerWithPrevious_selects := @CheckedWith.lowerWithPrevious_selects check failure
abbrev candidate_stock := @CheckedWith.candidate_stock check failure
abbrev lowerWithPrevious_preserves := @CheckedWith.lowerWithPrevious_preserves check failure
abbrev lowerWithPrevious_accepts := @CheckedWith.lowerWithPrevious_accepts check failure

end Backend.Stock.CallStore
