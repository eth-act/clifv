import FV.Isle.Generated.Program

/-! The `smin`/`smax`/`umin`/`umax` rules of `lower` and their opcodes, for the min/max source
match (`StockMinMaxSourceMatch`) and the min/max driver runs. Their own module, so that the latter
need not wait for the former. -/
namespace Backend.Stock.Proof.ScalarSelect
open Isle Isle.Aarch64
def minmaxRule (unsigned maximum : Bool) : Rule :=
  if unsigned then (if maximum then rule_lower_1226 else rule_lower_1222) else (if maximum then rule_lower_1228 else rule_lower_1224)
def minmaxFallback (unsigned maximum : Bool) : Rule :=
  if unsigned then (if maximum then rule_lower_1251 else rule_lower_1239) else (if maximum then rule_lower_1245 else rule_lower_1233)
def minmaxOpcode (unsigned maximum : Bool) : Nat :=
  if unsigned then (if maximum then 23 else 21) else (if maximum then 22 else 20)
end Backend.Stock.Proof.ScalarSelect
