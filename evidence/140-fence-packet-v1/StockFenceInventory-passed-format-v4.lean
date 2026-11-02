import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- All original lower rules use one of the checked instruction formats. -/
theorem stock_lower_all_formats : R.lower.all (fun r => match ruleFmt r with
    | none => false
    | some ft => 2447 ≤ ft && ft < 2483) = true := by decide +kernel

/-- NullAry has eight actual root candidates in the original complete lower list. -/
theorem stock_nullary_inventory : R.lower.filter (fun r => ruleFmt r == some 2466) =
    [rule_lower_78,rule_lower_2476,rule_lower_2481,rule_lower_2496,
     rule_lower_2499,rule_lower_2502,rule_lower_2770,rule_lower_3292] := by decide +kernel

end Backend.Stock.Proof
