import FV.E2E.StockMixedDivFixtures
namespace E2E.StockReturnedDivNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
abbrev operations := StockDivNIWitness.operations
abbrev arguments := StockDivNIWitness.arguments
abbrev divisor := StockMixedDivNIWitness.divisor
abbrev frontBody := StockMixedDivNIWitness.frontBody

/-- Real later scalar computation consumes the quotient/remainder while its
unused result remains original source syntax; the return is the division value. -/
def backBody (config : Configuration) : List Clif.Stmt :=
  [⟨[6000],.binary .iadd (valueType config) 5000 0⟩,
   ⟨[6001],.binary .imul (valueType config) 6000 1⟩]

def function (config : Configuration) (op : Clif.DivOp) (safe : Bool) : Clif.Function :=
  let old := StockMixedDivNIWitness.function config op safe
  {old with name := "returned_" ++ old.name,blocks := old.blocks.map fun b =>
    {b with body := b.body ++ backBody config}}

def frame (config : Configuration) (op : Clif.DivOp) (safe : Bool)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config op safe
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := (function config op safe).blocks[0]!.body
  term := .ret [5000] }
end E2E.StockReturnedDivNIWitness
