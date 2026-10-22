import FV.E2E.StockProductionFixtures
namespace E2E.StockDivNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false

def operations : List Clif.DivOp := [.sdiv,.udiv,.srem,.urem]

/-- Live division by the ninth stack argument, seven other original parameters
and the original explicit source slot, in every shipped integer ABI. -/
def function (config : Configuration) (op : Clif.DivOp) : Clif.Function :=
  let old := StockArithmeticNIWitness.function config
  let name := "stock_div_" ++ (match op with | .sdiv => "sdiv" | .udiv => "udiv" | .srem => "srem" | .urem => "urem")
  { old with
    name := name
    blocks := old.blocks.map fun b =>
      {b with body := [⟨[100],.div op (valueType config) 1 8⟩],term := .ret [100]} }

def arguments (config : Configuration) (input : Nat → BitVec (valueType config).width) : List Clif.Val :=
  (List.range 9).map fun i => ⟨valueType config,input i⟩

def frame (config : Configuration) (op : Clif.DivOp)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config op
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := [⟨[100],.div op (valueType config) 1 8⟩]
  term := .ret [100] }
end E2E.StockDivNIWitness
