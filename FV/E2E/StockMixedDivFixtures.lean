import FV.E2E.StockHighMulFixtures
import FV.E2E.StockDivFixtures
namespace E2E.StockMixedDivNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
abbrev operations := StockDivNIWitness.operations
abbrev arguments := StockDivNIWitness.arguments

def divisor (safe : Bool) : Nat := if safe then 5001 else 8

def frontBody (config : Configuration) (safe : Bool) : List Clif.Stmt :=
  (StockHighMulNIWitness.function config).blocks[0]!.body ++
    (if safe then [⟨[5001],.iconst (valueType config) 2⟩] else [])

/-- The full live scalar computation is the dividend. The divisor is the original
ninth stack argument, or an original source constant for the safe selected roots. -/
def function (config : Configuration) (op : Clif.DivOp) (safe : Bool) : Clif.Function :=
  let old := StockHighMulNIWitness.function config
  let name := "stock_mixed_div_" ++ (match op with | .sdiv => "sdiv" | .udiv => "udiv" | .srem => "srem" | .urem => "urem") ++ (if safe then "_two" else "")
  {old with name := name,blocks := old.blocks.map fun b =>
    {b with body := b.body ++ (if safe then [⟨[5001],.iconst (valueType config) 2⟩] else []) ++
      [⟨[5000],.div op (valueType config) 4008 (divisor safe)⟩],term := .ret [5000]}}

def frame (config : Configuration) (op : Clif.DivOp) (safe : Bool)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config op safe
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := (function config op safe).blocks[0]!.body
  term := .ret [5000] }
end E2E.StockMixedDivNIWitness
