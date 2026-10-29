module

public import FV.E2E.StockReturnedDivFixtures

@[expose] public section

namespace E2E.StockGeneralDivNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
inductive Layout where
  | unused | consumed | multiple
  deriving Inhabited, DecidableEq, Repr
def layouts : List Layout := [.unused,.consumed,.multiple]
def layoutName : Layout → String
  | .unused => "unused"
  | .consumed => "consumed"
  | .multiple => "multiple"
abbrev operations := StockDivNIWitness.operations
abbrev arguments := StockDivNIWitness.arguments
abbrev divisor := StockMixedDivNIWitness.divisor

def body (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout) : List Clif.Stmt :=
  (StockReturnedDivNIWitness.function config op safe).blocks[0]!.body ++
    match layout with
    | .multiple => [⟨[6500],.div op (valueType config) 6001 (divisor safe)⟩]
    | _ => []

def returned : Layout → Nat
  | .unused => 4008
  | .consumed | .multiple => 6001

/-- Original arguments, explicit stack slot and proved scalar prefix are retained.
Divisions may have unused results, feed scalar consumers, or occur repeatedly. -/
def function (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout) : Clif.Function :=
  let old := StockReturnedDivNIWitness.function config op safe
  {old with name := "general_" ++ layoutName layout ++ "_" ++ old.name,blocks := old.blocks.map fun b =>
    {b with body := body config op safe layout,term := .ret [returned layout]}}

def frame (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config op safe layout
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := body config op safe layout
  term := .ret [returned layout] }

def resultValue (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout)
    (input : Nat → BitVec (valueType config).width) : Except Clif.TrapCode (BitVec (valueType config).width) := do
  let numerator := StockHighMulNIWitness.resultValue config input
  let denominator := if safe then 2 else input 8
  let quotient ← Clif.Sem.div op numerator denominator
  let consumed := (quotient + input 0) * input 1
  match layout with
  | .unused => pure numerator
  | .consumed => pure consumed
  | .multiple =>
    let _ ← Clif.Sem.div op consumed denominator
    pure consumed
end E2E.StockGeneralDivNIWitness
