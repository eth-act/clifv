module

public import FV.E2E.StockMaskFixtures
public import FV.E2E.StockNarrowChecks

@[expose] public section

namespace E2E.StockMaskNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

abbrev checks := StockNarrowNIWitness.checks

def grid : Bool := conventions.all fun config =>
  (functions config).all fun (f,ty) =>
    StockNarrowNIWitness.sourceCases f ty && checks f false && checks f true

def mixedTraps : Bool := conventions.all fun config => widths.all fun input => widths.all fun output =>
  StockNarrowNIWitness.trapped .intDivz (StockNarrowNIWitness.sourceRun (mixedFunction config input output) input 0) &&
  StockNarrowNIWitness.trapped .intOvf (StockNarrowNIWitness.sourceRun (mixedFunction config input output) input 2)

def returnedValue (f : Clif.Function) (input : Clif.Ty) (sample : Nat) (expected : Int) : Bool :=
  match StockNarrowNIWitness.sourceRun f input sample with
  | .returned [value] _ => value.toInt == expected
  | _ => false

def primitiveValues : Bool := conventions.all fun config => widths.all fun input => widths.all fun output =>
  returnedValue (function config input output) input 0 0 &&
  returnedValue (function config input output) input 1 (-1)

def mixedValues : Bool := conventions.all fun config => widths.all fun input => widths.all fun output =>
  returnedValue (mixedFunction config input output) input 1 (-1)

/-- Fixed full bmask/nop pipelines, including all sixteen width pairs,
arbitrary-position scalar/division mixtures, and real original source traps. -/
theorem checks_true : (grid && mixedTraps && primitiveValues && mixedValues) = true := by native_decide

end E2E.StockMaskNIWitness
