import FV.E2E.StockNarrowFixtures
import FV.E2E.ABIReadDiv
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockScalarNI

namespace E2E.StockNarrowNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def checks (f : Clif.Function) (cleanup : Bool) : Bool :=
  Stock.Scalar.sourceOk f &&
  match Stock.lower f with
  | .error _ => false
  | .ok result =>
    DivBoundary.check f.sig result.code && Stock.Scalar.check f result.code &&
    SemanticNI.check f result.code &&
    (match Stock.Scalar.lowerValidated f with
      | .error _ => false
      | .ok vc => decide (vc = result.code)) &&
    match Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (Stock.Arithmetic.stage cleanup result.code) vcp &&
      match leanAlloc vcp with
      | .error _ => false
      | .ok rf =>
        (checkAlloc vcp rf).isOk &&
        match lowerRFunc vcp rf with
        | .error _ => false
        | .ok af =>
          match emitFunc 0 af with
          | .error _ => false
          | .ok fa => formsCoveredB ⟨fa.k,af.slotBase⟩ vcp && fa.layout.isOk

def completed : Clif.Outcome → Bool
  | .returned .. | .trapped .. => true
  | _ => false

def returned : Clif.Outcome → Bool
  | .returned .. => true
  | _ => false

def trapped (code : Clif.TrapCode) : Clif.Outcome → Bool
  | .trapped observed => code == observed
  | _ => false

def sourceCases (f : Clif.Function) (ty : Clif.Ty) : Bool :=
  ([0,1,2].all fun sample => completed (sourceRun f ty sample)) &&
    returned (sourceRun f ty 1)

def primitiveTraps (config : Configuration) (c : Case) : Bool :=
  match c.inst with
  | .div op _ _ _ =>
      trapped .intDivz (sourceRun (function config c) c.inputTy 0) &&
      (if op == .sdiv then trapped .intOvf (sourceRun (function config c) c.inputTy 2) else true)
  | _ => true

def primitiveGrid : Bool := conventions.all fun config => widths.all fun ty =>
  (cases ty).all fun c =>
    let f := function config c
    if outsideOriginalScope c then !lowerScopeB f && !Stock.Scalar.sourceOk f
    else sourceCases f c.inputTy && primitiveTraps config c && checks f false && checks f true

def mixedGrid : Bool := conventions.all fun config => widths.all fun ty =>
  let f := mixedFunction config ty
  sourceCases f ty && checks f false && checks f true

def grid : Bool := primitiveGrid && mixedGrid

/-- The rejected i8 byte-swap fixture violates the unchanged original scope. -/
theorem bswap8_original_scope : conventions.all (fun config =>
    !(lowerScopeB (function config ⟨s!"unary_{repr Clif.UnaryOp.bswap}",.i8,.unary .bswap .i8 1⟩))) = true := by
  decide +kernel

/-- Fixed complete narrow pipelines and genuine source returns/traps only. -/
theorem checks_true : grid = true := by native_decide

end E2E.StockNarrowNIWitness
