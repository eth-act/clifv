import FV.E2E.StockGeneralDivFixtures
import FV.E2E.DivBoundaryCheck
import FV.Backend.Proof.RegallocCover
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockScalarNI
namespace E2E.StockGeneralDivNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def checks (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout) (cleanup : Bool) : Bool :=
  lowerScopeB (function config op safe layout) && dominatedB (function config op safe layout) && sigAbiOk (function config op safe layout).sig &&
  match Stock.lower (function config op safe layout) with
  | .error _ => false
  | .ok result =>
    DivBoundary.check (function config op safe layout).sig result.code &&
    Stock.Scalar.check (function config op safe layout) result.code && SemanticNI.check (function config op safe layout) result.code &&
    (match Stock.Scalar.lowerValidated (function config op safe layout) with
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

/-- Concrete original inputs used only to witness actual source outcomes. -/
def caseInput (config : Configuration) (positive : Bool) : Nat → BitVec (valueType config).width :=
  fun i => BitVec.ofNat _ (if positive then 2*i+1 else 0)

def caseWanted (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) (layout : Layout) :=
  let input := caseInput config positive
  resultValue config op safe layout input

def caseRun (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) (layout : Layout) : Clif.Outcome :=
  Clif.runLoop Clif.Env.empty {funcs := []} ((function config op safe layout).blocks[0]!.body.length+1)
    ⟨frame config op safe layout (caseInput config positive) 4096,[],Clif.Mem.empty⟩

def outcomeAgrees (ty : Clif.Ty) (wanted : Except Clif.TrapCode (BitVec ty.width))
    (actual : Clif.Outcome) : Bool :=
  match wanted,actual with
  | .error code,.trapped observed => code == observed
  | .ok bits,.returned vals _ => decide (vals = [⟨ty,bits⟩])
  | _,_ => false

def sourceCases (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout) : Bool :=
  outcomeAgrees (valueType config) (caseWanted config op safe false layout) (caseRun config op safe false layout) &&
  outcomeAgrees (valueType config) (caseWanted config op safe true layout) (caseRun config op safe true layout)

theorem outcomeAgrees_sound {ty : Clif.Ty}
    {wanted : Except Clif.TrapCode (BitVec ty.width)} {actual : Clif.Outcome}
    (checked : outcomeAgrees ty wanted actual = true) :
    match (generalizing := false) wanted with
    | .error code => actual = .trapped code
    | .ok bits => ∃ mem,actual = .returned [⟨ty,bits⟩] mem := by
  cases wanted with
  | error code =>
    cases actual with
    | trapped observed =>
      change (code == observed) = true at checked
      have equal : code = observed := beq_iff_eq.mp checked
      cases equal
      rfl
    | returned vals mem => change false = true at checked; cases checked
    | stuck message => change false = true at checked; cases checked
    | outOfFuel => change false = true at checked; cases checked
  | ok bits =>
    cases actual with
    | returned vals mem =>
      change decide (vals = [Clif.Val.mk ty bits]) = true at checked
      have equal : vals = [Clif.Val.mk ty bits] := of_decide_eq_true checked
      subst vals
      exact ⟨mem,rfl⟩
    | trapped code => change false = true at checked; cases checked
    | stuck message => change false = true at checked; cases checked
    | outOfFuel => change false = true at checked; cases checked



def grid : Bool := configurations.all fun config => operations.all fun op =>
  [false,true].all fun safe => layouts.all fun layout =>
    sourceCases config op safe layout && checks config op safe layout false && checks config op safe layout true
-- witness: native_decide (288 fixed actual pipeline configurations only)
theorem checks_true : grid = true := by native_decide

end E2E.StockGeneralDivNIWitness
