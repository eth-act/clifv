import FV.E2E.StockReturnedDivFixtures
import FV.E2E.ABIReadDiv
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockScalarNI
namespace E2E.StockReturnedDivNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def checks (config : Configuration) (op : Clif.DivOp) (safe : Bool) (cleanup : Bool) : Bool :=
  lowerScopeB (function config op safe) && dominatedB (function config op safe) && sigAbiOk (function config op safe).sig &&
  match Stock.lower (function config op safe) with
  | .error _ => false
  | .ok result =>
    !lowerCheck (function config op safe) result.code &&
    DivBoundary.check (function config op safe).sig result.code &&
    Stock.Scalar.check (function config op safe) result.code && SemanticNI.check (function config op safe) result.code &&
    (match Stock.Scalar.lowerValidated (function config op safe) with
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

def caseWanted (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) :=
  let input := caseInput config positive
  Clif.Sem.div op (StockHighMulNIWitness.resultValue config input) (if safe then 2 else input 8)

def caseRun (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) : Clif.Outcome :=
  Clif.runLoop Clif.Env.empty {funcs := []} ((function config op safe).blocks[0]!.body.length+1)
    ⟨frame config op safe (caseInput config positive) 4096,[],Clif.Mem.empty⟩

def outcomeAgrees (ty : Clif.Ty) (wanted : Except Clif.TrapCode (BitVec ty.width))
    (actual : Clif.Outcome) : Bool :=
  match wanted,actual with
  | .error code,.trapped observed => code == observed
  | .ok bits,.returned vals _ => decide (vals = [⟨ty,bits⟩])
  | _,_ => false

def sourceCases (config : Configuration) (op : Clif.DivOp) (safe : Bool) : Bool :=
  outcomeAgrees (valueType config) (caseWanted config op safe false) (caseRun config op safe false) &&
  outcomeAgrees (valueType config) (caseWanted config op safe true) (caseRun config op safe true)

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
  [false,true].all fun safe => sourceCases config op safe && checks config op safe false && checks config op safe true
-- witness: native_decide (ninety-six fixed actual pipeline configurations only)
theorem checks_true : grid = true := by native_decide

end E2E.StockReturnedDivNIWitness
