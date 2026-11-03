import FV.Backend.SemanticNICheck

namespace Backend.Stock.Acquire
open Backend.Proof.Driver
set_option autoImplicit false

/-- This new source class permits a general straight-line read/extend sequence.
Original scope checking supplies type, SSA, dominance and ABI conditions. -/
def bodyEligible (stmt : Clif.Stmt) : Bool :=
  match stmt.inst with
  | .atomicLoad _ _ _ | .extend _ _ _ => true
  | _ => false

def hasAcquire (stmt : Clif.Stmt) : Bool :=
  match stmt.inst with
  | .atomicLoad _ _ _ => true
  | _ => false

def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [block] => block.body.all bodyEligible && block.body.any hasAcquire &&
      (match block.term with | .ret _ => true | _ => false)
  | _ => false

/-- Keep all widths, flags, parameter locations and sequence lengths allowed by original scope. -/
def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- Validate actual compiler output. No source theorem is supplied by the caller. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) &&
      result.edgeArgs.all (fun row => row.all (·.isEmpty))

/-- Preserve every accepted semantic branch before considering the new acquire branch. -/
def extendedCheck (f : Clif.Function) (vc : VCode) : Bool :=
  SemanticNI.check f vc || check f vc

theorem previous_check {f : Clif.Function} {vc : VCode}
    (accepted : SemanticNI.check f vc = true) : extendedCheck f vc = true := by
  simp [extendedCheck,accepted]

theorem previous_exact {f : Clif.Function} {vc : VCode}
    (absent : check f vc = false) : extendedCheck f vc = SemanticNI.check f vc := by
  simp [extendedCheck,absent]

private def acquireOr (f : Clif.Function) (fallback : Except String VCode) : Except String VCode :=
  if sourceOk f then
    match Stock.lower f with
    | .error _ => fallback
    | .ok result =>
      if result.edgeArgs.all (fun row => row.all (·.isEmpty)) then .ok result.code else fallback
  else fallback

/-- Retain every previous accepted output and preserve all earlier fallback results. -/
def lowerCandidateWith (previous : Clif.Function → Except String VCode) (f : Clif.Function) : Except String VCode :=
  let old := previous f
  match old with
  | .ok vc => if SemanticNI.check f vc then .ok vc else acquireOr f old
  | .error _ => acquireOr f old

theorem previous_output_exact {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (observed : previous f = .ok vc)
    (accepted : SemanticNI.check f vc = true) : lowerCandidateWith previous f = .ok vc := by
  simp only [lowerCandidateWith,observed,accepted,ite_true]

end Backend.Stock.Acquire
