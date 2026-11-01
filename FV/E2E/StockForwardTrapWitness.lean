import FV.E2E.CompiledSemanticNI
import FV.E2E.StockForwardCfgFixtures
import FV.E2E.StockNarrowChecks
import FV.Backend.Lowering.StockForwardCfgNI

/-! Production witness of the forward CFG route on CFGs with a `trap` leaf: the existing forward
fixtures (ranked jump chains) with their return block ending in `trap`, in every calling
convention and both cleanup modes. The fixed checks run the actual classifier, Stock lowering, paired
checks, `lowerValidated`, preparation, allocation, physical lowering and emission. -/

namespace E2E.StockForwardTrapNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

abbrev conventions := StockNarrowNIWitness.conventions

/-- The first twenty forward fixtures with their return block ending in `trap (user 6)`;
scalar, division and mask bodies stay spread over four to eight blocks. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  ((StockForwardCfgNIWitness.functions config).take 20).map fun (f,ty) =>
    let blocks := f.blocks.map fun b => match b.term with
      | .ret _ => {b with term := .trap (.user 6)}
      | _ => b
    ({f with name := f.name ++ "_trap",blocks := blocks},ty)

/-- The source run, with enough fuel for every block of the chain. -/
def sourceRun (f : Clif.Function) (ty : Clif.Ty) (sample : Nat) : Clif.Outcome :=
  Clif.runLoop Clif.Env.empty {funcs := []} 64
    ⟨StockNarrowNIWitness.frame f ty (StockNarrowNIWitness.caseInput ty sample) 4096,[],Clif.Mem.empty⟩

def checks (f : Clif.Function) (cleanup : Bool) : Bool :=
  Stock.ForwardCfg.sourceOk f &&
  match Stock.lower f with
  | .error _ => false
  | .ok result =>
    ABIReadCfg.check f.sig result.code && Stock.ForwardCfg.check f result.code &&
    SemanticNI.check f result.code &&
    (match Stock.ForwardCfg.lowerValidated f with
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

def grid : Bool := conventions.all fun config =>
  (functions config).all fun (f,_) => checks f false && checks f true

/-- Every fixture completes. Some fixture reaches the trap leaf with its code at sample 1;
others trap first in a division body, which the same domain covers. -/
def sourceCases : Bool := conventions.all fun config =>
  ((functions config).all fun (f,ty) =>
    [0,1,2].all fun sample => StockNarrowNIWitness.completed (sourceRun f ty sample)) &&
  (functions config).any fun (f,ty) => StockNarrowNIWitness.trapped (.user 6) (sourceRun f ty 1)

-- witness: native_decide (fixed actual pipelines and source runs only)
theorem checks_true : (grid && sourceCases) = true := by native_decide

/-- Extract complete artifacts from the same checks used by the fixed grid. -/
theorem compiled_of_checks {f : Clif.Function} {cleanup : Bool} (checked : checks f cleanup = true) :
    Stock.Scalar.Domain f ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI f 0 result.code vcp rf af fa fb ∧
      Stock.ForwardCfg.lowerValidated f = .ok result.code ∧
      ABIReadCfg.check f.sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  simp only [checks,Bool.and_eq_true] at checked
  obtain ⟨source,h⟩ := checked
  have domain := Stock.ForwardCfg.sourceOk_sound source
  refine ⟨domain,?_⟩
  cases lowered : Stock.lower f with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨reads,conditional⟩,semantic⟩,actual⟩,h⟩ := h
    have actualLower : Stock.ForwardCfg.lowerValidated f = .ok result.code := by
      cases observed : Stock.ForwardCfg.lowerValidated f with
      | error message => simp [observed] at actual
      | ok vc =>
        simp only [observed,decide_eq_true_eq] at actual
        cases actual
        rfl
    cases prepared : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
    | error message => simp [prepared] at h
    | ok vcp =>
      simp only [prepared,Bool.and_eq_true] at h
      obtain ⟨prepOk,h⟩ := h
      cases allocated : leanAlloc vcp with
      | error message => simp [allocated] at h
      | ok rf =>
        simp only [allocated,Bool.and_eq_true] at h
        obtain ⟨checked,h⟩ := h
        cases physical : lowerRFunc vcp rf with
        | error message => simp [physical] at h
        | ok af =>
          cases emitted : emitFunc 0 af with
          | error message => simp [physical,emitted] at h
          | ok fa =>
            simp only [physical,emitted,Bool.and_eq_true] at h
            obtain ⟨covered,layoutOk⟩ := h
            cases emittedLayout : fa.layout with
            | error message => rw [emittedLayout] at layoutOk; change false = true at layoutOk; cases layoutOk
            | ok fb =>
              have check : checkAlloc vcp rf = .ok () := by
                cases check : checkAlloc vcp rf with
                | error message => rw [check] at checked; change false = true at checked; cases checked
                | ok value => cases value; rfl
              have stage : CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb :=
                ⟨lowered,prepared,prepOk,check,physical,emitted,emittedLayout⟩
              exact ⟨result,vcp,rf,af,fa,fb,stage,
                CompiledSemanticNI.cfg domain rfl reads stage,
                actualLower,reads,allocated,(formsCoveredB_iff _ _).mp covered⟩

/-- Each fixed forward CFG with a `trap` leaf has the scalar production domain, the actual
raw Stock artifact, preparation, checked allocation, physical lowering, byte emission and
semantic consumer certificate, in both cleanup modes. -/
theorem compiled_cases {config : Configuration} (configuration : config ∈ conventions)
    {f : Clif.Function} {ty : Clif.Ty} (member : (f,ty) ∈ functions config) (cleanup : Bool) :
    Stock.Scalar.Domain f ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI f 0 result.code vcp rf af fa fb ∧
      Stock.ForwardCfg.lowerValidated f = .ok result.code ∧
      ABIReadCfg.check f.sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have fixed := checks_true
  simp only [Bool.and_eq_true] at fixed
  have row := List.all_eq_true.mp fixed.1 config configuration
  have row := List.all_eq_true.mp row (f,ty) member
  simp only [Bool.and_eq_true] at row
  have checked : checks f cleanup = true := by cases cleanup <;> first | exact row.2 | exact row.1
  exact compiled_of_checks checked

end E2E.StockForwardTrapNIWitness
