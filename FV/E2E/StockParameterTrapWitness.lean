import FV.E2E.CompiledSemanticNI
import FV.E2E.StockParameterCfgFixtures
import FV.E2E.StockNarrowChecks
import FV.Backend.Lowering.StockParameterCfgNI

/-! Production witness of the parameter CFG route on CFGs with a `trap` leaf: the existing
parameter fixtures (a later block branches on an inherited parameter; jump copies, shared joins)
with their first return block ending in `trap`, in every calling convention and both cleanup
modes. The fixed checks run the actual classifier, Stock lowering, paired
checks, `lowerValidated`, preparation, allocation, physical lowering and emission. -/

namespace E2E.StockParameterTrapNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

abbrev conventions := StockNarrowNIWitness.conventions

/-- The first twenty parameter fixtures with their first return block ending in `trap (user 8)`;
later return blocks still return. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  ((StockParameterCfgNIWitness.functions config).take 20).map fun (f,ty) =>
    let first := f.blocks.findIdx fun b => match b.term with | .ret _ => true | _ => false
    let blocks := f.blocks.zipIdx.map fun (b,i) => if i == first then {b with term := .trap (.user 8)} else b
    ({f with name := f.name ++ "_trap",blocks := blocks},ty)

/-- The narrow fixture frame, with the arguments bound to the actual (renamed) entry parameters. -/
def entryFrame (f : Clif.Function) (ty : Clif.Ty) (input : Nat → BitVec ty.width) (slot : Nat) : Clif.Frame := {
  func := f
  regs := (Clif.Regs.empty.setMany (f.blocks[0]!.params.map (·.1))
    (StockNarrowNIWitness.arguments ty input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := f.blocks[0]!.body
  term := f.blocks[0]!.term }

/-- The source run, with enough fuel for every block. -/
def sourceRun (f : Clif.Function) (ty : Clif.Ty) (sample : Nat) : Clif.Outcome :=
  Clif.runLoop Clif.Env.empty {funcs := []} 64
    ⟨entryFrame f ty (StockNarrowNIWitness.caseInput ty sample) 4096,[],Clif.Mem.empty⟩

def checks (f : Clif.Function) (cleanup : Bool) : Bool :=
  Stock.ParameterCfg.sourceOk f &&
  match Stock.lower f with
  | .error _ => false
  | .ok result =>
    ABIReadCfg.check f.sig result.code && Stock.ParameterCfg.check f result.code &&
    SemanticNI.check f result.code &&
    (match Stock.ParameterCfg.lowerValidated f with
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

/-- Every fixture completes; some run reaches the trap leaf with its code, and some run returns. -/
def sourceCases : Bool := conventions.all fun config =>
  ((functions config).all fun (f,ty) =>
    [0,1,2].all fun sample => StockNarrowNIWitness.completed (sourceRun f ty sample)) &&
  ((functions config).any fun (f,ty) =>
    [0,1,2].any fun sample => StockNarrowNIWitness.trapped (.user 8) (sourceRun f ty sample)) &&
  (functions config).any fun (f,ty) =>
    [0,1,2].any fun sample => StockNarrowNIWitness.returned (sourceRun f ty sample)

-- witness: native_decide (fixed actual pipelines and source runs only)
theorem checks_true : (grid && sourceCases) = true := by native_decide

/-- Extract complete artifacts from the same checks used by the fixed grid. -/
theorem compiled_of_checks {f : Clif.Function} {cleanup : Bool} (checked : checks f cleanup = true) :
    Stock.Scalar.Domain f ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI f 0 result.code vcp rf af fa fb ∧
      Stock.ParameterCfg.lowerValidated f = .ok result.code ∧
      ABIReadCfg.check f.sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  simp only [checks,Bool.and_eq_true] at checked
  obtain ⟨source,h⟩ := checked
  have domain := Stock.ParameterCfg.source_ok_sound source
  refine ⟨domain,?_⟩
  cases lowered : Stock.lower f with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨reads,conditional⟩,semantic⟩,actual⟩,h⟩ := h
    have actualLower : Stock.ParameterCfg.lowerValidated f = .ok result.code := by
      cases observed : Stock.ParameterCfg.lowerValidated f with
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
                CompiledSemanticNI.of_checks semantic prepared prepOk check physical emitted emittedLayout,
                actualLower,reads,allocated,(formsCoveredB_iff _ _).mp covered⟩

/-- Each fixed parameter CFG with a `trap` leaf has the scalar production domain, the actual
raw Stock artifact, preparation, checked allocation, physical lowering, byte emission and
semantic consumer certificate, in both cleanup modes. -/
theorem compiled_cases {config : Configuration} (configuration : config ∈ conventions)
    {f : Clif.Function} {ty : Clif.Ty} (member : (f,ty) ∈ functions config) (cleanup : Bool) :
    Stock.Scalar.Domain f ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI f 0 result.code vcp rf af fa fb ∧
      Stock.ParameterCfg.lowerValidated f = .ok result.code ∧
      ABIReadCfg.check f.sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have fixed := checks_true
  simp only [Bool.and_eq_true] at fixed
  have row := List.all_eq_true.mp fixed.1 config configuration
  have row := List.all_eq_true.mp row (f,ty) member
  simp only [Bool.and_eq_true] at row
  have checked : checks f cleanup = true := by cases cleanup <;> first | exact row.2 | exact row.1
  exact compiled_of_checks checked

end E2E.StockParameterTrapNIWitness
