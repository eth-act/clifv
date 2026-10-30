import FV.E2E.ActualCompilerModes
import FV.E2E.ActualPrologueWitness

/-! Dependent whole-program non-vacuity candidate. Fixed native receipts only;
not a production selector or a universal Stock completeness proof. -/
set_option autoImplicit false
namespace E2E.ActualProgramWitness
open Backend E2E.LinkCheck E2E.ActualPrologueWitness

def clif : String :=
  "function %actual_stock_prologue(i64) -> i64 system_v {\nblock0(v0: i64):\n    nop\n    jump block1\nblock1:\n    nop\n    return v0\n}\n"
def input : LinkInput :=
  { funcs := [{clif, ra := "null"}], addrs := [("actual_stock_prologue", 4096)],
    syms := [], raStar := 8192, D := 4096, fallback := true }
def outputs (cleanup : Bool) : Res :=
  input.resultsWithLowering actualLower (stage cleanup)
def checks (cleanup : Bool) : Bool :=
  okRWith (stage cleanup) input (outputs cleanup) &&
  (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) &&
  !((artOf (outputs cleanup) input.funcs[0]!.func).vc.rulesFired ==
    (getOk (lowerFunction input.funcs[0]!.func)).rulesFired) &&
  (Stock.lower input.funcs[0]!.func).isOk &&
  ((progOf (outputs cleanup)).func? "actual_stock_prologue").isSome

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Actual Stock, actual program checks and distinct history in both modes. -/
theorem checks_true : checks false = true ∧ checks true = true := by native_decide

def world (cleanup : Bool) : BitVec 64 → Prop :=
  (ofRes input (outputs cleanup) closedBase (fun _ => False)).Img
def system (cleanup : Bool) : LinkSys :=
  ofRes input (outputs cleanup) closedBase (world cleanup)

theorem checked (cleanup : Bool) :
    okRWith (stage cleanup) input (outputs cleanup) = true ∧
    (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) = true := by
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact checks_true.1
    | true => exact checks_true.2
  simp only [checks, Bool.and_eq_true, and_assoc] at h
  exact ⟨h.1, h.2.1⟩

theorem base_ok (cleanup : Bool) : BaseOk (system cleanup) :=
  baseOk_closedR fun g hg => by
    simpa only [Bool.not_eq_true'] using
      (List.all_eq_true.mp (checked cleanup).2 g hg)

/-- The entry named by the program theorem really occurs in the actual table. -/
theorem entry_present (cleanup : Bool) :
    ∃ f, (system cleanup).P.func? "actual_stock_prologue" = some f := by
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact checks_true.1
    | true => exact checks_true.2
  simp only [checks, Bool.and_eq_true, and_assoc] at h
  exact Option.isSome_iff_exists.mp h.2.2.2.2

/-- All39 fields of the actual-output whole-program contract are jointly
inhabited, using the code image as world rather than all memory addresses. -/
theorem system_ok (cleanup : Bool) : (system cleanup).OkProduction := by
  have stages : stage cleanup = (fun _ => id) ∨ stage cleanup = (fun _ => DeadCleanup.prune) := by
    cases cleanup with
    | false => exact .inl rfl
    | true => exact .inr rfl
  exact input.resultsWithLowering_sound actualLower (stage cleanup) stages
    (checked cleanup).1 (base_ok cleanup) (fun _ h => h)

/-- The actual callback's program theorem, with its ordinary run premises,
applies to this non-legacy-history Stock program in both modes. -/
theorem program_correct (cleanup : Bool) :
    CrateStmtWithCompilerModes input actualLower (stage cleanup) "actual_stock_prologue" := by
  have stages : stage cleanup = (fun _ => id) ∨ stage cleanup = (fun _ => DeadCleanup.prune) := by
    cases cleanup with
    | false => exact .inl rfl
    | true => exact .inr rfl
  exact crate_correct_withCompilerModes input actualLower (stage cleanup) stages
    (checked cleanup).1 _
end E2E.ActualProgramWitness
