import FV.E2E.CompiledProduction
import FV.E2E.LoweringProvenance
import FV.E2E.DeadCleanupUnwindWitness

/-! A successful actual Stock compilation with different diagnostic history.
This fixed non-vacuity witness does not enable a production class or replace
that class's universal source/code/consumer correctness obligations. -/
set_option autoImplicit false
namespace E2E.ActualPrologueWitness
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck
open DeadCleanupUnwindWitness

def source : Clif.Function :=
  { Stock.D0.source "actual_stock_prologue" .systemVI64 [] with blocks := [
      { id := 0, params := [(0, .i64)], body := [{ inst := .nop }],
        term := .jump { block := 1, args := [] } },
      { id := 1, body := [{ inst := .nop }], term := .ret [0] }] }

/-- The fixture uses actual Stock output and retains all diagnostic history.
Only empty edge-operand vectors are admitted; branch control remains in code. -/
def actualLower (f : Clif.Function) : Except String VCode := do
  let r ← Stock.lower f
  if r.edgeArgs.all (fun row => row.all (·.isEmpty)) then
    pure (Stock.D0.compact f.name r)
  else .error "nonempty edge operands in prologue witness"

def stage (cleanup : Bool) : Clif.Function → VCode → VCode := fun _ => cond cleanup DeadCleanup.prune id
def result (cleanup : Bool) : Except String Art :=
  pipeTWithLowering actualLower (stage cleanup) source 0 4096 .null
def artifact (cleanup : Bool) : Art := getOk (result cleanup)
def legacy : VCode := (lowerFunction source).toOption.getD default

def checks (cleanup : Bool) : Bool :=
  (Stock.lower source).isOk && (result cleanup).isOk &&
  !(artifact cleanup).vc.rulesFired == legacy.rulesFired &&
  lowerCheck source (artifact cleanup).vc &&
  prepCheck (stage cleanup source (artifact cleanup).vc) (artifact cleanup).vcp &&
  (checkAlloc (artifact cleanup).vcp (artifact cleanup).rf).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Both complete Stock pipelines succeed, retain non-legacy history and pass
all source/preparation/allocation checks. A fixed test receipt only. -/
theorem checks_true : checks false = true ∧ checks true = true := by native_decide

/-- The actual artifact, with its distinct Stock history, inhabits each new
production contract. No legacy-constructor equality is assumed or fabricated. -/
theorem actual_contracts (cleanup : Bool) :
    ∃ (r : Stock.Result) (a : Art),
      Stock.lower source = .ok r ∧ result cleanup = .ok a ∧
      a.vc.rulesFired ≠ legacy.rulesFired ∧
      CompiledProduction source a.k a.vc a.vcp a.rf a.af a.fa a.fb := by
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact checks_true.1
    | true => exact checks_true.2
  simp only [checks, Bool.and_eq_true, and_assoc, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨hs, hr, hh, hl, hp, hc⟩ := h
  have run : result cleanup = .ok (artifact cleanup) := getOk_eq hr
  obtain ⟨lower, prep, rf, alloc, emit, layout, index, addr⟩ := pipeTWithLowering_spec run
  have certificate : CompiledProduction source (artifact cleanup).k
      (artifact cleanup).vc (artifact cleanup).vcp (artifact cleanup).rf
      (artifact cleanup).af (artifact cleanup).fa (artifact cleanup).fb := by
    cases cleanup with
    | false => exact .stock ⟨⟨hl, prep, hp, allocChecked_of_checkAlloc (ok_unit hc),
        alloc, emit, layout⟩, ok_unit hc⟩
    | true => exact .stockCleanup ⟨⟨hl, prep, hp, allocChecked_of_checkAlloc (ok_unit hc),
        alloc, emit, layout⟩, ok_unit hc⟩
  cases stock : Stock.lower source with
  | error e => rw [stock] at hs; cases hs
  | ok r => exact ⟨r, artifact cleanup, rfl, run, hh, certificate⟩
end E2E.ActualPrologueWitness
