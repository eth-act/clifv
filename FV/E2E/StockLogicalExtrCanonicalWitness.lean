import FV.E2E.StockLogicalExtrMatchWitness
import FV.Backend.Proof.StockLogicalExtrMatchReceipt

namespace E2E.StockLogicalExtrWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0 Backend.Stock.Proof
open Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def canonicalBuilt (config : Configuration) (mirrored : Bool) : Ctx × Array (Nat × Nat) × Stock.State :=
  (Stock.buildCtx (function config mirrored)).toOption.getD (sinkCtx,#[],sinkState)
private theorem canonicalBuild (config : Configuration) (mirrored : Bool) :
    Stock.buildCtx (function config mirrored) = .ok (canonicalBuilt config mirrored) := by
  cases config <;> cases mirrored <;> rfl

/-- All twelve original source contexts inhabit the canonical environment and
shift-guard theorem, using their real successful matches and unchanged inputs. -/
theorem canonical_matches (config : Configuration) (mirrored : Bool) :
    let ctx := (canonicalBuilt config mirrored).1
    let st := (canonicalBuilt config mirrored).2.2
    let ty := valueType config
    ∃ (env : Isle.Interp.Env V) (middle : Stock.State × Array RuleId)
      (first : LogicalExtr.SourceWord ctx (if mirrored then 12 else 11) (!mirrored))
      (second : LogicalExtr.SourceWord ctx (if mirrored then 11 else 12) mirrored),
      (matchRule program (Stock.sem ctx) {} 20 (LogicalExtr.extrRule mirrored) [.inst 4]).run (st,#[]) =
        .ok (some env,middle) ∧
      (ty.width = 32 ∨ ty.width = 64) ∧
      ExtrOk ty.width (if mirrored then second.amount else first.amount)
        (if mirrored then first.amount else second.amount) ∧
      env = LogicalExtr.extrEnv mirrored ty.width
        (if mirrored then second.word else first.word) (if mirrored then second.amount else first.amount)
        (if mirrored then first.word else second.word) (if mirrored then first.amount else second.amount) ∧
      middle = (st,#[]) := by
  dsimp only
  obtain ⟨info,env,middle,found,data,run,_,_⟩ := source_matches config mirrored
  have expected : ((canonicalBuilt config mirrored).1.insts[4]?).bind IInfo.clif =
      some (.binary .bor (valueType config) (if mirrored then 12 else 11) (if mirrored then 11 else 12)) := by
    cases config <;> cases mirrored <;> rfl
  change (canonicalBuilt config mirrored).1.insts[4]? = some info at found
  rw [found] at expected
  have clif : info.clif = some (.binary .bor (valueType config)
      (if mirrored then 12 else 11) (if mirrored then 11 else 12)) := expected
  have scope : LowerScope (function config mirrored) := by
    apply lowerScope_of
    cases config <;> cases mirrored <;> decide +kernel
  have inv := buildCtx_mappedInv scope (canonicalBuild config mirrored)
  obtain ⟨first,second,width,guard,envEq,stateEq⟩ :=
    LogicalExtr.match_receipt data_program inv mirrored found clif (n := 0) run
  exact ⟨env,middle,first,second,run,width,guard,envEq,stateEq⟩
end E2E.StockLogicalExtrWitness
