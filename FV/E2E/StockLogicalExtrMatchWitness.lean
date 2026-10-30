import FV.E2E.StockLogicalExtrWitness
import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockLogicalExtrMatch

namespace E2E.StockLogicalExtrWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0 Backend.Stock.Proof
open Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def built (config : Configuration) (mirrored : Bool) : Ctx × Array (Nat × Nat) × Stock.State :=
  (Stock.buildCtx (function config mirrored)).toOption.getD (sinkCtx,#[],sinkState)
private theorem build (config : Configuration) (mirrored : Bool) :
    Stock.buildCtx (function config mirrored) = .ok (built config mirrored) := by
  cases config <;> cases mirrored <;> rfl
private def matchChecks (config : Configuration) (mirrored : Bool) : Bool :=
  let ctx := (built config mirrored).1
  let st := (built config mirrored).2.2
  lowerScopeB (function config mirrored) &&
  match ctx.insts[4]? with
  | none => false
  | some info =>
    decide (info.data = .data 152 2 [.data 151 98 [],
      .values [if mirrored then 12 else 11,if mirrored then 11 else 12]]) &&
    match (matchRule program (Stock.sem ctx) {} 20 (LogicalExtr.extrRule mirrored) [.inst 4]).run (st,#[]) with
    | .ok (some _,_) => true
    | _ => false
private def matchGrid : Bool := configurations.all fun config =>
  [false,true].all fun mirrored => matchChecks config mirrored
-- witness: native_decide (twelve fixed source contexts and actual rule matches only)
theorem match_checks_true : matchGrid = true := by native_decide

/-- Each ABI/width and mirrored root has an actual successful source match
inhabiting the original two-shift/two-literal definition theorem. -/
theorem source_matches (config : Configuration) (mirrored : Bool) :
    let ctx := (built config mirrored).1
    let st := (built config mirrored).2.2
    ∃ info env middle,
      ctx.insts[4]? = some info ∧
      info.data = .data 152 2 [.data 151 98 [],
        .values [if mirrored then 12 else 11,if mirrored then 11 else 12]] ∧
      (matchRule program (Stock.sem ctx) {} 20 (LogicalExtr.extrRule mirrored) [.inst 4]).run (st,#[]) =
        .ok (some env,middle) ∧
      LogicalExtr.WordSource ctx (if mirrored then 12 else 11) (!mirrored) ∧
      LogicalExtr.WordSource ctx (if mirrored then 11 else 12) mirrored := by
  dsimp only
  have h : matchChecks config mirrored = true := by
    have allConfig := List.all_eq_true.mp match_checks_true config (by cases config <;> simp [configurations])
    exact List.all_eq_true.mp allConfig mirrored (by cases mirrored <;> simp)
  simp only [matchChecks,Bool.and_eq_true] at h
  obtain ⟨scope,h⟩ := h
  have inv := buildCtx_mappedInv (lowerScope_of scope) (build config mirrored)
  cases found : (built config mirrored).1.insts[4]? with
  | none => simp [found] at h
  | some info =>
    simp only [found,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨data,h⟩ := h
    cases run : (matchRule program (Stock.sem (built config mirrored).1) {} 20
        (LogicalExtr.extrRule mirrored) [.inst 4]).run ((built config mirrored).2.2,#[]) with
    | error message => simp [run] at h
    | ok result =>
      rcases result with ⟨value,middle⟩
      cases value with
      | none => simp [run] at h
      | some env =>
        obtain ⟨first,second⟩ := LogicalExtr.matched_sources data_program inv mirrored found data (n := 0) run
        exact ⟨info,env,middle,rfl,data,rfl,first,second⟩
end E2E.StockLogicalExtrWitness
