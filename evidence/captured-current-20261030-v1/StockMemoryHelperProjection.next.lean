import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselScopedProjectionInv

/-! Draft for the next memory batch. The current production gates exclude it. -/
namespace Backend.Stock.Proof.MemoryHelpers
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- Integer load/store helpers and their complete constructor closure. -/
def helperIds : List Nat :=
  [175,201,235,529,530,531,532,533,534,535,541,542,543,544,1787,
    1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838]

private def ruleCalls (r : Rule) : List Nat :=
  r.iflets.flatMap (fun il => exprCalls il.rhs) ++ exprCalls r.rhs

private def checkTerm (ids : List Nat) (id : Nat) : Bool :=
  match termOf program id with
  | .error _ => false
  | .ok term => !(revisedCtors.contains term.id) &&
      (program.rulesOf id).all (fun r => (ruleCalls r).all (ids.contains ·))

section Certificate
attribute [local semireducible] Isle.Aarch64.program
private theorem checked : helperIds.all (checkTerm helperIds) = true := by decide +kernel
end Certificate

private theorem valid {t : Nat} (member : t ∈ helperIds) {term : Term}
    (lookup : termOf program t = .ok term) :
    term.id ∉ revisedCtors ∧
      (program.rulesOf t).all (fun r => (ruleCalls r).all (helperIds.contains ·)) = true := by
  have fact := List.all_eq_true.mp checked t member
  have parts : (!(revisedCtors.contains term.id)) = true ∧
      (program.rulesOf t).all (fun r => (ruleCalls r).all (helperIds.contains ·)) = true := by
    simpa only [checkTerm,lookup,Bool.and_eq_true] using fact
  exact ⟨by simpa using parts.1,parts.2⟩

private theorem scope (ctx : Ctx) (original : State) :
    ProjectionScopeInv program (Backend.sem ctx) State.base
      (fun st => st = {original with base := st.base}) (Stock.externCtor ctx)
      (fun t => t ∈ helperIds) := by
  constructor
  · intro t term member lookup args st invariant
    exact stock_ctor_unchanged ctx term args st (valid member lookup).1
  · intro t term member lookup args st value next invariant ran
    rw [stock_ctor_baseOnly ctx term args st (valid member lookup).1] at ran
    cases result : Backend.externCtor ctx term args st.base with
    | fail => rw [result] at ran; cases ran
    | unmodeled error => rw [result] at ran; cases ran
    | ok pair =>
      rcases pair with ⟨out,base⟩
      rw [result] at ran
      have same := (ExtResult.ok.inj ran).2
      rw [← same]
      rw [invariant]
  · intro t term member lookup flags ex kind args r recorded
    apply Or.inl
    have calls := List.all_eq_true.mp (valid member lookup).2 r recorded
    have contains : ∀ u ∈ ruleCalls r,u ∈ helperIds := by
      intro u inside
      have yes := List.all_eq_true.mp calls u inside
      simpa using yes
    constructor
    · intro il inside u called
      exact contains u (List.mem_append_left _ (List.mem_flatMap.mpr ⟨il,inside,called⟩))
    · intro u called
      exact contains u (List.mem_append_right _ called)

/-- All integer load/store helpers retain the exact legacy evaluation and full
Stock scheduling state. The checked helper closure is internal to the proof. -/
theorem integer_helpers_project_and_preserve (ctx : Ctx) (cfg : Config)
    (overlap : cfg.checkOverlap = false) (fuel ty term : Nat)
    (member : term ∈ helperIds) (args : List V) (st : State) (trace : Array RuleId) :
    projectResult State.base ((applyTerm program (Stock.sem ctx) cfg fuel ty term args).run (st,trace)) =
      (applyTerm program (Backend.sem ctx) cfg fuel ty term args).run (st.base,trace) ∧
    ∀ value next resultTrace,
      (applyTerm program (Stock.sem ctx) cfg fuel ty term args).run (st,trace) =
        .ok (value,next,resultTrace) → next = {st with base := next.base} := by
  exact ((evaluation_scoped_restate_inv program (Backend.sem ctx) cfg overlap State.base
    (fun next => next = {st with base := next.base}) (Stock.externCtor ctx)
    (fun t v next => Backend.externExtract ctx t v next.base) (fun t => t ∈ helperIds)
    (scope ctx st) (fun _ _ _ => rfl) fuel).term ty term args member) st trace rfl

end Backend.Stock.Proof.MemoryHelpers
