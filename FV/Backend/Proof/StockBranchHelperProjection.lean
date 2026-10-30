import FV.Backend.Proof.StockProjection
import FV.Arm.MinTheory
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.IselScopedProjection

namespace Backend.Stock.Proof.BranchHelpers
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private def helperIds : List Nat := [164, 166, 169, 175, 181, 185, 201, 235, 242, 243, 251, 254, 256, 305, 318, 319, 320, 321, 327, 329, 349, 350, 351, 352, 356, 358, 359, 360, 362, 390, 391, 426, 497, 498, 501, 528, 553, 554, 661, 662, 663, 664, 665, 666, 667, 668, 670, 715, 722, 1787, 1788, 1789, 1791, 1799, 1800, 1802, 1803, 1820, 1822, 1823, 1844, 1851, 1935, 1936, 1937, 1941, 1946, 1964, 1966, 1972, 1989, 1990, 2028, 2029, 2030, 2031, 2037, 2038, 2235]
private def ruleCalls (r : Rule) : List Nat := r.iflets.flatMap (fun il => exprCalls il.rhs) ++ exprCalls r.rhs
private def checkTerm (ids : List Nat) (id : Nat) : Bool :=
  match termOf program id with
  | .error _ => false
  | .ok term => (!(revisedCtors.contains term.id) || term.id == TId.opportunistic_def) &&
      (program.rulesOf id).all (fun r => (ruleCalls r).all (ids.contains ·))

section Certificate
attribute [local semireducible] Isle.Aarch64.program
private theorem checked : helperIds.all (checkTerm helperIds) = true := by decide +kernel
end Certificate

private theorem delegate_project (st : State) (result : ExtResult (V × LState)) :
    projectCtor State.base (match result with
      | .ok (v,base) => .ok (v,{st with base})
      | .fail => .fail
      | .unmodeled e => .unmodeled e) = result := by
  cases result with
  | ok pair => cases pair; rfl
  | fail => rfl
  | unmodeled e => rfl

private def opportunityResult (ctx : Ctx) (st : State) (v : Nat) (rs : List Reg) : ExtResult (V × State) :=
  let block? := st.current.map (fun i => st.instBlock[i]!)
  let defBlock? := (ctx.defInst? v).map (fun i => st.instBlock[i]!)
  if st.demand[v]! == 0 || block?.isNone || block? != defBlock? then .ok (.op .unit,st)
  else .ok (.op .unit,{st with opportunistic := st.opportunistic.set! v (some ⟨block?.getD 0,rs,st.demand[v]!⟩)})

private theorem opportunity_eq (ctx : Ctx) (term : Term) (args : List V) (st : State)
    (id : term.id = TId.opportunistic_def) :
    Stock.externCtor ctx term args st = match args with
      | [.value v,.regs rs] => opportunityResult ctx st v rs
      | _ => match Backend.externCtor ctx term args st.base with
        | .ok (v,base) => .ok (v,{st with base})
        | .fail => .fail
        | .unmodeled e => .unmodeled e := by
  cases term with
  | mk tid name inputs ret kind pos =>
    change tid = 181 at id
    subst tid
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => cases a <;> rfl
      | cons b rest =>
        cases rest with
        | cons c rest => cases a <;> cases b <;> rfl
        | nil => cases a <;> first | rfl | (cases b <;> rfl)

private theorem opportunity_project (ctx : Ctx) (term : Term) (args : List V) (st : State)
    (id : term.id = TId.opportunistic_def) :
    projectCtor State.base (Stock.externCtor ctx term args st) = Backend.externCtor ctx term args st.base := by
  rw [opportunity_eq ctx term args st id]
  split
  · rename_i v rs
    have legacy : Backend.externCtor ctx term [.value v,.regs rs] st.base = .ok (.op .unit,st.base) := by
      cases term with
      | mk tid name inputs ret kind pos =>
        change tid = 181 at id
        subst tid
        rfl
    rw [legacy]
    unfold opportunityResult
    dsimp only
    split <;> rfl
  · exact delegate_project st (Backend.externCtor ctx term args st.base)

private theorem scope (ctx : Ctx) :
    ProjectionScope program (Backend.sem ctx) State.base (Stock.externCtor ctx) (fun t => t ∈ helperIds) := by
  have valid : ∀ t ∈ helperIds,∀ term,termOf program t = .ok term →
      (!(revisedCtors.contains term.id) || term.id == TId.opportunistic_def) = true ∧
      (program.rulesOf t).all (fun r => (ruleCalls r).all (helperIds.contains ·)) = true := by
    intro t member term lookup
    have fact := List.all_eq_true.mp checked t member
    simpa only [checkTerm,lookup,Bool.and_eq_true] using fact
  constructor
  · intro t term member lookup args st
    have constructors := (valid t member term lookup).1
    simp only [Bool.or_eq_true] at constructors
    rcases constructors with ordinary | opportunity
    · apply stock_ctor_unchanged
      simpa using ordinary
    · exact opportunity_project ctx term args st (beq_iff_eq.mp opportunity)
  · intro t term member lookup flags ex kind r recorded
    have calls := List.all_eq_true.mp (valid t member term lookup).2 r recorded
    have contains : ∀ u ∈ ruleCalls r,u ∈ helperIds := by
      intro u inside
      have yes := List.all_eq_true.mp calls u inside
      simpa using yes
    constructor
    · intro il inside u called
      exact contains u (List.mem_append_left _ (List.mem_flatMap.mpr ⟨il,inside,called⟩))
    · intro u called
      exact contains u (List.mem_append_right _ called)

/-- Exact base-state projection of every actual conditional-result branch
helper. The complete reachable helper/rule closure is checked in the kernel;
opportunistic bookkeeping is proved to leave the projected machine state alone.
No source-value, scheduling-state or helper-output certificate is assumed. -/
theorem stock_br_cond_result_projects (ctx : Ctx) (cfg : Config)
    (overlap : cfg.checkOverlap = false) (fuel : Nat) (args : List V) (st : State) (trace : Array RuleId) :
    projectResult State.base ((applyTerm program (Stock.sem ctx) cfg fuel 46 722 args).run (st,trace)) =
      (applyTerm program (Backend.sem ctx) cfg fuel 46 722 args).run (st.base,trace) := by
  exact (evaluation_scoped_restate program (Backend.sem ctx) cfg overlap State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base) (fun t => t ∈ helperIds) (scope ctx)
    (fun _ _ _ => rfl) fuel).term 46 722 args (by decide) st trace

/-- The same already-certified conditional helper closure includes its actual
side-effect emitter. Reuse its base-state projection for exact branch code. -/
theorem stock_emit_side_effect_projects (ctx : Ctx) (cfg : Config)
    (overlap : cfg.checkOverlap = false) (fuel : Nat) (args : List V) (st : State) (trace : Array RuleId) :
    projectResult State.base ((applyTerm program (Stock.sem ctx) cfg fuel 13 242 args).run (st,trace)) =
      (applyTerm program (Backend.sem ctx) cfg fuel 13 242 args).run (st.base,trace) := by
  exact (evaluation_scoped_restate program (Backend.sem ctx) cfg overlap State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base) (fun t => t ∈ helperIds) (scope ctx)
    (fun _ _ _ => rfl) fuel).term 13 242 args (by decide) st trace

end Backend.Stock.Proof.BranchHelpers
