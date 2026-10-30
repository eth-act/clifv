import FV.Backend.Proof.IselData
import FV.Arm.MinTheory
import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.PrepareCheck
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def helperScope : List Nat := [164, 170, 172, 175, 201, 356, 390, 391, 426, 593, 649, 657, 1791, 1802, 1816, 1817, 1820, 1822, 1851, 1972, 1996, 1997, 2000, 2001, 2236, 2237, 2238, 2239, 2240]
private theorem helper_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx) (fun t => t ∈ helperScope) := by
  constructor
  · intro t term member lookup vs st
    simp only [helperScope,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t164] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t170] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t172] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t175] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t201] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t356] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t390] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t391] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t426] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t593] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t649] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t657] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1791] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1802] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1816] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1817] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1820] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1822] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1851] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1972] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1996] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1997] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2000] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2001] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2236] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2237] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2238] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2239] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2240] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
  · intro t term member lookup flags ex kind r recorded
    simp only [helperScope,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t164] at lookup
      cases lookup
      cases kind
    · rw [hp.t170] at lookup
      cases lookup
      cases kind
    · rw [hp.t172] at lookup
      cases lookup
      rw [hp.r172] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_prelude_lower_105]
    · rw [hp.t175] at lookup
      cases lookup
      cases kind
    · rw [hp.t201] at lookup
      cases lookup
      cases kind
    · rw [hp.t356] at lookup
      cases lookup
      cases kind
    · rw [hp.t390] at lookup
      cases lookup
      rw [hp.r390] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_2767]
    · rw [hp.t391] at lookup
      cases lookup
      rw [hp.r391] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_2774]
    · rw [hp.t426] at lookup
      cases lookup
      rw [hp.r426] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3068]
    · rw [hp.t593] at lookup
      cases lookup
      cases kind
    · rw [hp.t649] at lookup
      cases lookup
      rw [hp.r649] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl | rfl | rfl | rfl | rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_4954,rule_inst_4955,rule_inst_4956,rule_inst_4957,rule_inst_4959]
    · rw [hp.t657] at lookup
      cases lookup
      rw [hp.r657] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl | rfl | rfl | rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_5264,rule_inst_5265,rule_inst_5266,rule_inst_5267]
    · rw [hp.t1791] at lookup
      cases lookup
      cases kind
    · rw [hp.t1802] at lookup
      cases lookup
      cases kind
    · rw [hp.t1816] at lookup
      cases lookup
      cases kind
    · rw [hp.t1817] at lookup
      cases lookup
      cases kind
    · rw [hp.t1820] at lookup
      cases lookup
      cases kind
    · rw [hp.t1822] at lookup
      cases lookup
      cases kind
    · rw [hp.t1851] at lookup
      cases lookup
      cases kind
    · rw [hp.t1972] at lookup
      cases lookup
      cases kind
    · rw [hp.t1996] at lookup
      cases lookup
      cases kind
    · rw [hp.t1997] at lookup
      cases lookup
      cases kind
    · rw [hp.t2000] at lookup
      cases lookup
      cases kind
    · rw [hp.t2001] at lookup
      cases lookup
      cases kind
    · rw [hp.t2236] at lookup
      cases lookup
      cases kind
    · rw [hp.t2237] at lookup
      cases lookup
      cases kind
    · rw [hp.t2238] at lookup
      cases lookup
      cases kind
    · rw [hp.t2239] at lookup
      cases lookup
      cases kind
    · rw [hp.t2240] at lookup
      cases lookup
      cases kind
private def frameCtor (ctx : Ctx) (t : Term) (vs : List V) (st : State) : ExtResult (V × State) :=
  match Backend.externCtor ctx t vs st.base with
  | .ok (v, base) => .ok (v, {st with base})
  | .fail => .fail
  | .unmodeled e => .unmodeled e
private def frameSem (ctx : Ctx) : Isle.Sem V State :=
  (Backend.sem ctx).restate (frameCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base)
private def scheduling (st : State) : State := {st with base := default}
private theorem frame_presAt (p : Program) (ctx : Ctx) (cfg : Config) (n : Nat) :
    PresAt p (frameSem ctx) cfg (fun st next => scheduling next = scheduling st) n := by
  apply presAt (R := fun st next => scheduling next = scheduling st)
    (fun _ => rfl) (fun _ _ _ ab bc => bc.trans ab)
  intro t vs st v next run
  change frameCtor ctx t vs st = .ok (v, next) at run
  unfold frameCtor at run
  split at run <;> cases run
  rfl
private theorem frame_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (frameSem ctx) id (Stock.externCtor ctx) (fun t => t ∈ helperScope) := by
  constructor
  · intro t term member lookup vs st
    have unchanged : term.id ∉ revisedCtors := by
      simp only [helperScope,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hp.t164] at lookup
        cases lookup
        decide
      · rw [hp.t170] at lookup
        cases lookup
        decide
      · rw [hp.t172] at lookup
        cases lookup
        decide
      · rw [hp.t175] at lookup
        cases lookup
        decide
      · rw [hp.t201] at lookup
        cases lookup
        decide
      · rw [hp.t356] at lookup
        cases lookup
        decide
      · rw [hp.t390] at lookup
        cases lookup
        decide
      · rw [hp.t391] at lookup
        cases lookup
        decide
      · rw [hp.t426] at lookup
        cases lookup
        decide
      · rw [hp.t593] at lookup
        cases lookup
        decide
      · rw [hp.t649] at lookup
        cases lookup
        decide
      · rw [hp.t657] at lookup
        cases lookup
        decide
      · rw [hp.t1791] at lookup
        cases lookup
        decide
      · rw [hp.t1802] at lookup
        cases lookup
        decide
      · rw [hp.t1816] at lookup
        cases lookup
        decide
      · rw [hp.t1817] at lookup
        cases lookup
        decide
      · rw [hp.t1820] at lookup
        cases lookup
        decide
      · rw [hp.t1822] at lookup
        cases lookup
        decide
      · rw [hp.t1851] at lookup
        cases lookup
        decide
      · rw [hp.t1972] at lookup
        cases lookup
        decide
      · rw [hp.t1996] at lookup
        cases lookup
        decide
      · rw [hp.t1997] at lookup
        cases lookup
        decide
      · rw [hp.t2000] at lookup
        cases lookup
        decide
      · rw [hp.t2001] at lookup
        cases lookup
        decide
      · rw [hp.t2236] at lookup
        cases lookup
        decide
      · rw [hp.t2237] at lookup
        cases lookup
        decide
      · rw [hp.t2238] at lookup
        cases lookup
        decide
      · rw [hp.t2239] at lookup
        cases lookup
        decide
      · rw [hp.t2240] at lookup
        cases lookup
        decide
    rw [stock_ctor_baseOnly ctx term vs st unchanged]
    change projectCtor id (frameCtor ctx term vs st) = frameCtor ctx term vs st
    unfold frameCtor
    cases Backend.externCtor ctx term vs st.base <;> rfl
  · exact (helper_scope hp ctx).rules
theorem stock_cmp_pure_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel ty t : Nat} {vs : List V} (allowed : t ∈ helperScope)
    {st : State} {base : LState} {tr trace : Array RuleId} {v : Option V}
    (legacy : (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base, tr) = .ok (v, base, trace)) :
    (applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr) =
      .ok (v, {st with base}, trace) := by
  have projection := (evaluation_scoped_restate p (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ helperScope) (helper_scope hp ctx) (fun _ _ _ => rfl) fuel).term ty t vs allowed st tr
  change projectResult State.base ((applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr)) =
    (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base, tr) at projection
  rw [legacy] at projection
  cases actual : (applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr) with
  | error err => rw [actual] at projection; cases projection
  | ok output =>
    obtain ⟨out, next, rules⟩ := output
    rw [actual] at projection
    simp only [projectResult, Except.ok.injEq, Prod.mk.injEq] at projection
    obtain ⟨rfl, baseEq, rfl⟩ := projection
    have framed := (evaluation_scoped_restate p (frameSem ctx) cfg hc id
      (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
      (fun t => t ∈ helperScope) (frame_scope hp ctx) (fun _ _ _ => rfl) fuel).term ty t vs allowed st tr
    change projectResult id ((applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr)) =
      (applyTerm p (frameSem ctx) cfg fuel ty t vs).run (st, tr) at framed
    rw [actual] at framed
    simp only [projectResult, id_eq] at framed
    have preserved := (frame_presAt p ctx cfg fuel).apply ty t vs st tr out next rules framed.symm
    have whole := congrArg (fun q => {q with base := base}) preserved
    have whole' : {next with base} = {st with base} := by simpa only [scheduling] using whole
    have eta : {next with base} = next := by rw [← baseEq]
    have nextEq : next = {st with base} := by rw [eta] at whole'; exact whole'
    rw [nextEq]


end Backend.Stock.Proof.ScalarCmp
