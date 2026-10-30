import FV.Backend.Proof.IselData
import FV.Arm.MinTheory
import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.PrepareCheck
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def helperScope : List Nat := [492, 493, 444, 559, 561, 562, 362, 1976, 1975, 382, 1986, 235, 1938, 349, 161, 1822, 1971, 305, 356, 327, 1854, 560, 326, 348, 2037, 351, 2043, 162, 110, 361, 1980, 324, 306, 175, 1820, 201, 1821, 111, 2028, 113, 2029, 1824]
private theorem helper_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx) (fun t => t ∈ helperScope) := by
  constructor
  · intro t term member lookup vs st
    simp only [helperScope,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t492] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t493] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t444] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t559] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t561] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t562] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t362] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1976] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1975] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t382] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1986] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t235] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1938] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t349] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t161] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1822] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1971] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t305] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t356] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t327] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1854] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t560] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t326] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t348] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2037] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t351] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2043] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t162] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t110] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t361] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1980] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t324] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t306] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t175] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1820] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t201] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1821] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t111] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2028] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t113] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2029] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1824] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
  · intro t term member lookup flags ex kind r recorded
    simp only [helperScope,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t492] at lookup
      cases lookup
      rw [hp.r492] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3389]
    · rw [hp.t493] at lookup
      cases lookup
      rw [hp.r493] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3394]
    · rw [hp.t444] at lookup
      cases lookup
      rw [hp.r444] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3182]
    · rw [hp.t559] at lookup
      cases lookup
      rw [hp.r559] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3838]
    · rw [hp.t561] at lookup
      cases lookup
      rw [hp.r561] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3861]
    · rw [hp.t562] at lookup
      cases lookup
      rw [hp.r562] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl | rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3888,rule_inst_3892]
    · rw [hp.t362] at lookup
      cases lookup
      rw [hp.r362] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_2545]
    · rw [hp.t1976] at lookup
      cases lookup
      cases kind
    · rw [hp.t1975] at lookup
      cases lookup
      cases kind
    · rw [hp.t382] at lookup
      cases lookup
      rw [hp.r382] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_2701]
    · rw [hp.t1986] at lookup
      cases lookup
      cases kind
    · rw [hp.t235] at lookup
      cases lookup
      cases kind
    · rw [hp.t1938] at lookup
      cases lookup
      cases kind
    · rw [hp.t349] at lookup
      cases lookup
      cases kind
    · rw [hp.t161] at lookup
      cases lookup
      cases kind
    · rw [hp.t1822] at lookup
      cases lookup
      cases kind
    · rw [hp.t1971] at lookup
      cases lookup
      cases kind
    · rw [hp.t305] at lookup
      cases lookup
      rw [hp.r305] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl | rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_1592,rule_inst_1593]
    · rw [hp.t356] at lookup
      cases lookup
      cases kind
    · rw [hp.t327] at lookup
      cases lookup
      cases kind
    · rw [hp.t1854] at lookup
      cases lookup
      cases kind
    · rw [hp.t560] at lookup
      cases lookup
      rw [hp.r560] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl | rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_3852,rule_inst_3853]
    · rw [hp.t326] at lookup
      cases lookup
      cases kind
    · rw [hp.t348] at lookup
      cases lookup
      cases kind
    · rw [hp.t2037] at lookup
      cases lookup
      cases kind
    · rw [hp.t351] at lookup
      cases lookup
      cases kind
    · rw [hp.t2043] at lookup
      cases lookup
      cases kind
    · rw [hp.t162] at lookup
      cases lookup
      cases kind
    · rw [hp.t110] at lookup
      cases lookup
      cases kind
    · rw [hp.t361] at lookup
      cases lookup
      rw [hp.r361] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_2537]
    · rw [hp.t1980] at lookup
      cases lookup
      cases kind
    · rw [hp.t324] at lookup
      cases lookup
      cases kind
    · rw [hp.t306] at lookup
      cases lookup
      rw [hp.r306] at recorded
      simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
      rcases recorded with rfl | rfl
      all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,argCalls,bindCalls,helperScope,rule_inst_1599,rule_inst_1600]
    · rw [hp.t175] at lookup
      cases lookup
      cases kind
    · rw [hp.t1820] at lookup
      cases lookup
      cases kind
    · rw [hp.t201] at lookup
      cases lookup
      cases kind
    · rw [hp.t1821] at lookup
      cases lookup
      cases kind
    · rw [hp.t111] at lookup
      cases lookup
      cases kind
    · rw [hp.t2028] at lookup
      cases lookup
      cases kind
    · rw [hp.t113] at lookup
      cases lookup
      cases kind
    · rw [hp.t2029] at lookup
      cases lookup
      cases kind
    · rw [hp.t1824] at lookup
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
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hp.t492] at lookup
        cases lookup
        decide
      · rw [hp.t493] at lookup
        cases lookup
        decide
      · rw [hp.t444] at lookup
        cases lookup
        decide
      · rw [hp.t559] at lookup
        cases lookup
        decide
      · rw [hp.t561] at lookup
        cases lookup
        decide
      · rw [hp.t562] at lookup
        cases lookup
        decide
      · rw [hp.t362] at lookup
        cases lookup
        decide
      · rw [hp.t1976] at lookup
        cases lookup
        decide
      · rw [hp.t1975] at lookup
        cases lookup
        decide
      · rw [hp.t382] at lookup
        cases lookup
        decide
      · rw [hp.t1986] at lookup
        cases lookup
        decide
      · rw [hp.t235] at lookup
        cases lookup
        decide
      · rw [hp.t1938] at lookup
        cases lookup
        decide
      · rw [hp.t349] at lookup
        cases lookup
        decide
      · rw [hp.t161] at lookup
        cases lookup
        decide
      · rw [hp.t1822] at lookup
        cases lookup
        decide
      · rw [hp.t1971] at lookup
        cases lookup
        decide
      · rw [hp.t305] at lookup
        cases lookup
        decide
      · rw [hp.t356] at lookup
        cases lookup
        decide
      · rw [hp.t327] at lookup
        cases lookup
        decide
      · rw [hp.t1854] at lookup
        cases lookup
        decide
      · rw [hp.t560] at lookup
        cases lookup
        decide
      · rw [hp.t326] at lookup
        cases lookup
        decide
      · rw [hp.t348] at lookup
        cases lookup
        decide
      · rw [hp.t2037] at lookup
        cases lookup
        decide
      · rw [hp.t351] at lookup
        cases lookup
        decide
      · rw [hp.t2043] at lookup
        cases lookup
        decide
      · rw [hp.t162] at lookup
        cases lookup
        decide
      · rw [hp.t110] at lookup
        cases lookup
        decide
      · rw [hp.t361] at lookup
        cases lookup
        decide
      · rw [hp.t1980] at lookup
        cases lookup
        decide
      · rw [hp.t324] at lookup
        cases lookup
        decide
      · rw [hp.t306] at lookup
        cases lookup
        decide
      · rw [hp.t175] at lookup
        cases lookup
        decide
      · rw [hp.t1820] at lookup
        cases lookup
        decide
      · rw [hp.t201] at lookup
        cases lookup
        decide
      · rw [hp.t1821] at lookup
        cases lookup
        decide
      · rw [hp.t111] at lookup
        cases lookup
        decide
      · rw [hp.t2028] at lookup
        cases lookup
        decide
      · rw [hp.t113] at lookup
        cases lookup
        decide
      · rw [hp.t2029] at lookup
        cases lookup
        decide
      · rw [hp.t1824] at lookup
        cases lookup
        decide
    rw [stock_ctor_baseOnly ctx term vs st unchanged]
    change projectCtor id (frameCtor ctx term vs st) = frameCtor ctx term vs st
    unfold frameCtor
    cases Backend.externCtor ctx term vs st.base <;> rfl
  · exact (helper_scope hp ctx).rules
theorem stock_div_pure_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
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


end Backend.Stock.Proof.ScalarDiv
