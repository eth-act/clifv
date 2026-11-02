import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen

namespace Backend.Stock.Proof.PureHelper
open Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

def ruleCalls (r : Rule) : List Nat :=
  r.iflets.flatMap (fun il => exprCalls il.rhs) ++ exprCalls r.rhs

/-- A finite helper closure may use only the unchanged constructors. -/
def checkTerm (p : Program) (ids : List Nat) (id : Nat) : Bool :=
  match termOf p id with
  | .error _ => false
  | .ok term => !revisedCtors.contains term.id &&
      (p.rulesOf id).all (fun r => (ruleCalls r).all (ids.contains ·))

private theorem valid {p : Program} {ids : List Nat}
    (checked : ids.all (checkTerm p ids) = true) {t : Nat} (member : t ∈ ids)
    {term : Term} (lookup : termOf p t = .ok term) :
    term.id ∉ revisedCtors ∧
      (p.rulesOf t).all (fun r => (ruleCalls r).all (ids.contains ·)) = true := by
  have fact := List.all_eq_true.mp checked t member
  have parts : (!revisedCtors.contains term.id) = true ∧
      (p.rulesOf t).all (fun r => (ruleCalls r).all (ids.contains ·)) = true := by
    simpa only [checkTerm,lookup,Bool.and_eq_true] using fact
  exact ⟨by simpa using parts.1,parts.2⟩

private def frameCtor (ctx : Ctx) (t : Term) (vs : List V) (st : State) : ExtResult (V × State) :=
  match Backend.externCtor ctx t vs st.base with
  | .ok (v,base) => .ok (v,{st with base})
  | .fail => .fail
  | .unmodeled e => .unmodeled e

private def frameSem (ctx : Ctx) : Isle.Sem V State :=
  (Backend.sem ctx).restate (frameCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base)

def scheduling (st : State) : State := {st with base := default}

private theorem rules_closed {p : Program} {ids : List Nat}
    (checked : ids.all (checkTerm p ids) = true) {t : Nat} (member : t ∈ ids)
    {term : Term} (lookup : termOf p t = .ok term) {r : Rule} (recorded : r ∈ p.rulesOf t) :
    RuleScoped (· ∈ ids) r := by
  have calls := List.all_eq_true.mp (valid checked member lookup).2 r recorded
  have contains : ∀ u ∈ ruleCalls r,u ∈ ids := by
    intro u inside
    simpa using List.all_eq_true.mp calls u inside
  constructor
  · intro il inside u called
    exact contains u (List.mem_append_left _ (List.mem_flatMap.mpr ⟨il,inside,called⟩))
  · intro u called
    exact contains u (List.mem_append_right _ called)

private theorem base_scope {p : Program} {ids : List Nat}
    (checked : ids.all (checkTerm p ids) = true) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx) (· ∈ ids) := by
  constructor
  · intro t term member lookup vs st
    exact stock_ctor_unchanged ctx term vs st (valid checked member lookup).1
  · intro t term member lookup flags ex kind r recorded
    exact rules_closed checked member lookup recorded

private theorem frame_scope {p : Program} {ids : List Nat}
    (checked : ids.all (checkTerm p ids) = true) (ctx : Ctx) :
    ProjectionScope p (frameSem ctx) id (Stock.externCtor ctx) (· ∈ ids) := by
  constructor
  · intro t term member lookup vs st
    rw [stock_ctor_baseOnly ctx term vs st (valid checked member lookup).1]
    change projectCtor id (frameCtor ctx term vs st) = frameCtor ctx term vs st
    unfold frameCtor
    cases Backend.externCtor ctx term vs st.base with
    | ok pair => cases pair; rfl
    | fail => rfl
    | unmodeled e => rfl
  · intro t term member lookup flags ex kind r recorded
    exact rules_closed checked member lookup recorded

/-- A checked, unchanged helper closure projects every actual Stock execution
onto the original helper semantics, including its failure and output behavior. -/
theorem projects {p : Program} {ids : List Nat}
    (checked : ids.all (checkTerm p ids) = true) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) (fuel ty t : Nat) (member : t ∈ ids)
    (args : List V) (st : State) (trace : Array RuleId) :
    projectResult State.base ((applyTerm p (Stock.sem ctx) cfg fuel ty t args).run (st,trace)) =
      (applyTerm p (Backend.sem ctx) cfg fuel ty t args).run (st.base,trace) :=
  (evaluation_scoped_restate p (Backend.sem ctx) cfg overlap State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (· ∈ ids) (base_scope checked ctx) (fun _ _ _ => rfl) fuel).term ty t args member st trace

/-- The same checked closure preserves all Stock scheduling fields; only the
legacy code-generation state may change. -/
theorem preserves {p : Program} {ids : List Nat}
    (checked : ids.all (checkTerm p ids) = true) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {fuel ty t : Nat} (member : t ∈ ids)
    (args : List V) {st next : State} {before trace : Array RuleId} {out : Option V}
    (run : (applyTerm p (Stock.sem ctx) cfg fuel ty t args).run (st,before) = .ok (out,next,trace)) :
    next = {st with base := next.base} := by
  have projection := (evaluation_scoped_restate p (frameSem ctx) cfg overlap id
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (· ∈ ids) (frame_scope checked ctx) (fun _ _ _ => rfl) fuel).term ty t args member st before
  change projectResult id ((applyTerm p (Stock.sem ctx) cfg fuel ty t args).run (st,before)) =
    (applyTerm p (frameSem ctx) cfg fuel ty t args).run (st,before) at projection
  rw [run] at projection
  simp only [projectResult,id_eq] at projection
  have frame : PresAt p (frameSem ctx) cfg (fun s after => scheduling after = scheduling s) fuel := by
    apply presAt (R := fun s after => scheduling after = scheduling s)
      (fun _ => rfl) (fun _ _ _ ab bc => bc.trans ab)
    intro term vs s value after executed
    change frameCtor ctx term vs s = .ok (value,after) at executed
    unfold frameCtor at executed
    split at executed <;> cases executed
    rfl
  have held := frame.apply ty t args st before out next trace projection.symm
  have equal := congrArg (fun s => {s with base := next.base}) held
  simpa only [scheduling] using equal

/-- Replay a successful original helper call in Stock. The checked closure
supplies both existence and the complete post-state, not just a projection. -/
theorem replays {p : Program} {ids : List Nat}
    (checked : ids.all (checkTerm p ids) = true) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {fuel ty t : Nat} (member : t ∈ ids)
    (args : List V) (st : State) {base : LState} {before trace : Array RuleId} {out : Option V}
    (legacy : (applyTerm p (Backend.sem ctx) cfg fuel ty t args).run (st.base,before) =
      .ok (out,base,trace)) :
    (applyTerm p (Stock.sem ctx) cfg fuel ty t args).run (st,before) =
      .ok (out,{st with base},trace) := by
  have projection := projects checked ctx overlap fuel ty t member args st before
  rw [legacy] at projection
  cases actual : (applyTerm p (Stock.sem ctx) cfg fuel ty t args).run (st,before) with
  | error err => rw [actual] at projection; cases projection
  | ok result =>
    obtain ⟨value,next,rules⟩ := result
    rw [actual] at projection
    simp only [projectResult,Except.ok.injEq,Prod.mk.injEq] at projection
    obtain ⟨rfl,baseEq,rfl⟩ := projection
    have frame := preserves checked ctx overlap member args actual
    rw [baseEq] at frame
    rw [frame]

end Backend.Stock.Proof.PureHelper
