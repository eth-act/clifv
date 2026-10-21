import FV.Backend.Proof.StockBitHelper
namespace Backend.Stock.Proof.UnchangedHelper
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

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
  change frameCtor ctx t vs st = .ok (v,next) at run
  unfold frameCtor at run
  split at run <;> cases run
  rfl

/-- Reuse existing helper inversions while retaining every Stock scheduling field.
Only constructor agreement and the existing finite call-graph closure are required. -/
theorem observe {p : Program} (ctx : Ctx) {allowed : Nat → Prop}
    (safe : ∀ t term, allowed t → termOf p t = .ok term → term.id ∉ revisedCtors)
    (closed : ∀ t term, allowed t → termOf p t = .ok term →
      ∀ flags ex, term.kind = .decl flags (some .internal) ex →
        ∀ r ∈ p.rulesOf t,RuleScoped allowed r)
    {cfg : Config} (hc : cfg.checkOverlap = false) {fuel ty t : Nat} {vs : List V}
    (member : allowed t) {st next : State} {tr trace : Array RuleId} {v : Option V}
    (actual : (applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st,tr) = .ok (v,next,trace)) :
    (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base,tr) =
      .ok (v,next.base,trace) ∧ next = {st with base := next.base} := by
  have scope : ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx) allowed :=
    ⟨fun t term member lookup vs st => stock_ctor_unchanged ctx term vs st (safe t term member lookup),closed⟩
  have framedScope : ProjectionScope p (frameSem ctx) id (Stock.externCtor ctx) allowed := by
    constructor
    · intro t term member lookup vs st
      change projectCtor id (Stock.externCtor ctx term vs st) = frameCtor ctx term vs st
      rw [stock_ctor_baseOnly ctx term vs st (safe t term member lookup)]
      unfold frameCtor
      cases Backend.externCtor ctx term vs st.base <;> rfl
    · exact closed
  have projection := (evaluation_scoped_restate p (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    allowed scope (fun _ _ _ => rfl) fuel).term ty t vs member st tr
  change projectResult State.base ((applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st,tr)) =
    (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base,tr) at projection
  rw [actual] at projection
  have projected : (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base,tr) =
      .ok (v,next.base,trace) := projection.symm
  have framed := (evaluation_scoped_restate p (frameSem ctx) cfg hc id
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    allowed framedScope (fun _ _ _ => rfl) fuel).term ty t vs member st tr
  change projectResult id ((applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st,tr)) =
    (applyTerm p (frameSem ctx) cfg fuel ty t vs).run (st,tr) at framed
  rw [actual] at framed
  simp only [projectResult,id_eq] at framed
  have preserved := (frame_presAt p ctx cfg fuel).apply ty t vs st tr v next trace framed.symm
  have whole := congrArg (fun q => {q with base := next.base}) preserved
  have same : {next with base := next.base} = {st with base := next.base} := by
    simpa only [scheduling] using whole
  exact ⟨projected,by simpa using same⟩
end Backend.Stock.Proof.UnchangedHelper
