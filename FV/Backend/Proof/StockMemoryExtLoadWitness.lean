import FV.Backend.Proof.StockMemoryExtLoadSelection

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def flags : Clif.MemFlags := {trapCode := none}
private def fixture (kind : Kind) : Clif.Function := {
  name := "stock_extending_load_root"
  sig := {
    params := [⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64)]
    body := [⟨[2],.load kind.sourceOp .i64 flags 0 0⟩]
    term := .ret [2] }] }

private def built (kind : Kind) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (fixture kind)).toOption.getD (sinkCtx,#[],sinkState)

private theorem build_ok (kind : Kind) : Stock.buildCtx (fixture kind) = .ok (built kind) := by
  cases kind <;> rfl
private theorem parameter (kind : Kind) : (built kind).1.defInst? 0 = none := by
  cases kind <;> rfl
private theorem mapped (kind : Kind) :
    (built kind).1.valueReg? 0 = some (.vreg 192 .int) := by
  cases kind <;> rfl

private def rootWitnessOk (kind : Kind) : Bool :=
  match Stock.runTerm (built kind).1 "lower" [.inst 0] (built kind).2.2 with
  | .ok (some _,_,trace) => decide (trace.getLast? = some kind.root.id)
  | _ => false

private theorem roots_succeed (kind : Kind) : rootWitnessOk kind = true := by
  cases kind <;> decide +kernel

/-- Actual first-match Stock selection chooses each signed and unsigned extending load root
in a real source context with a parameter mapped to register192. -/
theorem extending_load_root_witness (kind : Kind) :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat))
      (st next : State) (out : V) (trace : List RuleId),
      Stock.buildCtx f = .ok (ctx,ranges,st) ∧
      ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      Stock.runTerm ctx "lower" [.inst 0] st = .ok (some out,next,trace) ∧
      trace.getLast? = some kind.root.id := by
  have checked := roots_succeed kind
  unfold rootWitnessOk at checked
  cases actual : Stock.runTerm (built kind).1 "lower" [.inst 0] (built kind).2.2 with
  | error error => rw [actual] at checked; cases checked
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    rw [actual] at checked
    cases out with
    | none => cases checked
    | some out =>
      exact ⟨fixture kind,(built kind).1,(built kind).2.1,(built kind).2.2,
        next,out,trace,build_ok kind,mapped kind,actual,of_decide_eq_true checked⟩

/-- Every root's forward contract has a concrete source-built context. -/
theorem extending_load_rhs_witness (kind : Kind) :
    ∃ (ctx : Ctx) (st : State) (trace : Array RuleId),
      ctx.defInst? 0 = none ∧ ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (evalExpr program (Stock.sem ctx) {} 120 kind.root.rhs
        (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run (st,#[]) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),
          {(st.mark 0) with base := (st.base.fresh .int).2.emit (.load kind.loadOp (st.base.fresh .int).1 (.unsignedOffset (.vreg 192 .int) 0) flags)},trace) := by
  obtain ⟨trace,run⟩ := stock_parameter_extending_load_rhs data_program kind (built kind).1
    (cfg := {}) rfl (parameter kind) (mapped kind) flags (built kind).2.2 #[] 0
  exact ⟨(built kind).1,(built kind).2.2,trace,parameter kind,mapped kind,run⟩

end Backend.Stock.Memory.ExtendedRoots
