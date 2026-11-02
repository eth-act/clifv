import FV.Backend.Proof.StockMemoryIntegerLoadSelection

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def Width.clifTy : Width → Clif.Ty
  | .w8 => .i8 | .w16 => .i16 | .w32 => .i32 | .w64 => .i64

private def flags : Clif.MemFlags := {trapCode := none}
private def fixture (width : Width) : Clif.Function := {
  name := "stock_integer_load_root"
  sig := {
    params := [⟨.i64,.none,.normal⟩]
    returns := [⟨width.clifTy,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64)]
    body := [⟨[2],.load .load width.clifTy flags 0 0⟩]
    term := .ret [2] }] }

private def built (width : Width) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (fixture width)).toOption.getD (sinkCtx,#[],sinkState)

private theorem build_ok (width : Width) : Stock.buildCtx (fixture width) = .ok (built width) := by
  cases width <;> rfl
private theorem parameter (width : Width) : (built width).1.defInst? 0 = none := by
  cases width <;> rfl
private theorem mapped (width : Width) :
    (built width).1.valueReg? 0 = some (.vreg 192 .int) := by
  cases width <;> rfl

private def rootWitnessOk (width : Width) : Bool :=
  match Stock.runTerm (built width).1 "lower" [.inst 0] (built width).2.2 with
  | .ok (some _,_,trace) => decide (trace.getLast? = some width.root.id)
  | _ => false

private theorem roots_succeed (width : Width) : rootWitnessOk width = true := by
  cases width <;> decide +kernel

/-- Actual first-match Stock selection chooses each unsigned integer load root
in a real source context with a parameter mapped to register192. -/
theorem integer_load_root_witness (width : Width) :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat))
      (st next : State) (out : V) (trace : List RuleId),
      Stock.buildCtx f = .ok (ctx,ranges,st) ∧
      ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      Stock.runTerm ctx "lower" [.inst 0] st = .ok (some out,next,trace) ∧
      trace.getLast? = some width.root.id := by
  have checked := roots_succeed width
  unfold rootWitnessOk at checked
  cases actual : Stock.runTerm (built width).1 "lower" [.inst 0] (built width).2.2 with
  | error error => rw [actual] at checked; cases checked
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    rw [actual] at checked
    cases out with
    | none => cases checked
    | some out =>
      exact ⟨fixture width,(built width).1,(built width).2.1,(built width).2.2,
        next,out,trace,build_ok width,mapped width,actual,of_decide_eq_true checked⟩

/-- Every root's forward contract has a concrete source-built context. -/
theorem integer_load_rhs_witness (width : Width) :
    ∃ (ctx : Ctx) (st : State) (trace : Array RuleId),
      ctx.defInst? 0 = none ∧ ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (evalExpr program (Stock.sem ctx) {} 120 width.root.rhs
        (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run (st,#[]) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),
          {(st.mark 0) with base := (st.base.fresh .int).2.emit (.load width.loadOp (st.base.fresh .int).1 (.unsignedOffset (.vreg 192 .int) 0) flags)},trace) := by
  obtain ⟨trace,run⟩ := stock_parameter_integer_load_rhs data_program width (built width).1
    (cfg := {}) rfl (parameter width) (mapped width) flags (built width).2.2 #[] 0
  exact ⟨(built width).1,(built width).2.2,trace,parameter width,mapped width,run⟩

end Backend.Stock.Memory.IntegerRoots
