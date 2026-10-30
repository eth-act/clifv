import FV.Backend.Proof.StockDivRootMatch
namespace Backend.Stock.Proof.ScalarDiv.RhsWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def Supported (ty : Clif.Ty) := ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64
private def function (op : Clif.DivOp) (ty : Clif.Ty) (literal : Int) : Clif.Function := {
  name := "stock_div_rhs_original_context"
  sig := {params := [⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty)],body := [⟨[31],.iconst ty (BitVec.ofInt ty.width literal)⟩,
    ⟨[100],.div op ty 7 31⟩],term := .ret [100]}] }
private def built (op : Clif.DivOp) (ty : Clif.Ty) (literal : Int) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function op ty literal)).toOption.getD (sinkCtx,#[],sinkState)
private def rule (op : Clif.DivOp) (ty : Clif.Ty) (literal : Int) : Rule :=
  if op = .sdiv ∧ literal = 9 then
    if ty.width = 64 then rule_lower_1163 else rule_lower_1167
  else if ty.width = 64 then baseWideRule op else baseNarrowRule op
private def observed (op : Clif.DivOp) (ty : Clif.Ty) (literal : Int) : Option Bool := do
  let (env,st,tr) ← ((matchRule program (Stock.sem (built op ty literal).1) {} 200
    (rule op ty literal) [.inst 1]).run ((built op ty literal).2.2,#[])).toOption
  let env ← env
  let (out,_,_) ← ((evalExpr program (Stock.sem (built op ty literal).1) {} 200
    (rule op ty literal).rhs env).run (st,tr)).toOption
  return out.isSome
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem observed_run (op : Clif.DivOp) (ty : Clif.Ty) (literal : Int)
    (supported : Supported ty) (values : literal = 0 ∨ literal = 9) : observed op ty literal = some true := by
  cases op <;> rcases supported with rfl | rfl | rfl | rfl <;> rcases values with rfl | rfl <;> decide +kernel
end Kernel
/-- All ten actual division/remainder roots have successful matcher and RHS
runs in original sparse-ID Stock contexts, including zero falling through to
guards and nonzero safe signed constants. These are RHS witnesses; complete
retained/source execution is a separate obligation. -/
theorem stock_div_actual_rhs_witness (op : Clif.DivOp) (ty : Clif.Ty) (literal : Int)
    (supported : Supported ty) (values : literal = 0 ∨ literal = 9) :
    ∃ env matched matchTrace out next trace,
      (matchRule program (Stock.sem (built op ty literal).1) {} 200 (rule op ty literal) [.inst 1]).run
        ((built op ty literal).2.2,#[]) = .ok (some env,matched,matchTrace) ∧
      (evalExpr program (Stock.sem (built op ty literal).1) {} 200 (rule op ty literal).rhs env).run
        (matched,matchTrace) = .ok (some out,next,trace) := by
  have actual := observed_run op ty literal supported values
  unfold observed at actual
  cases hm : (matchRule program (Stock.sem (built op ty literal).1) {} 200 (rule op ty literal) [.inst 1]).run
    ((built op ty literal).2.2,#[]) with
  | error err => simp [hm,Except.toOption,Option.bind] at actual
  | ok result =>
    obtain ⟨env,matched,matchTrace⟩ := result
    cases env with
    | none => simp [hm,Except.toOption,Option.bind] at actual
    | some env =>
      cases he : (evalExpr program (Stock.sem (built op ty literal).1) {} 200 (rule op ty literal).rhs env).run
        (matched,matchTrace) with
      | error err => simp [hm,he,Except.toOption,Option.bind] at actual
      | ok result =>
        obtain ⟨out,next,trace⟩ := result
        cases out with
        | none => simp [hm,he,Except.toOption,Option.bind] at actual
        | some out => exact ⟨env,matched,matchTrace,out,next,trace,rfl,he⟩
end Backend.Stock.Proof.ScalarDiv.RhsWitness
