import FV.Backend.Proof.IselFamALUA
import FV.Backend.Proof.StockLogicalSelected

namespace Backend.Stock.Proof.LogicalSelected
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def Kind.tag : Kind → Nat
  | .band => 4 | .bor => 2 | .bxor => 7
private def Kind.opTerm : Kind → Nat
  | .band => 1966 | .bor => 1964 | .bxor => 1969
private def Kind.argTerms (kind : Kind) : List Expr :=
  [.term 59 kind.opTerm [],.var 14 0,.var 15 1,.var 15 2]
private theorem root_rhs (kind : Kind) : kind.rule.rhs = .term 25 172 [.term 27 565 kind.argTerms] := by
  cases kind <;> rfl
private theorem arguments {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (kind : Kind) (w x y : Nat) (st : State) (tr : Array RuleId) (n : Nat) :
    (evalArgs p (Stock.sem ctx) cfg (n + 5) kind.argTerms
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st,tr) =
      .ok (some [.data 59 kind.tag [],.ty (.int w),.value x,.value y],st,tr) := by
  cases hp
  cases kind <;> isel_eval [*,Kind.argTerms,Kind.opTerm,Kind.tag] <;> rfl

/-- A typed logical root's real RHS exposes the actual helper execution and its
output wrapper, with the exact complete intermediate state and trace. -/
theorem stock_logical_rhs_helper {ctx : Ctx} (kind : Kind) {w x y : Nat}
    {st next : State} {tr rhsTrace : Array RuleId} {out : V}
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 kind.rule.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st,tr) = .ok (some out,next,rhsTrace)) :
    ∃ (a : V) (middle : State) (helperTrace : Array RuleId),
      (applyTerm program (Stock.sem ctx) {} 999996 27 565
        [.data 59 kind.tag [],.ty (.int w),.value x,.value y]).run (st,tr) = .ok (some a,middle,helperTrace) ∧
      (applyTerm program (Stock.sem ctx) {} 999998 25 172 [a]).run (middle,helperTrace) =
        .ok (some out,next,rhsTrace) := by
  rw [root_rhs] at rhs
  obtain ⟨vs,s1,a,s2,values,helper,output⟩ := rhs_output_inv (n := 999996) rhs
  rw [arguments data_program ctx {} kind w x y st tr 999991] at values
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at values
  obtain ⟨rfl,rfl,rfl⟩ := values
  exact ⟨a,s2.1,s2.2,helper,output⟩

/-- Actual complete selected logical runs inhabit the root-to-helper bridge. -/
theorem stock_logical_helper_witness (kind : Kind) :
    ∃ (ctx : Ctx) (ii : Nat) (st next middle : State) (out a : V)
      (trace : List RuleId) (rhsTrace helperTrace : Array RuleId),
      Stock.runTerm ctx "lower" [.inst ii] st = .ok (some out,next,trace) ∧
      (evalExpr program (Stock.sem ctx) {} 999999 kind.rule.rhs
        (env3 (.ty (.int 64)) (.value 7) (.value 31))).run (st,#[]) = .ok (some out,next,rhsTrace) ∧
      (applyTerm program (Stock.sem ctx) {} 999996 27 565
        [.data 59 kind.tag [],.ty (.int 64),.value 7,.value 31]).run (st,#[]) = .ok (some a,middle,helperTrace) ∧
      (applyTerm program (Stock.sem ctx) {} 999998 25 172 [a]).run (middle,helperTrace) =
        .ok (some out,next,rhsTrace) := by
  obtain ⟨result,event,record,info,step,run,scope,events,records,source,clif,recorded,
    emitted,selectedId,out,next,trace,rhsTrace,rootRun,rhsRun⟩ := stock_logical_selected_witness kind
  obtain ⟨a,middle,helperTrace,helper,output⟩ := stock_logical_rhs_helper kind rhsRun
  exact ⟨event.ctx,record.inst,scanState record.input record.inst,next,middle,out,a,trace,
    rhsTrace,helperTrace,rootRun,rhsRun,helper,output⟩

end Backend.Stock.Proof.LogicalSelected
