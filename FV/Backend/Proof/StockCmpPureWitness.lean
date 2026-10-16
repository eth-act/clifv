import FV.Backend.Proof.StockCmpPure
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
inductive PureCase where
  | compareRegs | compareImmediate | conditionalSet | invertZero | extendSigned | outputRegister
  deriving DecidableEq
private def caseTerm : PureCase → Nat
  | .compareRegs => 390 | .compareImmediate => 391 | .conditionalSet => 426
  | .invertZero => 649 | .extendSigned => 657 | .outputRegister => 172
private def caseType : PureCase → Nat
  | .compareRegs | .compareImmediate => 47 | .conditionalSet => 49
  | .invertZero => 123 | .extendSigned => 84 | .outputRegister => 25
private def caseArgs : PureCase → List V
  | .compareRegs => [.data 93 1 [],.reg (.vreg 7 .int),.reg (.vreg 9 .int)]
  | .compareImmediate => [.data 93 0 [],.reg (.vreg 7 .int),.op (.imm12 ⟨0,false⟩)]
  | .conditionalSet => [.data 96 Cond.eq.idx []]
  | .invertZero => [.data 123 0 [.reg (.vreg 7 .int),.data 93 0 []]]
  | .extendSigned => [.ty (.int 8),.data 56 2 []]
  | .outputRegister => [.reg (.vreg 7 .int)]
private def fixtureState : State := {sinkState with base := {sinkState.base with nextVreg := 10}}
private theorem legacy_success (fixture : PureCase) :
    ((applyTerm program (Backend.sem sinkCtx) {} 1000 (caseType fixture) (caseTerm fixture) (caseArgs fixture)).run
      (fixtureState.base,#[])).toOption.isSome = true := by
  cases fixture <;> decide +kernel
/-- Six real successful comparison/condition builders preserve all actual
Stock scheduling fields through the original legacy-to-Stock projection. -/
theorem stock_cmp_pure_helper_witness (fixture : PureCase) :
    ∃ out base trace,(applyTerm program (Backend.sem sinkCtx) {} 1000 (caseType fixture)
      (caseTerm fixture) (caseArgs fixture)).run (fixtureState.base,#[]) = .ok (out,base,trace) ∧
      (applyTerm program (Stock.sem sinkCtx) {} 1000 (caseType fixture)
        (caseTerm fixture) (caseArgs fixture)).run (fixtureState,#[]) = .ok (out,{fixtureState with base},trace) := by
  have actual := legacy_success fixture
  cases run : (applyTerm program (Backend.sem sinkCtx) {} 1000 (caseType fixture)
      (caseTerm fixture) (caseArgs fixture)).run (fixtureState.base,#[]) with
  | error err => simp only [run,Except.toOption,Option.isSome_none] at actual; cases actual
  | ok result =>
    obtain ⟨out,base,trace⟩ := result
    exact ⟨out,base,trace,rfl,stock_cmp_pure_helper data_program sinkCtx rfl (by cases fixture <;> decide) run⟩
end Backend.Stock.Proof.ScalarCmp
