import FV.Backend.Proof.StockCmpNarrowRhs
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def narrowFixtureCtx (half : Bool) : Ctx := {sinkCtx with
  valDef := #[none,none]
  valTy := #[some (.int (if half then 16 else 8)),some (.int (if half then 16 else 8))]
  valReg := #[some (.vreg 7 .int),some (.vreg 31 .int)]}
private def narrowFixtureState : State := {sinkState with base := {sinkState.base with nextVreg := 40}}
private theorem safe (half : Bool) (st : State) (x : Nat) (small : x < 2) :
    DemandAllowed (narrowFixtureCtx half) st x := by
  intro i impossible
  have choices : x = 0 ∨ x = 1 := by omega
  rcases choices with rfl | rfl <;> change none = some i at impossible <;> cases impossible
/-- Both signednesses and both narrow widths have a real guarded request,
with sparse source mappings below the newly allocated temporary. -/
theorem stock_cmp_narrow_extend_request_witness (signed half : Bool) :
    ∃ trace,(applyTerm program (Stock.sem (narrowFixtureCtx half)) {} 1000 27
      (if signed then 555 else 556) [.value 0]).run (narrowFixtureState,#[]) =
      .ok (some (.reg (.vreg 40 .int)),
        {narrowFixtureState.mark 0 with base := ((narrowFixtureState.base.fresh .int).2.emit
          (.extend (.vreg 40 .int) (.vreg 7 .int) signed (if half then 16 else 8) 32))},trace) := by
  exact stock_cmp_narrow_extend_request data_program (narrowFixtureCtx half) signed
    (by cases half <;> decide) rfl rfl narrowFixtureState (safe half _ 0 (by decide)) #[] 940
/-- Every condition and each narrow width inhabits the appropriate signed or
unsigned actual emitter RHS. This witness covers the RHS; selected retained
whole-driver/source-step witnesses are separate obligations. -/
theorem stock_cmp_narrow_rhs_witness (cc : Clif.IntCC) (half : Bool) :
    ∃ out next trace,(evalExpr program (Stock.sem (narrowFixtureCtx half)) {} 1000
      (if signedCC cc then rule_inst_5108 else rule_inst_5117).rhs
      #[some (.data 145 (ccIdx cc) []),some (.value 0),
        some (.ty (.int (if half then 16 else 8))),some (.value 1)]).run
      (narrowFixtureState,#[]) = .ok (some out,next,trace) ∧
      next.base = (narrowFixtureState.base.fresh .int).2.emit
        (.extend (.vreg 40 .int) (.vreg 7 .int) (signedCC cc) (if half then 16 else 8) 32) ∧
      next.demand = ((narrowFixtureState.mark 0).mark 1).demand := by
  obtain ⟨trace,run⟩ := stock_cmp_narrow_rhs data_program (narrowFixtureCtx half) (signedCC cc) half cc
    rfl (x := 0) (y := 1) (rx := .vreg 7 .int) (ry := .vreg 31 .int) rfl rfl
    narrowFixtureState (safe half _ 0 (by decide)) (safe half _ 1 (by decide)) #[] 840
  exact ⟨_,_,trace,run,rfl,rfl⟩
end Backend.Stock.Proof.ScalarCmp
