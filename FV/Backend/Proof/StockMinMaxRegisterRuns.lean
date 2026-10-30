import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.PrepareCheck
namespace Backend.Stock.Proof.ScalarSelect.MinMaxRegisterFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def minmaxOperation (unsigned maximum : Bool) : Clif.BinaryOp :=
  if unsigned then (if maximum then .umax else .umin) else (if maximum then .smax else .smin)
def minmaxComparison (unsigned maximum : Bool) : Clif.IntCC :=
  if unsigned then (if maximum then .ugt else .ult) else (if maximum then .sgt else .slt)
def minmaxFunction (unsigned maximum : Bool) : Clif.Function := {
  name := "stock_minmax_register_original"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [⟨[100],.binary (minmaxOperation unsigned maximum) .i64 7 31⟩],term := .ret [100]}] }
def minmaxBuilt (unsigned maximum : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (minmaxFunction unsigned maximum)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- All four original scalar64 min/max functions complete the actual Stock driver. -/
theorem stock_minmax_register_driver_success (unsigned maximum : Bool) :
    (Stock.lower (minmaxFunction unsigned maximum)).isOk = true := by
  cases unsigned <;> cases maximum <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarSelect.MinMaxRegisterFixture
