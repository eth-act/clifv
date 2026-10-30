import FV.Backend.Proof.StockMinMaxRegisterRuns
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def narrowMinmaxTy (half : Bool) : Clif.Ty := if half then .i16 else .i8
def narrowMinmaxFunction (unsigned maximum half : Bool) : Clif.Function := {
  name := "stock_minmax_narrow_original"
  sig := {params := [⟨narrowMinmaxTy half,.none,.normal⟩,⟨narrowMinmaxTy half,.none,.normal⟩],returns := [⟨narrowMinmaxTy half,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,narrowMinmaxTy half),(31,narrowMinmaxTy half)],body := [⟨[100],.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31⟩],term := .ret [100]}] }
def narrowMinmaxBuilt (unsigned maximum half : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (narrowMinmaxFunction unsigned maximum half)).toOption.getD (sinkCtx,#[],sinkState)
def narrowConstantLiteral (half large : Bool) : Nat := if large then (if half then 4097 else 129) else 3
def narrowConstantFunction (unsigned maximum half left large : Bool) : Clif.Function := {
  name := "stock_minmax_wide_constant_original"
  sig := {params := [⟨narrowMinmaxTy half,.none,.normal⟩],returns := [⟨narrowMinmaxTy half,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(31,narrowMinmaxTy half)],body := [
    ⟨[7],.iconst (narrowMinmaxTy half) (BitVec.ofNat (narrowMinmaxTy half).width (narrowConstantLiteral half large))⟩,
    ⟨[100],.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) (if left then 7 else 31) (if left then 31 else 7)⟩],term := .ret [100]}] }
def narrowConstantBuilt (unsigned maximum half left large : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (narrowConstantFunction unsigned maximum half left large)).toOption.getD (sinkCtx,#[],sinkState)
def narrowConstantTarget (_half _large : Bool) : Nat := 197
def narrowBothConstantFunction (unsigned maximum half : Bool) : Clif.Function := {
  name := "stock_minmax_wide_both_constant_original"
  sig := {returns := [⟨narrowMinmaxTy half,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [
    ⟨[7],.iconst (narrowMinmaxTy half) (BitVec.ofNat (narrowMinmaxTy half).width 3)⟩,
    ⟨[31],.iconst (narrowMinmaxTy half) (BitVec.ofNat (narrowMinmaxTy half).width (narrowConstantLiteral half true))⟩,
    ⟨[100],.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31⟩],term := .ret [100]}] }
def narrowBothConstantBuilt (unsigned maximum half : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (narrowBothConstantFunction unsigned maximum half)).toOption.getD (sinkCtx,#[],sinkState)
def narrowBothConstantTargetX (_half : Bool) : Nat := 198
def narrowBothConstantTargetY (_half : Bool) : Nat := 197
end Backend.Stock.Proof.ScalarSelect
