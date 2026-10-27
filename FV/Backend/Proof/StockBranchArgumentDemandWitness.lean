import FV.Backend.Proof.StockBranchArgumentDemand
import FV.Backend.Proof.StockPolicy

namespace Backend.Stock.Proof.BranchDemandWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private def function : Clif.Function := {
  name := "stock_duplicate_outgoing_demand"
  sig := {callConv := some .systemV}
  blocks := [
    {id := 0,body := [⟨[2],.iconst .i8 9⟩],term := .jump ⟨1,[2,2]⟩},
    {id := 1,params := [(5,.i8),(6,.i8)],term := .ret []}] }

private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)

/-- A real context and outgoing call with duplicate source operands demonstrate
that both requests are retained, rather than collapsing to set membership. -/
theorem duplicate_argument_marks_witness :
    ∃ f ctx ranges initial next args,
      Stock.buildCtx f = .ok (ctx,ranges,initial) ∧ ctx.func = f ∧
      f.blocks[0]? = some f.blocks[0]! ∧
      (dests f.blocks[0]!.term)[0]? = some ⟨1,[2,2]⟩ ∧
      branchArgs ctx initial 0 0 = .ok (args,next) ∧
      initial.demand[2]! = 0 ∧ next.demand[2]! = 2 ∧
      next = ([2,2] : List Nat).foldl State.mark initial := by
  have build : Stock.buildCtx function = .ok built := rfl
  have func : built.1.func = function := rfl
  have call : branchArgs built.1 built.2.2 0 0 =
      .ok (#[.vreg 192 .int,.vreg 192 .int],(built.2.2.mark 2).mark 2) := rfl
  exact ⟨function,built.1,built.2.1,built.2.2,(built.2.2.mark 2).mark 2,_,
    build,func,rfl,rfl,call,rfl,rfl,stock_branchArgs_selected_marks func rfl rfl call⟩

end Backend.Stock.Proof.BranchDemandWitness
