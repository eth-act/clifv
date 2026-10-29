module

public import FV.Backend.Proof.StockAddSubNegativeMatch

@[expose] public section

namespace Backend.Stock.Proof.ScalarAddSub.AuxWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def function : Clif.Function := {
  name := "stock_addsub_negative_helper_projection"
  sig := {params := [],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [⟨[31],.iconst .i64 (BitVec.ofInt 64 (-5))⟩],term := .ret [31]}] }
private def ctx : Ctx := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState) |>.1
private def state : State := {sinkState with demand := #[2,1],sunk := #[true,false]}
/-- The auxiliary pure-term projection has an actual successful negative
constant execution, preserving an inhabited nonzero scheduling state. -/
theorem stock_addsub_negative_projection_witness :
    ∃ (context : Ctx) (st : State) (trace : Array RuleId),st.demand = #[2,1] ∧ st.sunk = #[true,false] ∧
      (applyTerm program (Stock.sem context) {} 30 64 344 [.value 31]).run (st,#[88]) =
        .ok (some (.op (.imm12 ⟨5,false⟩)),st,trace) ∧
      (applyTerm program (Backend.sem context) {} 30 64 344 [.value 31]).run (st.base,#[88]) =
        .ok (some (.op (.imm12 ⟨5,false⟩)),st.base,trace) := by
  have defined : ctx.defInst? 31 = some 0 := rfl
  have found : ctx.insts[0]? = some (ctx.insts[0]!) := rfl
  have type : (ctx.insts[0]!).resTys.head? = some (.int 64) := rfl
  have data : (ctx.insts[0]!).data = .data 152 35 [.data 151 57 [],.int (-5)] := rfl
  have actual := stock_addsub_neg_helper data_program ctx defined found type data state #[88] 0
  have choice : negImm12? 64 (-5) = some ⟨5,false⟩ := by decide +kernel
  simp only [choice,Option.map_some,Option.isSome_some,ite_true,Nat.zero_add] at actual
  have projected := Negative.stock_addsub_negative_project data_program ctx (by decide) actual
  exact ⟨ctx,state,#[88].push rule_inst_2404.id,rfl,rfl,actual,projected⟩
end Backend.Stock.Proof.ScalarAddSub.AuxWitness
