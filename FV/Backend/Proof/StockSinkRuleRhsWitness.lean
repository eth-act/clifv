import FV.Backend.Proof.StockNoLoadSink
import FV.Backend.Proof.StockSinkRuleRhs

namespace Backend.Stock.Proof.SinkRules.RhsWitness
open Backend.Proof Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

private def ctx : Ctx :=
  { sinkCtx with insts := sinkCtx.insts.push ⟨.op .unit,[],[],none⟩ }
private def input : State :=
  { sinkState with sunk := #[false,false], entryColor := #[1,0], instBlock := #[0,0] }
private def next : State := { input with color := some 1, sunk := #[true,false] }
private def env : Isle.Interp.Env V := #[some (.inst 0),none]

private theorem no_loads : NoLoadData ctx := by
  intro i info found fmt fields load decoded
  have member : info ∈ ctx.insts.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
  change info ∈ [⟨.op .unit,[0],[.int 8],some (.load .load .i8 {} 1 0)⟩,
    ⟨.op .unit,[],[],none⟩] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals change none = some (fmt,fields) at decoded; cases decoded

private theorem direct_run :
    (evalExpr program (Stock.sem ctx) {} 3 (.term 13 236 [.var 18 0]) env).run
      (input,#[]) = .ok (some (.op .unit),next,#[]) := by
  simp only [evalExpr,evalArgs,applyTerm,data_program.t236,Stock.sem,T.sink_inst,isel_monad]
  rfl

attribute [local semireducible] Isle.Aarch64.program in
private theorem let_run :
    (evalExpr program (Stock.sem ctx) {} 8
      (.let 4 [(1,13,.term 13 236 [.var 18 0])] (.constInt 4 7)) env).run
      (input,#[]) = .ok (some (.int 7),next,#[]) := by
  simp only [evalExpr,evalBinds,evalArgs,applyTerm,data_program.t236,Stock.sem,T.sink_inst,isel_monad]
  rfl

/-- A real direct sink changes bit zero while both frame lemmas protect the
distinct installed slot one. No theorem assumes every sink constructor is safe. -/
theorem explicit_sink_other_witness :
    input.sunk[0]! = false ∧ next.sunk[0]! = true ∧
    next.sunk[1]! = input.sunk[1]! := by
  have direct := sink_expr_other (i := 1) (by rfl) (by decide) direct_run
  have whole := sink_let_other (i := 1) (blocked := blocked)
    (fun m _ => (no_load_frames no_loads m).mono
      (fun _ _ same => congrArg (fun bits : Array Bool => bits[1]!) same))
    (by rfl) (by decide) (by rfl) let_run
  exact ⟨rfl,rfl,whole⟩

end Backend.Stock.Proof.SinkRules.RhsWitness
