import FV.Backend.Proof.StockSourceEdges

namespace Backend.Stock.Proof.SourceEdgesWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_source_edge_defined"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .jump ⟨1,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}] }
private def value (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩
private def first (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 (value word),slots := [],body := [],term := .jump ⟨1,[7]⟩ }
private def second (word : BitVec 64) : Clif.Frame := {
  first word with regs := (first word).regs.set 31 (value word),term := .ret [31] }
private def Observed : Prop := (Stock.lower function).toOption.map (fun result => decide
  (result.blockScans.size = 2 ∧
    (result.code.blocks[0]!).insts = #[.args [(.vreg 192 .int,.x 0)],.jump 1] ∧
    (result.code.blocks[0]!).branchArgs = #[.vreg 192 .int] ∧
    (result.code.blocks[1]!).params = #[.vreg 193 .int] ∧
    (result.code.blocks[1]!).insts = #[.rets [(.vreg 193 .int,.x 0)]])) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem ssa : (valueDefs function).Nodup := by change ([7,31] : List Nat).Nodup; decide +kernel
private theorem entry_defined (ctx : Ctx) (word : BitVec 64) : SourceDefinedAt function ctx 0 0 (first word) := by
  intro x available
  have block : function.blocks[0]? = some function.blocks[0]! := rfl
  obtain ⟨present,_⟩ := (mem_av block).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · have same : x = 7 := by simpa [function] using parameter
    subst x
    exact ⟨value word,rfl⟩
  · have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand 0 x incoming
    omega
  · omega

/-- A complete real two-block Stock driver and an arbitrary source word
inhabit both edge-definedness theorems. The successor parameter31 is bound
from7 while7 remains defined; actual VCode has nonempty outgoing arguments
and successor parameters. Source entry, branch and final return all succeed. -/
theorem stock_source_edge_defined_witness (word : BitVec 64) :
    ∃ result : Result,Stock.lower function = .ok result ∧ LowerScope function ∧ (valueDefs function).Nodup ∧
      result.blockScans.size = 2 ∧ (result.code.blocks[0]!).branchArgs = #[.vreg 192 .int] ∧
      (result.code.blocks[1]!).params = #[.vreg 193 .int] ∧
      Clif.enterFunc function [value word] Clif.Mem.empty = .ok (first word,Clif.Mem.empty) ∧
      Clif.stepTerm Clif.Env.empty {funcs := []} ⟨first word,[],Clif.Mem.empty⟩ (.jump ⟨1,[7]⟩) =
        .next ⟨second word,[],Clif.Mem.empty⟩ ∧
      Clif.stepTerm Clif.Env.empty {funcs := []} ⟨second word,[],Clif.Mem.empty⟩ (.ret [31]) =
        .done [value word] Clif.Mem.empty ∧
      SourceDefinedAt function result.ctx 0 0 (first word) ∧
      SourceDefinedAt function result.ctx 1 0 (second word) ∧
      (second word).regs 7 = some (value word) ∧ (second word).regs 31 = some (value word) ∧
      ∃ tl target,function.blocks[tl]? = some target ∧ (second word).func = function ∧
        (second word).body = target.body ∧ (second word).term = target.term ∧
        SourceDefinedAt function result.ctx tl 0 (second word) ∧
        Clif.Mem.empty = Clif.Mem.empty ∧ ([] : List (Clif.Frame × List Clif.ValueId)) = [] := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨scans,code,arguments,parameters,retCode⟩ := actual
    have source : Clif.enterBlock (first word) ⟨1,[7]⟩ = .ok (second word) := rfl
    have branch : Clif.stepTerm Clif.Env.empty {funcs := []} ⟨first word,[],Clif.Mem.empty⟩
        (.jump ⟨1,[7]⟩) = .next ⟨second word,[],Clif.Mem.empty⟩ := rfl
    have defined := source_defined_enterBlock ssa result.ctx (bi := 0) (b := function.blocks[0]!)
      rfl (fr := first word) rfl (bc := ⟨1,[7]⟩) (by decide +kernel) (tl := 1) rfl (entry_defined result.ctx word) source
    have transitioned := source_defined_branch_step ssa result.ctx (bi := 0) (b := function.blocks[0]!)
      rfl (s := ⟨first word,[],Clif.Mem.empty⟩) (next := ⟨second word,[],Clif.Mem.empty⟩)
      rfl (entry_defined result.ctx word) (by decide +kernel) branch
    exact ⟨result,rfl,lowerScope_of (by decide +kernel),ssa,scans,arguments,parameters,rfl,branch,rfl,
      entry_defined result.ctx word,defined,rfl,rfl,transitioned⟩
end Backend.Stock.Proof.SourceEdgesWitness
