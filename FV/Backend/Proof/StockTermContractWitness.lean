import FV.Backend.Proof.StockTermContract
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.TermContractWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_trap_abi_contract"
  sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .trap (.user 9)}] }
private def Observed : Prop := (Stock.lower function).toOption.map (fun result => decide
  ((result.code.blocks[0]!).insts = #[.udf (.user 9)] ∧
    result.initial.base.nextVreg = result.final.base.nextVreg ∧
    (sigRets result.ctx.func.sig).any (·.purpose == .sret) = false)) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel

/-- Complete original trap lowering inhabits both terminator interfaces. The
legacy conversion is applied to the actual context and initial/final states. -/
theorem stock_trap_term_contract_witness : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧
    (result.code.blocks[0]!).insts = #[.udf (.user 9)] ∧
    Clif.step Clif.Env.empty {funcs := []}
      ⟨{func := function,regs := fun _ => none,slots := [],body := [],term := .trap (.user 9)},[],Clif.Mem.empty⟩ =
        .trapped (.user 9) ∧
    LowerTermOkABI ispec (fun _ _ _ => True) result.ctx (.trap (.user 9)) []
      result.initial.base result.final.base [.udf (.user 9)] ∧
    LowerTermOk ispec (fun _ _ _ => True) result.ctx (.trap (.user 9)) []
      result.initial.base result.final.base [.udf (.user 9)] := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨code,next,ordinary⟩ := actual
    have contract : LowerTermOkABI ispec (fun _ _ _ => True) result.ctx (.trap (.user 9)) []
        result.initial.base result.final.base [.udf (.user 9)] := by
      refine ⟨Nat.le_of_eq next,?_,?_⟩
      · simp [vdefs,operands_udf]
      · intro fr cm ρ w _ _ _ _
        exact ⟨by simp [UsesOk,vuseNums,operands_udf],0,.udf (.user 9),#[],ρ,w,[],w,rfl,rfl⟩
    exact ⟨result,rfl,lowerScope_of (by decide +kernel),code,rfl,contract,contract.legacy ordinary⟩
end Backend.Stock.Proof.TermContractWitness
