import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockCmpNonzero16OriginalSelection
namespace Backend.Stock.Proof.ScalarCmp.Nonzero16OriginalWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_nonzero16_original_selection"
  sig := {params := [⟨.i16,.none,.normal⟩],returns := [⟨.i16,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i16)],body := [],term := .ret [7]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private theorem scope : LowerScope function := lowerScope_of (by rfl)
private theorem build : Stock.buildCtx function = .ok built := rfl
section KernelFacts
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem actual : ∃ out next trace,ApplyInternal program (Stock.sem built.1) {} 999 123 651 [.value 7]
    (built.2.2,#[]) out (next,trace) := by
  have present : (((applyTerm program (Stock.sem built.1) {} 1000 123 651 [.value 7]).run
      (built.2.2,#[])).toOption.bind (fun result => result.1)).isSome = true := by decide +kernel
  cases run : (applyTerm program (Stock.sem built.1) {} 1000 123 651 [.value 7]).run (built.2.2,#[]) with
  | error e => simp only [run,Except.toOption,Option.bind_none,Option.isSome_none] at present; cases present
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    cases out with
    | none => simp only [run,Except.toOption,Option.bind_some,Option.isSome_none] at present; cases present
    | some out => exact ⟨out,next,trace,run⟩
end KernelFacts
/-- Actual original context construction and nonzero execution inhabit the
original-invariant selection contract; no parameter certificate is supplied. -/
theorem stock_cmp_nonzero16_original_selection_witness :
    ∃ out next trace rhsTrace,LowerScope function ∧ MappedCtxInv function built.1 ∧
      ApplyInternal program (Stock.sem built.1) {} 999 123 651 [.value 7] (built.2.2,#[]) out (next,trace) ∧
      (evalExpr program (Stock.sem built.1) {} 999 rule_inst_4977.rhs #[some (.ty (.int 16)),some (.value 7)]).run
        (built.2.2,#[]) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_4977.id := by
  obtain ⟨out,next,trace,run⟩ := actual
  have inv := buildCtx_mappedInv scope build
  obtain ⟨rhsTrace,rhs,finish⟩ := stock_cmp_original_nonzero16_selected built.1 inv (by decide) rfl run
  exact ⟨out,next,trace,rhsTrace,scope,inv,run,rhs,finish⟩
end Backend.Stock.Proof.ScalarCmp.Nonzero16OriginalWitness
