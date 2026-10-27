import FV.Backend.Proof.StockBmaskMatch

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def bmaskWitnessFunction : Clif.Function := {
  name := "stock_bmask_original_selection"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [⟨[100],.bmask .i8 7⟩],term := .ret [100]}] }
def bmaskWitnessBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx bmaskWitnessFunction).toOption.getD (sinkCtx,#[],sinkState)
private theorem scope : LowerScope bmaskWitnessFunction := lowerScope_of (by decide +kernel)
private theorem built_run : Stock.buildCtx bmaskWitnessFunction = .ok bmaskWitnessBuilt := rfl

section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed :
    (Stock.runTerm bmaskWitnessBuilt.1 "lower" [.inst 0] bmaskWitnessBuilt.2.2).toOption.map (fun q => q.1.isSome) = some true := by
  decide +kernel
end Kernel

/-- A real accepted source with different input/output widths and sparse value
IDs inhabits rule selection, inferred operand typing and full-state lowering. -/
theorem stock_bmask_original_selection_witness :
    ∃ out next trace,Stock.runTerm bmaskWitnessBuilt.1 "lower" [.inst 0] bmaskWitnessBuilt.2.2 = .ok (some out,next,trace) ∧
      ∃ selected : LowerSelection bmaskWitnessBuilt.1 0 bmaskWitnessBuilt.2.2 out next trace,
        selected.rule = rule_lower_2052 ∧ MappedCtxInv bmaskWitnessFunction bmaskWitnessBuilt.1 ∧
        out = .regsVec [[bmaskResult bmaskWitnessBuilt.2.2.base 64 (.vreg 192 .int)]] ∧
        next = {bmaskWitnessBuilt.2.2.mark 7 with base := bmaskBase bmaskWitnessBuilt.2.2.base 64 (.vreg 192 .int)} ∧
        (matchRule program (Stock.sem bmaskWitnessBuilt.1) {} 2 rule_lower_2052 [.inst 0]).run (bmaskWitnessBuilt.2.2,#[]) =
          .ok (some (env3 (.ty (.int 8)) (.ty (.int 64)) (.value 7)),bmaskWitnessBuilt.2.2,#[]) := by
  have success := observed
  cases run : Stock.runTerm bmaskWitnessBuilt.1 "lower" [.inst 0] bmaskWitnessBuilt.2.2 with
  | error err => simp only [run,Except.toOption,Option.map_none] at success; cases success
  | ok q =>
    obtain ⟨out,next,trace⟩ := q
    cases out with
    | none => simp only [run,Except.toOption,Option.map_some,Option.isSome_none] at success; cases success
    | some out =>
      obtain ⟨selected⟩ := stock_named_lower_selection run
      have inv := buildCtx_mappedInv scope built_run
      have source : bmaskWitnessBuilt.1.insts[0]? = some bmaskWitnessBuilt.1.insts[0]! := rfl
      have original : bmaskWitnessBuilt.1.insts[0]!.clif = some (.bmask .i8 7) := rfl
      obtain ⟨wi,_,typed,_,r,mapped,outEq,stateEq⟩ := stock_bmask_selected inv source original selected
      change (some (CTy.int 64) : Option CTy) = some (CTy.int wi) at typed
      have width := CTy.int.inj (Option.some.inj typed)
      subst wi
      change (some (Reg.vreg 192 .int) : Option Reg) = some r at mapped
      cases mapped
      obtain ⟨_,data,type⟩ := stock_bmask_source_data inv source original
      have actualMatch := stock_bmask_match data_program bmaskWitnessBuilt.1 source type data
        (show bmaskWitnessBuilt.1.valueType? 7 = some (.int 64) from rfl) bmaskWitnessBuilt.2.2 #[] 0
      exact ⟨out,next,trace,rfl,selected,
        stock_selected_bmask_rule inv source original selected,inv,outEq,stateEq,actualMatch⟩

end Backend.Stock.Proof.ScalarMask
