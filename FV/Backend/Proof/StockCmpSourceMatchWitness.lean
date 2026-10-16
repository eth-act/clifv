import FV.Backend.Proof.StockCmpSourceMatch
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def sourceFunction : Clif.Function := {
  name := "stock_cmp_original_selection"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [⟨[100],.icmp .eq .i64 7 31⟩],term := .ret [100]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx sourceFunction).toOption.getD (sinkCtx,#[],sinkState)
private theorem scope : LowerScope sourceFunction := lowerScope_of (by decide +kernel)
private theorem built_run : Stock.buildCtx sourceFunction = .ok built := rfl
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed :
    (Stock.runTerm built.1 "lower" [.inst 0] built.2.2).toOption.map (fun q => q.1.isSome) = some true := by
  decide +kernel
end Kernel
/-- Original accepted sparse-ID source input inhabits the actual comparison
selection and exact source-data contracts through a successful named Stock run. -/
theorem stock_cmp_original_selection_witness :
    ∃ out next trace,Stock.runTerm built.1 "lower" [.inst 0] built.2.2 = .ok (some out,next,trace) ∧
      ∃ selected : LowerSelection built.1 0 built.2.2 out next trace,selected.rule.id = 958 ∧
        MappedCtxInv sourceFunction built.1 ∧
        built.1.insts[0]!.data = .data 152 14 [.data 151 72 [],.values [7,31],.data 145 (ccIdx .eq) []] ∧
        built.1.insts[0]!.resTys.head? = some (.int 8) := by
  have success := observed
  cases run : Stock.runTerm built.1 "lower" [.inst 0] built.2.2 with
  | error err => simp only [run,Except.toOption,Option.map_none] at success; cases success
  | ok q =>
    obtain ⟨out,next,trace⟩ := q
    cases out with
    | none => simp only [run,Except.toOption,Option.map_some,Option.isSome_none] at success; cases success
    | some out =>
      obtain ⟨selected⟩ := stock_named_lower_selection run
      have inv := buildCtx_mappedInv scope built_run
      have source : built.1.insts[0]? = some built.1.insts[0]! := rfl
      have original : built.1.insts[0]!.clif = some (.icmp .eq .i64 7 31) := rfl
      obtain ⟨_,data,type⟩ := stock_cmp_source_data inv source original
      exact ⟨out,next,trace,rfl,selected,stock_selected_cmp_root inv source original selected,inv,data,type⟩
end Backend.Stock.Proof.ScalarCmp
