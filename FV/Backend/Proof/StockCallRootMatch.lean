import FV.Backend.Proof.StockCallRhsCalls
namespace Backend.Stock.Proof.CallRootMatchDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open CallRootSelectionDraft CallRhsCallsDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

/-- Real colocated direct-call matching returns the complete canonical
environment and frames the full Stock scheduler and trace. -/
theorem stock_direct_call_root_match {p : Program} (hp : Data p) (ctx : Ctx)
    {ti fn : Nat} {info : IInfo} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : ctx.insts[ti]? = some info)
    (data : info.data = .data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)])
    (external : ctx.func.extern? fn = some ext) (colocated : ext.colocated = true)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+1000) rule_lower_2508 [.inst ti]).run (st,tr) =
      .ok (some (directEnv args ext.sig ext.name false),st,tr) := by
  have source := ext_inst_data_value ctx st.base slot
  rw [data] at source
  have extracted : Backend.externExtract ctx T.func_ref_data (.op (.funcRef fn)) st.base =
      .ok [.op (.sig ext.sig),.op (.extName ext.name),.data 38 0 [],.bool false] := by
    apply (ext_func_ref_data_iff st.base fn _).mpr
    exact ⟨ext,external,by rw [colocated]; rfl⟩
  have sliced : Backend.externExtract ctx T.value_list_slice (.values args) st.base = .ok [.values args] := rfl
  cases hp
  isel_eval [*,rule_lower_2508,directEnv,sem_extract,sem_unData,ext_value_list_slice_iff]
  isel_eval [*,rule_lower_2508,directEnv,sem_extract,sem_unData,ext_value_list_slice_iff]
  rfl

private theorem direct_before_got :
    (program.rulesOf T.lower.id).idxOf rule_lower_2508 <
      (program.rulesOf T.lower.id).idxOf rule_lower_2518 := by
  unfold program
  decide +kernel

/-- Actual first-match selection of a colocated direct source call derives
its ordinary call rule and every real RHS helper execution internally. The
non-colocated/GOT and indirect cases remain separate obligations. -/
theorem stock_selected_direct_call_rhs_calls {ctx : Ctx} {ti fn : Nat}
    {info : IInfo} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : ctx.insts[ti]? = some info)
    (data : info.data = .data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)])
    (external : ctx.func.extern? fn = some ext) (colocated : ext.colocated = true)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx ti st out next rules) :
    selected.rule = rule_lower_2508 ∧ selected.env = directEnv args ext.sig ext.name false ∧
      selected.matched = st ∧ selected.matchTrace = #[] ∧
      DirectRootCalls program ctx args ext.sig ext.name false st next #[] selected.rhsTrace out := by
  have chosen : selected.rule = rule_lower_2508 := by
    rcases stock_selected_call_rule slot data selected with direct | got
    · exact direct
    · have before := direct_before_got
      rw [← got] at before
      have earlier : rule_lower_2508 ∈ selected.pre := by
        by_cases present : rule_lower_2508 ∈ selected.pre
        · exact present
        · have unique := lower_ids_nodup
          change (List.map Rule.id (program.rulesOf T.lower.id)).Nodup at unique
          have order := congrArg (List.map Rule.id) selected.candidates
          simp only [List.map_append,List.map_cons] at order
          rw [order] at unique
          have absent : selected.rule ∉ selected.pre := by
            intro contained
            have disjoint := (List.nodup_append.mp unique).2.2
            exact (disjoint selected.rule.id (List.mem_map.mpr ⟨_,contained,rfl⟩)
              selected.rule.id (List.mem_cons_self ..)) rfl
          rw [selected.candidates,List.idxOf_append,if_neg present,List.idxOf_append,
            if_neg absent,List.idxOf_cons_self] at before
          omega
      obtain ⟨fuel,bound,after,failed⟩ := selected.rejected _ earlier
      have count : (program.rulesOf T.lower.id).length = 517 := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
      obtain ⟨n,equal⟩ : ∃ n,fuel=n+1000 := ⟨fuel-1000,by omega⟩
      rw [equal,stock_direct_call_root_match data_program ctx slot data external colocated st #[] n] at failed
      cases failed
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨n,equal⟩ : ∃ n,selected.matchFuel=n+1000 := ⟨selected.matchFuel-1000,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,equal,stock_direct_call_root_match data_program ctx slot data external colocated st #[] n] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨environment,state,trace⟩ := matched
  refine ⟨chosen,environment.symm,state.symm,trace.symm,?_⟩
  have rhs := selected.rhsRun
  rw [chosen,← environment,← state,← trace] at rhs
  exact stock_direct_call_rhs_calls data_program ctx args ext.sig ext.name false rhs
end Backend.Stock.Proof.CallRootMatchDraft
