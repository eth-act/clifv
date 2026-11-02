import FV.Backend.Proof.StockRootFlow
import FV.Backend.Proof.StockSelectedProvenance

/-! Output origins and source availability for the actual selected block context. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096

/-- Actual generated root execution transports output provenance back to the
source context after overriding terminator data and exception reservations. -/
theorem stock_selected_root_flow {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {ti ii : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : V) (reserved : List Reg × List Reg)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {fuel : Nat} {before after : State} {out : V} {trace finalTrace : Array RuleId}
    (run : (applyTerm program (Stock.sem { Driver.termCtx ctx ti data with tryRegs := reserved })
      {} fuel T.lower.ret T.lower.id [.inst ii]).run (before, trace) =
        .ok (some out, (after, finalTrace))) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls,
      rs = [.vreg o cls] →
      (before.base.nextVreg ≤ o ∧ o < after.base.nextVreg) ∨
        (∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg o cls)) ∨
        (.vreg o cls) ∈ reserved.1 ∨ (.vreg o cls) ∈ reserved.2 := by
  have selected := (mapped.termCtx placeholder data).withTryRegs reserved
  have infoSelected : ({ Driver.termCtx ctx ti data with tryRegs := reserved } : Ctx).insts[ii]? =
      some info := by
    change (Driver.termCtx ctx ti data).insts[ii]? = some info
    rw [termCtx_insts_ne distinct]
    exact source
  intro rss output results rs member o cls singleton
  rcases MappedFlow.stock_root_reserved_context_flow selected infoSelected original run
      rss output results rs member o cls singleton with fresh | ⟨x, reached, register⟩ | ret | payload
  · exact .inl fresh
  · exact .inr (.inl ⟨x, stock_selected_provenance_source mapped placeholder distinct data reserved reached,
      register⟩)
  · exact .inr (.inr (.inl ret))
  · exact .inr (.inr (.inr payload))

/-- A mapped source output reached by an actual selected root is available
whenever that source root's result is available at the source boundary. Fresh
outputs and exact exception reservations remain separate alternatives. -/
theorem stock_selected_root_available {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    (dominated : Dominated f) {ti ii bi j n : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : V) (reserved : List Reg × List Reg)
    (available : n ∈ availOf f (availIn f ctx) bi j) (definition : ctx.defInst? n = some ii)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {fuel : Nat} {before after : State} {out : V} {trace finalTrace : Array RuleId}
    (run : (applyTerm program (Stock.sem { Driver.termCtx ctx ti data with tryRegs := reserved })
      {} fuel T.lower.ret T.lower.id [.inst ii]).run (before, trace) =
        .ok (some out, (after, finalTrace))) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls,
      rs = [.vreg o cls] →
      (before.base.nextVreg ≤ o ∧ o < after.base.nextVreg) ∨
        (∃ x, x ∈ availOf f (availIn f ctx) bi j ∧ ctx.valueReg? x = some (.vreg o cls)) ∨
        (.vreg o cls) ∈ reserved.1 ∨ (.vreg o cls) ∈ reserved.2 := by
  intro rss output results rs member o cls singleton
  rcases stock_selected_root_flow (buildCtx_mappedInv scope build) placeholder distinct data reserved
      source original run rss output results rs member o cls singleton with
      fresh | ⟨x, reached, register⟩ | ret | payload
  · exact .inl fresh
  · exact .inr (.inl ⟨x, stock_available_provenance build dominated available definition reached, register⟩)
  · exact .inr (.inr (.inl ret))
  · exact .inr (.inr (.inr payload))

private def selectedFunction : Clif.Function := {
  name := "mapped_dfg"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i8, .none, .normal⟩] }
  blocks := [{ id := 5, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [2] }] }
private def selectedBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx selectedFunction).toOption.getD (sinkCtx, #[], sinkState)
private def selectedReserved : List Reg × List Reg :=
  ([.vreg 194 .int], [.vreg 195 .int, .vreg 196 .int])
private def selectedData : V := (Backend.termData (.ret [2])).toOption.getD (.op .unit)
private def selectedCtx : Ctx :=
  { Driver.termCtx selectedBuilt.1 1 selectedData with tryRegs := selectedReserved }
private def selectedInput : State :=
  { sinkState with base := { sinkState.base with nextVreg := 197 } }
private theorem selected_build : Stock.buildCtx selectedFunction = .ok selectedBuilt := rfl
private theorem selected_scope : LowerScope selectedFunction := buildCtx_mappedInv_witness.1
private theorem selected_info : selectedBuilt.1.insts[0]? = some selectedBuilt.1.insts[0]! := rfl
private theorem selected_original : selectedBuilt.1.insts[0]!.clif = some (.iconst .i8 9) := rfl
private theorem selected_placeholder : selectedBuilt.1.insts[1]? = some ⟨.op .unit, [], [], none⟩ := rfl

/-- Actual selected-context generated lowering uses fresh197 while its source
result2 maps to193; the terminator data changed and reserves194/195/196 are nonempty. -/
theorem stock_selected_root_flow_witness :
    ∃ (next : State) (trace : Array RuleId),
      Stock.buildCtx selectedFunction = .ok selectedBuilt ∧ LowerScope selectedFunction ∧
      selectedBuilt.1.valueReg? 2 = some (.vreg 193 .int) ∧
      selectedCtx.insts[1]? ≠ selectedBuilt.1.insts[1]? ∧ selectedCtx.tryRegs.2 ≠ [] ∧
      (applyTerm program (Stock.sem selectedCtx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (selectedInput, #[]) = .ok (some (.regsVec [[.vreg 197 .int]]), next, trace.push 582) ∧
      ((selectedInput.base.nextVreg ≤ 197 ∧ 197 < next.base.nextVreg) ∨
        (∃ x, Prov selectedBuilt.1 0 x ∧ selectedBuilt.1.valueReg? x = some (.vreg 197 .int)) ∨
        (.vreg 197 .int) ∈ selectedReserved.1 ∨ (.vreg 197 .int) ∈ selectedReserved.2) := by
  obtain ⟨next, trace, mapping, changed, nonempty, run⟩ := stock_statement_selectedConstant_context_witness
  refine ⟨next, trace, selected_build, selected_scope, mapping, changed, nonempty, run, ?_⟩
  exact stock_selected_root_flow (buildCtx_mappedInv selected_scope selected_build)
    selected_placeholder (by decide) selectedData selectedReserved selected_info selected_original
    run _ rfl (by decide) _ (List.mem_singleton_self _) _ _ rfl

private def selectedOriginalBuilt : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx selectedFunction).toOption.getD (sinkCtx, #[], sinkState.base)
private theorem selected_original_build : Backend.buildCtx selectedFunction = .ok selectedOriginalBuilt := rfl
private theorem selected_original_defs :
    selectedOriginalBuilt.1.valDef = #[none, none, some 0, none, none, none, none, none] := rfl
private theorem selected_original_args (x : Nat) : defArgs selectedOriginalBuilt.1 x = [] := by
  rcases x with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | x))))))) <;>
    simp [defArgs, Ctx.defInst?, selected_original_defs]
  rfl

private theorem selected_dominated : Dominated selectedFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi B block
    cases bi with
    | zero =>
      simp [selectedFunction] at block
      subst B
      constructor
      · intro j stmt lookup y member
        cases j with
        | zero => simp at lookup; subst stmt; simp [Backend.Proof.Driver.instArgs] at member
        | succ j => simp at lookup
      · intro y member
        change y ∈ [2] at member
        simp only [List.mem_singleton] at member
        subst y
        change 2 ∈ ([7] ++ (availIn selectedFunction ctx).getD 0 [] ++ [2]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    | succ bi => simp [selectedFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    rw [selected_original_build] at build
    cases build
    change y ∈ defArgs selectedOriginalBuilt.1 x at member
    rw [selected_original_args] at member
    cases member

private theorem selected_available :
    (2 : Nat) ∈ availOf selectedFunction (availIn selectedFunction selectedBuilt.1) 0 1 := by
  change 2 ∈ ([7] ++ (availIn selectedFunction selectedBuilt.1).getD 0 [] ++ [2]).filter
    (fun x => decide (x ∉ ([] : List Nat)))
  simp

/-- An inhabited source post-body boundary and actual selected root execution
certify the availability-aware classification with changed terminator/nonempty reserves. -/
theorem stock_selected_root_available_witness :
    ∃ (next : State) (trace : Array RuleId),
      Stock.buildCtx selectedFunction = .ok selectedBuilt ∧ LowerScope selectedFunction ∧
      Dominated selectedFunction ∧ selectedCtx.tryRegs.2 ≠ [] ∧
      (2 : Nat) ∈ availOf selectedFunction (availIn selectedFunction selectedBuilt.1) 0 1 ∧
      selectedBuilt.1.defInst? 2 = some 0 ∧
      (applyTerm program (Stock.sem selectedCtx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (selectedInput, #[]) = .ok (some (.regsVec [[.vreg 197 .int]]), next, trace.push 582) ∧
      ((selectedInput.base.nextVreg ≤ 197 ∧ 197 < next.base.nextVreg) ∨
        (∃ x, x ∈ availOf selectedFunction (availIn selectedFunction selectedBuilt.1) 0 1 ∧
          selectedBuilt.1.valueReg? x = some (.vreg 197 .int)) ∨
        (.vreg 197 .int) ∈ selectedReserved.1 ∨ (.vreg 197 .int) ∈ selectedReserved.2) := by
  obtain ⟨next, trace, _, _, _, run⟩ := stock_statement_selectedConstant_context_witness
  refine ⟨next, trace, selected_build, selected_scope, selected_dominated, (by decide),
    selected_available, rfl, run, ?_⟩
  exact stock_selected_root_available selected_build selected_scope selected_dominated
    selected_placeholder (by decide) selectedData selectedReserved selected_available rfl
    selected_info selected_original run _ rfl (by decide) _ (List.mem_singleton_self _) _ _ rfl

end Backend.Stock.Proof
