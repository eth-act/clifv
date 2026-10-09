import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.StockAvailableProvenance

/-! Transport operand provenance out of the actual block scan's terminator
and exception-register overrides. No restriction on reserved registers. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 4096

/-- The selected block context reaches the same source operands as the original
mapped context. A terminator placeholder cannot define a source value, and the
root here is a source statement outside that placeholder. Exception reservations
may be arbitrary. -/
theorem stock_selected_provenance_source {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {ti ii y : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : Backend.V) (reserved : List Reg × List Reg)
    (reached : Prov { Driver.termCtx ctx ti data with tryRegs := reserved } ii y) :
    Prov ctx ii y := by
  have defNe (x d : Nat) (defined : ctx.defInst? x = some d) : d ≠ ti := by
    intro same
    subst d
    obtain ⟨info, lookup, member⟩ := mapped.defInst x ti defined
    rw [placeholder] at lookup
    cases lookup
    cases member
  induction reached with
  | arg lookup original member =>
    change (Driver.termCtx ctx ti data).insts[ii]? = _ at lookup
    rw [termCtx_insts_ne distinct] at lookup
    exact .arg lookup original member
  | dep _ defined lookup original member ih =>
    change ctx.defInst? _ = _ at defined
    change (Driver.termCtx ctx ti data).insts[_]? = _ at lookup
    rw [termCtx_insts_ne (defNe _ _ defined)] at lookup
    exact .dep ih defined lookup original member

/-- Definition provenance discovered in the selected scan context remains
available in the source frame whenever its source result is available. This
includes contexts with nonempty exception reservations. -/
theorem stock_selected_available_provenance {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    (dominated : Dominated f) {ti bi j n d y : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : d ≠ ti) (data : Backend.V) (reserved : List Reg × List Reg)
    (available : n ∈ availOf f (availIn f ctx) bi j)
    (definition : ctx.defInst? n = some d)
    (reached : Prov { Driver.termCtx ctx ti data with tryRegs := reserved } d y) :
    y ∈ availOf f (availIn f ctx) bi j :=
  stock_available_provenance build dominated available definition
    (stock_selected_provenance_source (buildCtx_mappedInv scope build)
      placeholder distinct data reserved reached)

private def selectedFunction : Clif.Function := {
  name := "selected_provenance"
  sig := { returns := [⟨.i8, .none, .normal⟩] }
  blocks := [{ id := 0, params := [], body := [⟨[0], .iconst .i64 9⟩, ⟨[1], .ireduce .i8 0⟩], term := .ret [1] }] }
private def selectedBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx selectedFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem selected_build : Stock.buildCtx selectedFunction = .ok selectedBuilt := rfl
private theorem selected_scope : LowerScope selectedFunction := lowerScope_of (by decide +kernel)
private def selectedData : Backend.V :=
  (Backend.termData (.ret [1])).toOption.getD (.op .unit)
private def selectedReserved : List Reg × List Reg :=
  ([.vreg 194 .int], [.vreg 195 .int, .vreg 196 .int])
private def selectedCtx : Ctx := { Driver.termCtx selectedBuilt.1 2 selectedData with tryRegs := selectedReserved }
private theorem selected_placeholder : selectedBuilt.1.insts[2]? = some ⟨.op .unit, [], [], none⟩ := rfl
private theorem selected_reached : Prov selectedCtx 1 0 :=
  .arg (info := selectedCtx.insts[1]!) (c := .ireduce .i8 0) rfl rfl (by decide +kernel)

theorem stock_selected_provenance_source_witness :
    Stock.buildCtx selectedFunction = .ok selectedBuilt ∧
    selectedBuilt.1.valueReg? 0 = some (.vreg 192 .int) ∧
    selectedCtx.tryRegs = selectedReserved ∧ selectedReserved.2 ≠ [] ∧
    selectedCtx.insts[2]? ≠ selectedBuilt.1.insts[2]? ∧
    Prov selectedCtx 1 0 ∧ Prov selectedBuilt.1 1 0 := by
  refine ⟨selected_build, rfl, rfl, (by decide), (by
    intro same
    have data := congrArg (fun q => q.map (·.data)) same
    cases data), selected_reached, ?_⟩
  exact stock_selected_provenance_source (buildCtx_mappedInv selected_scope selected_build)
    selected_placeholder (by decide) selectedData selectedReserved selected_reached

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
        rcases j with _ | (_ | j) <;> simp at lookup
        · subst stmt; simp [Backend.Proof.Driver.instArgs] at member
        · subst stmt; simp [Backend.Proof.Driver.instArgs] at member; subst y
          change 0 ∈ ((availIn selectedFunction ctx).getD 0 [] ++ [0]).filter
            (fun x => decide (x ∉ [1]))
          simp
      · intro y member
        change y ∈ [1] at member
        simp only [List.mem_singleton] at member
        subst y
        change 1 ∈ ((availIn selectedFunction ctx).getD 0 [] ++ [0, 1]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    | succ bi => simp [selectedFunction] at block
  · intro ctx ranges st build tl x entry notLocal y args
    cases tl <;> simp [parsOf, selectedFunction]

private theorem selected_available :
    (1 : Nat) ∈ availOf selectedFunction (availIn selectedFunction selectedBuilt.1) 0 2 := by
  change 1 ∈ ((availIn selectedFunction selectedBuilt.1).getD 0 [] ++ [0, 1]).filter
    (fun x => decide (x ∉ ([] : List Nat)))
  simp

/-- Nonempty exception reservations and an actual return-data override coexist
with source availability: the reduction's source operand0 remains available
when its result1 is available at the post-body boundary. -/
theorem stock_selected_available_provenance_witness :
    Stock.buildCtx selectedFunction = .ok selectedBuilt ∧ LowerScope selectedFunction ∧
    Dominated selectedFunction ∧ selectedCtx.tryRegs.2 ≠ [] ∧
    (1 : Nat) ∈ availOf selectedFunction (availIn selectedFunction selectedBuilt.1) 0 2 ∧
    selectedBuilt.1.defInst? 1 = some 1 ∧ Prov selectedCtx 1 0 ∧
    (0 : Nat) ∈ availOf selectedFunction (availIn selectedFunction selectedBuilt.1) 0 2 := by
  refine ⟨selected_build, selected_scope, selected_dominated, (by decide),
    selected_available, rfl, selected_reached, ?_⟩
  exact stock_selected_available_provenance selected_build selected_scope selected_dominated
    selected_placeholder (by decide) selectedData selectedReserved selected_available rfl selected_reached

end Backend.Stock.Proof
