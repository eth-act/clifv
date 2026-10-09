import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.LowerCertBase
import FV.Backend.Proof.LowerDecide

set_option maxRecDepth 4096

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix

private theorem DFGViewEq.availIn_eq {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs, Ctx.defInst?, view.valDef, view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers, usersN, args, view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0, view.valDef, bytes, args]
  simp only [availIn, inFix_eq, users, bytes, work, view.valDef]

private theorem DFGViewEq.prov_source {ctx original : Ctx}
    (view : DFGViewEq ctx original) {d y : Nat} (reached : Prov ctx d y) :
    Prov original d y := by
  induction reached with
  | arg info originalInst member =>
    exact .arg (by simpa only [view.insts] using info) originalInst member
  | dep _ defined info originalInst member ih =>
    exact .dep ih (by simpa only [Ctx.defInst?, view.valDef] using defined)
      (by simpa only [view.insts] using info) originalInst member

/-- Source provenance remains available in the actual densely allocated stock
context. The original must-availability proof applies because the DFG is retained;
no identification of source value IDs with allocated vreg numbers is assumed. -/
theorem stock_available_provenance {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (dominated : Dominated f)
    {bi j n d y : Nat} (available : n ∈ availOf f (availIn f ctx) bi j)
    (definition : ctx.defInst? n = some d) (reached : Prov ctx d y) :
    y ∈ availOf f (availIn f ctx) bi j := by
  obtain ⟨original, st0, sourceBuild, _, view⟩ := buildCtx_source build
  have available' : n ∈ availOf f (availIn f original) bi j := by
    simpa only [view.availIn_eq f] using available
  have definition' : original.defInst? n = some d := by
    simpa only [Ctx.defInst?, view.valDef] using definition
  have result := prov_closed dominated sourceBuild available' definition' (view.prov_source reached)
  simpa only [view.availIn_eq f] using result

/-- The provenance of an available block-entry value remains available there
and is not redefined in the current block. This excludes stale local definitions
even when their old values still exist in the source frame. -/
theorem stock_entry_available_provenance {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (dominated : Dominated f)
    {bi n d y : Nat} (available : n ∈ (availIn f ctx).getD bi [])
    (notLocal : n ∉ defsOf f bi) (definition : ctx.defInst? n = some d)
    (reached : Prov ctx d y) :
    y ∈ (availIn f ctx).getD bi [] ∧ y ∉ defsOf f bi := by
  obtain ⟨original, st0, sourceBuild, _, view⟩ := buildCtx_source build
  have available' : n ∈ (availIn f original).getD bi [] := by
    simpa only [view.availIn_eq f] using available
  have definition' : original.defInst? n = some d := by
    simpa only [Ctx.defInst?, view.valDef] using definition
  have result := prov_entry dominated sourceBuild available' notLocal definition' (view.prov_source reached)
  simpa only [view.availIn_eq f] using result

private def provenanceFunction : Clif.Function := {
  name := "available_provenance"
  sig := { returns := [⟨.i8, .none, .normal⟩] }
  blocks := [
    { id := 7, params := [],
      body := [⟨[0], .iconst .i64 9⟩, ⟨[1], .ireduce .i8 0⟩], term := .jump ⟨9, []⟩ },
    { id := 9, params := [], body := [⟨[2], .iconst .i8 7⟩], term := .ret [1] }] }
private def provenanceBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx provenanceFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem provenance_build : Stock.buildCtx provenanceFunction = .ok provenanceBuilt := rfl
private theorem provenance_defs : provenanceBuilt.1.valDef = #[some 0, some 1, some 3] := rfl
private theorem provenance_args : defArgs provenanceBuilt.1 = fun n => if n = 1 then [0] else [] := by
  funext n
  rcases n with _ | (_ | (_ | n))
  · rfl
  · rfl
  · rfl
  · simp only [defArgs, Ctx.defInst?, provenance_defs]
    simp
private theorem provenance_fix : FixOk provenanceFunction provenanceBuilt.1 id
    (fun tl x => tl = 1 ∧ (x = 0 ∨ x = 1)) := by
  constructor
  · intro tl x h
    rcases h with ⟨rfl, rfl | rfl⟩ <;>
      simp [provenanceFunction, provenance_defs, valueDefs, parsOf]
  · intro tl x h p hp
    rcases h with ⟨rfl, hx⟩
    rcases p with _ | (_ | p)
    · right; left
      rcases hx with rfl | rfl <;> decide +kernel
    · right; right; exact ⟨rfl, hx⟩
    · simp [succIdx, provenanceFunction] at hp
  · intro tl x h y hy
    rcases h with ⟨rfl, rfl | rfl⟩
    · simp [provenance_args] at hy
    · simp [provenance_args] at hy
      subst y
      constructor
      · right; exact ⟨rfl, Or.inl rfl⟩
      · decide +kernel
private theorem provenance_entry_zero : (0 : Nat) ∈ (availIn provenanceFunction provenanceBuilt.1).getD 1 [] :=
  inFix_greatest provenance_fix ⟨rfl, Or.inl rfl⟩
private theorem provenance_entry_one : (1 : Nat) ∈ (availIn provenanceFunction provenanceBuilt.1).getD 1 [] :=
  inFix_greatest provenance_fix ⟨rfl, Or.inr rfl⟩
private theorem provenance_available_one (In : Array (List Nat))
    (entry : (1 : Nat) ∈ In.getD 1 []) :
    (1 : Nat) ∈ availOf provenanceFunction In 1 0 := by
  change 1 ∈ (In.getD 1 [] ++ []).filter (fun x => decide (x ∉ [2]))
  simp only [List.append_nil, List.mem_filter, decide_eq_true_eq]
  exact ⟨entry, by decide⟩
private theorem provenance_dominated : Dominated provenanceFunction := by
  obtain ⟨original, initial, originalBuild, _, view⟩ := buildCtx_source provenance_build
  constructor
  · decide +kernel
  · intro ctx ranges st hb bi B hB
    have ctxEq : original = ctx := congrArg (fun t => t.1) (Except.ok.inj (originalBuild.symm.trans hb))
    subst ctx
    rw [← view.availIn_eq provenanceFunction]
    rcases bi with _ | (_ | bi)
    · simp [provenanceFunction] at hB
      subst B
      constructor
      · intro j stm hs y hy
        rcases j with _ | (_ | j) <;> simp at hs
        · subst stm; simp [Backend.Proof.Driver.instArgs] at hy
        · subst stm; simp [Backend.Proof.Driver.instArgs] at hy; subst y
          change 0 ∈ ((availIn provenanceFunction provenanceBuilt.1).getD 0 [] ++ [0]).filter
            (fun x => decide (x ∉ [1]))
          simp
      · intro y hy; change y ∈ ([] : List Nat) at hy; cases hy
    · simp [provenanceFunction] at hB
      subst B
      constructor
      · intro j stm hs y hy
        rcases j with _ | j <;> simp at hs
        subst stm; simp [Backend.Proof.Driver.instArgs] at hy
      · intro y hy
        change y ∈ [1] at hy
        simp only [List.mem_singleton] at hy
        subst y
        change 1 ∈ ((availIn provenanceFunction provenanceBuilt.1).getD 1 [] ++ [2]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        apply List.mem_filter.mpr
        exact ⟨List.mem_append.mpr (Or.inl provenance_entry_one), by decide⟩
    · simp [provenanceFunction] at hB
  · intro ctx ranges st hb tl x hx hn y hy
    rcases tl with _ | (_ | tl) <;> simp [parsOf, provenanceFunction]
private theorem provenance_reached : Prov provenanceBuilt.1 1 0 :=
  .arg (info := provenanceBuilt.1.insts[1]!) (c := .ireduce .i8 0) rfl rfl (by decide +kernel)

/-- A real predecessor computes a reduction from its constant, and both values
are available at the successor. The stock context uses dense allocated registers. -/
theorem stock_available_provenance_witness :
    Stock.buildCtx provenanceFunction = .ok provenanceBuilt ∧ Dominated provenanceFunction ∧
      provenanceBuilt.1.valueReg? 0 = some (.vreg 192 .int) ∧
      provenanceBuilt.1.valueReg? 1 = some (.vreg 193 .int) ∧
      (1 : Nat) ∈ availOf provenanceFunction (availIn provenanceFunction provenanceBuilt.1) 1 0 ∧
      provenanceBuilt.1.defInst? 1 = some 1 ∧ Prov provenanceBuilt.1 1 0 ∧
      (0 : Nat) ∈ availOf provenanceFunction (availIn provenanceFunction provenanceBuilt.1) 1 0 := by
  refine ⟨provenance_build, provenance_dominated, rfl, rfl, provenance_available_one _ provenance_entry_one, rfl, provenance_reached, ?_⟩
  exact stock_available_provenance provenance_build provenance_dominated (n := 1)
    (bi := 1) (j := 0) (provenance_available_one _ provenance_entry_one) rfl provenance_reached

/-- Entry availability contains the predecessor's result and its source operand,
while excluding the successor's own future constant. The entry-closure premises
are witnessed by an actual nonempty dependency. -/
theorem stock_entry_available_provenance_witness :
    Stock.buildCtx provenanceFunction = .ok provenanceBuilt ∧ Dominated provenanceFunction ∧
      (1 : Nat) ∈ (availIn provenanceFunction provenanceBuilt.1).getD 1 [] ∧
      (1 : Nat) ∉ defsOf provenanceFunction 1 ∧ provenanceBuilt.1.defInst? 1 = some 1 ∧
      Prov provenanceBuilt.1 1 0 ∧
      (0 : Nat) ∈ (availIn provenanceFunction provenanceBuilt.1).getD 1 [] ∧
      (0 : Nat) ∉ defsOf provenanceFunction 1 ∧
      (2 : Nat) ∉ availOf provenanceFunction (availIn provenanceFunction provenanceBuilt.1) 1 0 := by
  refine ⟨provenance_build, provenance_dominated, provenance_entry_one, by decide +kernel, rfl,
    provenance_reached, ?_, ?_, by
      change 2 ∉ ((availIn provenanceFunction provenanceBuilt.1).getD 1 [] ++ []).filter
        (fun x => decide (x ∉ [2]))
      simp⟩
  · exact (stock_entry_available_provenance provenance_build provenance_dominated
      (n := 1) (bi := 1) provenance_entry_one (by decide +kernel) rfl provenance_reached).1
  · exact (stock_entry_available_provenance provenance_build provenance_dominated
      (n := 1) (bi := 1) provenance_entry_one (by decide +kernel) rfl provenance_reached).2

end Backend.Stock.Proof
