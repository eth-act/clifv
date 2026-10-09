import FV.Backend.Proof.StockAliasSemantics

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- Moving past a statement makes only its results newly source-available.
Stale registers for later definitions remain excluded by `availOf`. -/
theorem stock_availOf_next_other {f : Clif.Function} {In : Array (List Nat)}
    {bi j y : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stmt)
    (other : y ∉ stmt.results) (available : y ∈ availOf f In bi (j + 1)) :
    y ∈ availOf f In bi j := by
  obtain ⟨bound, slot⟩ := List.getElem?_eq_some_iff.mp statement
  have earlier : defsBefore block (j + 1) = defsBefore block j ++ stmt.results := by
    unfold defsBefore
    rw [List.take_succ_eq_append_getElem bound, List.flatMap_append, slot]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have later : defsFrom block j = stmt.results ++ defsFrom block (j + 1) := by
    unfold defsFrom
    rw [List.drop_eq_getElem_cons bound, slot, List.flatMap_cons]
  simp only [availOf, blockAt, List.mem_filter, decide_eq_true_eq,
    List.mem_append] at available ⊢
  rw [earlier] at available
  simp only [List.mem_append] at available
  refine ⟨?_, ?_⟩
  · rcases available.1 with old | fresh
    · exact Or.inl old
    · rcases fresh with old | result
      · exact Or.inr old
      · exact False.elim (other result)
  · rw [later, List.mem_append]
    intro member
    exact member.elim other available.2

/-- The result being defined need not have been held before the statement.
Only other values needed at the next source boundary must come from the previous
boundary. The original same-demand result theorem remains available. -/
theorem ValuesHeld.resolvedResult_frame_between
    {before after : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ ρ' : Nat → CV} {gn : Nat → Nat} {x n d : Nat}
    {v : Clif.Val} {ms : List MInst} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (held : ValuesHeld before ctx fr (fun k => ρ (gn k)))
    (needed : ∀ y, after y → y ≠ x → before y)
    (mapping : ctx.valueReg? x = some (.vreg n .int)) (result : gn n = d)
    (value : VHolds v (ρ' d))
    (keep : ∀ y m, after y → y ≠ x → ctx.valueReg? y = some (.vreg m .int) →
      (fr.regs y).isSome = true → ∀ mi ∈ ms, gn m ∉ vdefs mi)
    (run : PRun F isem ms ρ ρ') :
    ValuesHeld after ctx (withValue fr x v) (fun k => ρ' (gn k)) := by
  intro y hy val lookup
  by_cases same : y = x
  · subst y
    simp only [withValue, eq_self, ite_true] at lookup
    cases lookup
    exact ⟨n, mapping, by change VHolds v (ρ' (gn n)); rw [result]; exact value⟩
  · simp only [withValue, ite_eq_right same] at lookup
    obtain ⟨m, mapped, previous⟩ := held y (needed y hy same) val lookup
    obtain ⟨world, execution, _⟩ := run Arm.ArmState.default
    have unchanged := seqRun_fall_frame (keep y m hy same mapped (by rw [lookup]; rfl)) execution
    exact ⟨m, mapped, by change VHolds val (ρ' (gn m)); rw [unchanged]; exact previous⟩

private def boundaryFunction : Clif.Function := {
  name := "source_boundary"
  sig := {
    params := [⟨.i64, .none, .normal⟩]
    returns := [⟨.i8, .none, .normal⟩, ⟨.i64, .none, .normal⟩] }
  blocks := [{
    id := 7
    params := [(1, .i64)]
    body := [⟨[0], .iconst .i8 9⟩]
    term := .ret [0, 1] }] }
private def boundaryBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx boundaryFunction).toOption.getD (sinkCtx, #[], sinkState)
private abbrev boundaryBefore (y : Nat) : Prop := y ∈ availOf boundaryFunction #[] 0 0
private abbrev boundaryAfter (y : Nat) : Prop := y ∈ availOf boundaryFunction #[] 0 1
private def boundaryFrame : Clif.Frame := {
  func := boundaryFunction
  regs := fun y => if y = 0 then some (.ofInt .i8 64)
    else if y = 1 then some (.ofInt .i64 27) else none
  slots := [], body := boundaryFunction.blocks[0]!.body, term := .ret [0, 1] }
private def boundaryRF (n : Nat) : CV := if n = 192 then 27 else 0
private def boundaryRename (n : Nat) : Nat := if n = 193 then 194 else n

/-- A real nonempty source block has a live parameter before its constant and
the new constant afterwards. The parameter satisfies the next-boundary theorem. -/
theorem stock_availOf_next_other_witness :
    (valueDefs boundaryFunction).Nodup ∧
      boundaryBefore 1 ∧ boundaryAfter 1 ∧ ¬boundaryBefore 0 ∧ boundaryAfter 0 := by
  refine ⟨by decide, ?_, by decide, by decide, by decide⟩
  exact stock_availOf_next_other (f := boundaryFunction) (In := #[]) (bi := 0)
    (j := 0) (y := 1) (block := boundaryFunction.blocks[0]!)
    (stmt := ⟨[0], .iconst .i8 9⟩) rfl rfl (by decide) (by decide)

private theorem boundary_held :
    ValuesHeld boundaryBefore boundaryBuilt.1 boundaryFrame
      (fun k => boundaryRF (boundaryRename k)) := by
  intro y available val lookup
  have same : y = 1 := by
    simpa [boundaryBefore, availOf, boundaryFunction, defsBefore, defsFrom] using available
  subst y
  change some (Clif.Val.ofInt .i64 27) = some val at lookup
  cases lookup
  exact ⟨192, rfl, by unfold VHolds boundaryRF boundaryRename; decide⟩

private theorem boundary_needed (y : Nat) (available : boundaryAfter y) (other : y ≠ 0) :
    boundaryBefore y := by
  apply stock_availOf_next_other (f := boundaryFunction) (In := #[]) (bi := 0)
    (j := 0) (block := boundaryFunction.blocks[0]!) (stmt := ⟨[0], .iconst .i8 9⟩) rfl rfl
  · simpa using other
  · exact available

private theorem boundary_refines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ world _ execution => ⟨world, execution, SameWorld.refl _ _⟩

/-- A retained stale source result fails the old post-demand relation before
execution. Actual constant materialization nevertheless establishes the new
boundary relation while keeping a live parameter; no frame clearing is assumed. -/
theorem ValuesHeld.resolvedResult_frame_between_witness :
    Stock.buildCtx boundaryFunction = .ok boundaryBuilt ∧
      boundaryFrame.regs 0 = some (.ofInt .i8 64) ∧
      ¬ValuesHeld boundaryAfter boundaryBuilt.1 boundaryFrame
        (fun k => boundaryRF (boundaryRename k)) ∧
      ∃ ms ρ', PRun (fun _ => True) ispec ms boundaryRF ρ' ∧
        ValuesHeld boundaryAfter boundaryBuilt.1
          (withValue boundaryFrame 0 (.ofInt .i8 9)) (fun k => ρ' (boundaryRename k)) ∧
        VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧ ρ' 192 = 27 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro held
    have bad := held.read (x := 0) (n := 193) (v := .ofInt .i8 64) (by decide) rfl rfl
    exact (by unfold VHolds boundaryRF boundaryRename; decide :
      ¬VHolds (Clif.Val.ofInt .i8 64) (boundaryRF (boundaryRename 193))) bad
  · have materialized := imm_case_movz boundary_refines (w := 8) (i := 9)
      (mw := ⟨9, 0⟩) (Or.inl rfl) rfl sinkState.base
    obtain ⟨ms, d, reg, shape, materialize⟩ := materialized
    change V.reg (.vreg 194 .int) = V.reg (.vreg d .int) at reg
    cases reg
    obtain ⟨ρ', X, run, val, bits, _⟩ := materialize boundaryRF
    have value : VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) :=
      vholds_of_lo64 (by decide) val bits
    have keep : ∀ y m, boundaryAfter y → y ≠ 0 →
        boundaryBuilt.1.valueReg? y = some (.vreg m .int) →
        (boundaryFrame.regs y).isSome = true → ∀ mi ∈ ms, boundaryRename m ∉ vdefs mi := by
      intro y m available other mapped present mi member defined
      have before := boundary_needed y available other
      have same : y = 1 := by
        simpa [boundaryBefore, availOf, boundaryFunction, defsBefore, defsFrom] using before
      subst y
      change some (Reg.vreg 192 .int) = some (.vreg m .int) at mapped
      cases mapped
      have bound := (shape.defs mi member _ defined).1
      change 194 ≤ 192 at bound
      omega
    have held := boundary_held.resolvedResult_frame_between boundary_needed
      (x := 0) (n := 193) (d := 194) rfl rfl value keep run
    obtain ⟨world, execution, _⟩ := run Arm.ArmState.default
    have preserved : ρ' 192 = boundaryRF 192 := by
      apply seqRun_fall_frame _ execution
      intro mi member defined
      have bound := (shape.defs mi member _ defined).1
      change 194 ≤ 192 at bound
      omega
    exact ⟨ms, ρ', run, held, value, preserved⟩

end Backend.Stock.Proof
