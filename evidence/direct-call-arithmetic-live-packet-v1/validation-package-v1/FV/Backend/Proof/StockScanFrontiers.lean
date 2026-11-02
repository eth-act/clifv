import FV.Backend.Proof.StockAllocationFlow

/-! Every recorded scan input retains the block's initial allocation frontier. -/
namespace Backend.Stock.Proof

/-- The real backward scan carries the initial fresh frontier to every recorded
instruction input, rather than only to the final block state. -/
theorem stock_scanBlock_frontiers {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan} {cap : Nat}
    (bound : cap ≤ st.base.nextVreg)
    (h : scanBlock ctx block ti branch indices st = .ok output) :
    ∀ r ∈ output.records, cap ≤ r.input.base.nextVreg := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => simp
  | cons head rest ih =>
    intro record mem
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact bound
    · exact ih (Nat.le_trans bound (stock_scan_allocationLe head).1) record mem

/-- An actual opportunistic block scan has a recorded input and a nontrivial
installed alias, so the per-record frontier guarantee is inhabited. -/
theorem stock_scanBlock_frontiers_witness :
    ∃ ctx st output, scanBlock ctx 0 1 false [0] st = .ok output ∧
      output.state.alias[192]? = some (some 197) ∧ output.records ≠ [] ∧
      (∀ r ∈ output.records, st.base.nextVreg ≤ r.input.base.nextVreg) := by
  obtain ⟨ctx, st, output, run, _, alias, _⟩ := stock_scanBlock_allocationLe_witness
  have nonempty : output.records ≠ [] := by
    have order := (runScans_spec run).order
    intro empty
    rw [empty] at order
    cases order
  exact ⟨ctx, st, output, run, alias, nonempty, stock_scanBlock_frontiers (Nat.le_refl _) run⟩

end Backend.Stock.Proof
