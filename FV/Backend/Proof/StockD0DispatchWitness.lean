import FV.Backend.Proof.StockD0Witness
import FV.Backend.Proof.StockD0Edges

namespace Backend.Stock.D0

/-- A real successful Stock result reaches the Stock dispatcher branch for all
six configurations, arbitrary symbol names and arbitrary run metadata. -/
theorem actual_stock_dispatch (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) :
    ∃ result, Stock.lower (source name c runs) = .ok result ∧
      result.edgeArgs = #[#[]] ∧
      selectWith Stock.lower (source name c runs) = .ok (.stockD0, compact name result) := by
  obtain ⟨result, run⟩ := stock_succeeds name c runs
  have edges := stock_edges_empty name c runs run
  have guard : result.edgeArgs.all (·.isEmpty) = true := by
    rw [edges]
    decide +kernel
  refine ⟨result, run, edges, ?_⟩
  simp only [selectWith, source_eligible, ↓reduceIte, run, guard]
  rfl

/-- The fixed production candidate actually returns that successful Stock code;
legacy compatibility alone cannot satisfy this witness by choosing fallback. -/
theorem default_source_success (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) :
    ∃ result, Stock.lower (source name c runs) = .ok result ∧
      selectWith Stock.lower (source name c runs) = .ok (.stockD0, compact name result) ∧
      defaultLower (source name c runs) = .ok (compact name result) := by
  obtain ⟨result, run, _, selected⟩ := actual_stock_dispatch name c runs
  refine ⟨result, run, selected, ?_⟩
  simp only [defaultLower, selected, Except.map]

#print axioms actual_stock_dispatch
#print axioms default_source_success
end Backend.Stock.D0
