import FV.Backend.Proof.StockD0Witness
import FV.Backend.Proof.StockD0Dispatch

namespace Backend.Stock.D0

/-- A successful legacy result is retained when the Stock attempt is forced to
fail. Arbitrary names, metadata and error reasons do not make this vacuous. -/
theorem forced_failure_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (reason : String) :
    ∃ code, lowerFunction (source name c runs) = .ok code ∧
      selectWith (fun _ => .error reason) (source name c runs) = .ok (.legacy, code) := by
  obtain ⟨result, run⟩ := stock_succeeds name c runs
  have legacy : lowerFunction (source name c runs) = .ok (compact name result) := by
    rw [← normalized_eq_legacy name c runs, run]
    rfl
  refine ⟨compact name result, legacy, ?_⟩
  rw [failed_stock_falls_back, legacy]
  rfl

/-- A nonempty successor row cannot be erased by the fixed dispatcher. -/
theorem nonempty_edges_fall_back (f : Clif.Function) (result : Result)
    (edges : result.edgeArgs.all (·.isEmpty) = false) :
    selectWith (fun _ => .ok result) f =
      (lowerFunction f).map (fun code => (Origin.legacy, code)) := by
  unfold selectWith
  split <;> simp only [edges, Bool.false_eq_true, ↓reduceIte]

/-- The edge guard is exercised on an actual successful Stock result with only
its edge payload changed; fallback itself still succeeds on the original input. -/
theorem edge_guard_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) :
    ∃ result code, Stock.lower (source name c runs) = .ok result ∧
      lowerFunction (source name c runs) = .ok code ∧
      selectWith (fun _ => .ok {result with edgeArgs := #[#[#[.vreg 0 .int]]]})
        (source name c runs) = .ok (.legacy, code) := by
  obtain ⟨result, run⟩ := stock_succeeds name c runs
  have legacy : lowerFunction (source name c runs) = .ok (compact name result) := by
    rw [← normalized_eq_legacy name c runs, run]
    rfl
  have guard : (#[#[#[Reg.vreg 0 .int]]] : Array (Array (Array Reg))).all (·.isEmpty) = false := by
    decide +kernel
  refine ⟨result, compact name result, run, legacy, ?_⟩
  rw [nonempty_edges_fall_back _ _ guard, legacy]
  rfl

#print axioms forced_failure_witness
#print axioms nonempty_edges_fall_back
#print axioms edge_guard_witness
end Backend.Stock.D0
