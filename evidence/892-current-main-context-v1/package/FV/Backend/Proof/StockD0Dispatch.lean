import FV.Backend.Proof.StockD0Code

namespace Backend.Stock.D0

/-- Deferring legacy work preserves the original selector for every callback and
input. Successful Stock paths need not evaluate the unused legacy computation. -/
theorem selectWith_eq_original (stock : Clif.Function → Except String Result)
    (f : Clif.Function) :
    selectWith stock f =
      (let legacy := (lowerFunction f).map fun vc => (Origin.legacy, vc)
       if eligible f then
         match stock f with
         | .ok r => if r.edgeArgs.all (·.isEmpty) then .ok (.stockD0, compact f.name r) else legacy
         | .error _ => legacy
       else legacy) := by rfl

/-- All original compiler inputs, errors and outputs are retained. The only
Stock-output test is the structural zero-successor preparation guard. -/
theorem defaultLower_eq_legacy (f : Clif.Function) : defaultLower f = lowerFunction f := by
  unfold defaultLower selectWith
  split
  next h =>
    obtain ⟨c, _, hf⟩ := eligible_sound h
    have same : (Stock.lower f).map (compact f.name) = lowerFunction f := by
      simpa only [← hf] using normalized_eq_legacy f.name c f.runs
    cases hs : Stock.lower f with
    | error e =>
      simp only [hs, Except.map]
      cases lowerFunction f <;> rfl
    | ok r =>
      simp only [hs, Except.map]
      by_cases edges : r.edgeArgs.all (·.isEmpty) = true
      · simp only [edges, ↓reduceIte]
        simpa only [hs, Except.map] using same
      · simp only [edges, ↓reduceIte]
        cases lowerFunction f <;> rfl
  next => cases lowerFunction f <;> rfl

/-- Forced Stock failure reaches legacy with the same input; the test callback
is never assumed correct and does not certify any Stock success. -/
theorem failed_stock_falls_back (f : Clif.Function) (reason : String) :
    selectWith (fun _ => .error reason) f =
      (lowerFunction f).map (fun vc => (Origin.legacy, vc)) := by
  unfold selectWith
  split <;> rfl

#print axioms defaultLower_eq_legacy
#print axioms failed_stock_falls_back
#print axioms selectWith_eq_original
end Backend.Stock.D0
