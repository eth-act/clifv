import FV.Backend.Proof.StockCriticalSplit

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def scan (xs : List Nat) (a : Array Nat) : Array Nat := xs.foldl (fun a t => a.modify t (· + 1)) a
private def rows (xs : List (Array Nat)) (a : Array Nat) : Array Nat := xs.foldl (fun a ss => scan ss.toList a) a
private def rowStep (ss : Array Nat) (a : Array Nat) : Except String (ForInStep (Array Nat)) := do
  let next ← forIn ss a fun t a => pure (.yield (a.modify t (· + 1)))
  pure (.yield next)
private theorem rowStep_eq (ss : Array Nat) (a : Array Nat) : rowStep ss a = .ok (.yield (scan ss.toList a)) := by
  unfold rowStep
  rw [← Array.forIn_toList,Prep.forIn_yield_foldl _ _ _ _ (by intro t a; rfl)]
  rfl
private theorem computed (source : Array (Array Nat)) (size : Nat) : sourceIndegree source size =
    .ok (rows source.toList (Array.replicate size 0)) := by
  unfold sourceIndegree
  change (forIn source (Array.replicate size 0) rowStep >>= fun a => pure a) = _
  rw [← Array.forIn_toList,Prep.forIn_yield_foldl _ _ _ _ rowStep_eq]
  rfl
private theorem scan_size (xs : List Nat) (a : Array Nat) : (scan xs a).size = a.size := by
  induction xs generalizing a with
  | nil => rfl
  | cons t xs ih => exact (ih _).trans (Array.size_modify ..)
private theorem rows_size (xs : List (Array Nat)) (a : Array Nat) : (rows xs a).size = a.size := by
  induction xs generalizing a with
  | nil => rfl
  | cons ss xs ih => exact (ih _).trans (scan_size _ _)
private theorem scan_count (xs : List Nat) (a : Array Nat) (v : Nat) (bound : v < a.size) :
    (scan xs a)[v]! = a[v]! + xs.count v := by
  induction xs generalizing a with
  | nil => simp [scan]
  | cons t xs ih =>
    change (scan xs (a.modify t (· + 1)))[v]! = _
    rw [ih _ (by simpa using bound)]
    by_cases same : t = v
    · subst t
      simp [getElem!_def,Array.getElem?_modify,Array.getElem?_eq_getElem bound,List.count_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [getElem!_def,Array.getElem?_modify,same,Ne.symm same,List.count_cons,Nat.add_assoc]
private theorem rows_count (xs : List (Array Nat)) (a : Array Nat) (v : Nat) (bound : v < a.size) :
    (rows xs a)[v]! = a[v]! + (xs.flatMap Array.toList).count v := by
  induction xs generalizing a with
  | nil => simp [rows]
  | cons ss xs ih =>
    change (rows xs (scan ss.toList a))[v]! = _
    rw [ih _ (by rw [scan_size]; exact bound),scan_count _ _ _ bound]
    simp only [List.flatMap_cons,List.count_append,Nat.add_assoc]

/-- The executable source indegree table counts every occurrence of a target
in every source row, including duplicate and unreachable source edges. Bounds
and exact counts follow from the computation, not from an input certificate. -/
theorem sourceIndegree_counts {source : Array (Array Nat)} {size : Nat} {degree : Array Nat}
    (run : sourceIndegree source size = .ok degree) : degree.size = size ∧
      ∀ target,target < size → degree[target]! = (source.toList.flatMap Array.toList).count target := by
  have same := Except.ok.inj (run.symm.trans (computed source size))
  subst degree
  constructor
  · rw [rows_size,Array.size_replicate]
  · intro target bound
    rw [rows_count _ _ _ (by simpa using bound)]
    simp [getElem!_def,Array.getElem?_replicate,bound]

end Backend.Stock.Proof
