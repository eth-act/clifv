import FV.Backend.Proof.StockIncomingGraph
import FV.Backend.Proof.StockSourceIndegree

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem count_unique (xs : List Nat) (target : Nat) : ∀ (i j : Nat),
    xs.count target ≤ 1 → xs[i]? = some target → xs[j]? = some target → i = j := by
  induction xs with
  | nil => intro i j low first second; simp at first
  | cons x xs ih =>
    intro i j low first second
    have tailLow : xs.count target ≤ 1 := Nat.le_trans List.count_le_count_cons low
    cases i with
    | zero =>
      cases first
      cases j with
      | zero => rfl
      | succ j =>
        change xs[j]? = some target at second
        have positive := List.count_pos_iff.mpr (List.mem_of_getElem? second)
        simp only [List.count_cons,BEq.rfl,ite_true] at low
        omega
    | succ i =>
      change xs[i]? = some target at first
      cases j with
      | zero =>
        cases second
        have positive := List.count_pos_iff.mpr (List.mem_of_getElem? first)
        simp only [List.count_cons,BEq.rfl,ite_true] at low
        omega
      | succ j => exact congrArg Nat.succ (ih i j tailLow first second)
private theorem rows_unique (xs : List (Array Nat)) (target : Nat) :
    ∀ (i j : Nat) (row₁ row₂ : Array Nat) (k l : Nat),(xs.flatMap Array.toList).count target ≤ 1 →
      xs[i]? = some row₁ → xs[j]? = some row₂ → row₁[k]? = some target → row₂[l]? = some target → i = j ∧ k = l := by
  induction xs with
  | nil => intro i j row₁ row₂ k l low first second atFirst atSecond; simp at first
  | cons row xs ih =>
    intro i j row₁ row₂ k l low first second atFirst atSecond
    have sum : row.toList.count target + (xs.flatMap Array.toList).count target ≤ 1 := by
      simpa only [List.flatMap_cons,List.count_append] using low
    cases i with
    | zero =>
      cases first
      cases j with
      | zero =>
        cases second
        exact ⟨rfl,count_unique row.toList target k l (by omega) (by simpa using atFirst) (by simpa using atSecond)⟩
      | succ j =>
        change xs[j]? = some row₂ at second
        have left := List.count_pos_iff.mpr (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atFirst))
        have right := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨row₂,List.mem_of_getElem? second,
          Array.mem_toList_iff.mpr (Array.mem_of_getElem? atSecond)⟩)
        omega
    | succ i =>
      change xs[i]? = some row₁ at first
      cases j with
      | zero =>
        cases second
        have right := List.count_pos_iff.mpr (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atSecond))
        have left := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨row₁,List.mem_of_getElem? first,
          Array.mem_toList_iff.mpr (Array.mem_of_getElem? atFirst)⟩)
        omega
      | succ j =>
        obtain ⟨same,indices⟩ := ih i j row₁ row₂ k l (by omega) first second atFirst atSecond
        exact ⟨congrArg Nat.succ same,indices⟩
private theorem source_unique {source : Array (Array Nat)} {target bi₁ k₁ bi₂ k₂ : Nat}
    (low : (source.toList.flatMap Array.toList).count target ≤ 1)
    (first : source[bi₁]![k₁]? = some target) (second : source[bi₂]![k₂]? = some target) : bi₁ = bi₂ ∧ k₁ = k₂ := by
  have row₁ : source[bi₁]? = some source[bi₁]! := by
    cases found : source[bi₁]? with
    | none => simp only [getElem!_def,found] at first; cases first
    | some row => simpa only [getElem!_def,found] using found
  have row₂ : source[bi₂]? = some source[bi₂]! := by
    cases found : source[bi₂]? with
    | none => simp only [getElem!_def,found] at second; cases second
    | some row => simpa only [getElem!_def,found] using found
  exact rows_unique source.toList target bi₁ bi₂ _ _ k₁ k₂ low (by simpa using row₁) (by simpa using row₂) first second
private theorem incoming_key {result : Result} {source : Array (Array Nat)} {target b j : Nat}
    (incoming : IncomingOriginalAt result source target b j) :
    ∃ node bi k,result.order.nodes[b]? = some node ∧ sourceEdgeKey node j = (bi,k) ∧ source[bi]![k]? = some target := by
  rcases incoming with ⟨bi,node,selected,_⟩ | ⟨bi,k,node,_,selected⟩
  · exact ⟨.original bi,bi,j,node,rfl,selected⟩
  · exact ⟨.edge bi k target,bi,k,node,rfl,selected⟩

/-- Actual original-target graph indegree cannot exceed one when the exact
source indegree is at most one. Incoming occurrences retain their successor
indices, so repeated destinations and synthetic nodes cannot evade the bound. -/
theorem stock_lower_low_degree_incoming_unique {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    ∃ source degree,stockSourceTable f = .ok source ∧ sourceIndegree source f.blocks.length = .ok degree ∧
      ∀ targetLabel target,result.order.nodes[targetLabel]? = some (.original target) → degree[target]! ≤ 1 →
        ∀ (b₁ j₁ b₂ j₂ : Nat) (ss₁ ss₂ : Array Nat),
          result.order.successors[b₁]? = some ss₁ → ss₁[j₁]? = some targetLabel →
          result.order.successors[b₂]? = some ss₂ → ss₂[j₂]? = some targetLabel → b₁ = b₂ ∧ j₁ = j₂ := by
  obtain ⟨source,degree,computed,counted,_⟩ := stock_lower_critical_split_complete run
  obtain ⟨source',computed',incoming⟩ := stock_lower_incoming_original run
  have same := Except.ok.inj (computed.symm.trans computed')
  subst source'
  refine ⟨source,degree,computed,counted,?_⟩
  intro targetLabel target targetNode low b₁ j₁ b₂ j₂ ss₁ ss₂ firstRow firstEdge secondRow secondEdge
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have member : target ∈ stockOriginals result.order.nodes := by
    apply List.mem_filterMap.mpr
    exact ⟨.original target,Array.mem_toList_iff.mpr (Array.mem_of_getElem? targetNode),rfl⟩
  have bound := (stock_blockOrder_originals_nodup (stock_lower_order run) nonempty).2 target member
  have lowCount : (source.toList.flatMap Array.toList).count target ≤ 1 := by
    rw [← (sourceIndegree_counts counted).2 target bound]
    exact low
  obtain ⟨node₁,bi₁,k₁,atNode₁,key₁,selected₁⟩ := incoming_key (incoming _ _ targetNode _ _ _ firstRow firstEdge)
  obtain ⟨node₂,bi₂,k₂,atNode₂,key₂,selected₂⟩ := incoming_key (incoming _ _ targetNode _ _ _ secondRow secondEdge)
  obtain ⟨sameBi,sameIndex⟩ := source_unique lowCount selected₁ selected₂
  exact stock_lower_incoming_source_unique run scope targetNode atNode₁ atNode₂ firstRow firstEdge secondRow secondEdge
    (by rw [key₁,key₂,sameBi,sameIndex])

end Backend.Stock.Proof
