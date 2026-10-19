import FV.Backend.Proof.SpillStep4Cfg

namespace Backend.Proof.Spill
open Backend Backend.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem count_le_one (xs : List Nat) (target : Nat)
    (unique : ∀ (i j : Nat),xs[i]? = some target → xs[j]? = some target → i = j) : xs.count target ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have tailUnique : ∀ (i j : Nat),xs[i]? = some target → xs[j]? = some target → i = j := by
      intro i j first second
      exact Nat.succ.inj (unique (i+1) (j+1) first second)
    by_cases same : x = target
    · subst x
      have absent : target ∉ xs := by
        intro member
        obtain ⟨j,bound,value⟩ := List.getElem_of_mem member
        have found : xs[j]? = some target := (List.getElem?_eq_getElem bound).trans (congrArg some value)
        have impossible := unique 0 (j+1) rfl found
        omega
      simp [List.count_cons,List.count_eq_zero.mpr absent]
    · have tail := ih tailUnique
      simpa [List.count_cons,same,Ne.symm same] using tail
private theorem rows_count_le_one (xs : List (Array Nat)) (target : Nat)
    (unique : ∀ (i j k l : Nat) (first second : Array Nat),xs[i]? = some first → xs[j]? = some second →
      first[k]? = some target → second[l]? = some target → i = j ∧ k = l) :
    (xs.flatMap Array.toList).count target ≤ 1 := by
  induction xs with
  | nil => simp
  | cons row xs ih =>
    have headBound : row.toList.count target ≤ 1 := count_le_one _ _ (by
      intro k l first second
      exact (unique 0 0 k l row row rfl rfl (by simpa using first) (by simpa using second)).2)
    have tailBound : (xs.flatMap Array.toList).count target ≤ 1 := ih (by
      intro i j k l first second atFirst atSecond firstEdge secondEdge
      have same := unique (i+1) (j+1) k l first second atFirst atSecond firstEdge secondEdge
      exact ⟨Nat.succ.inj same.1,same.2⟩)
    by_cases headZero : row.toList.count target = 0
    · simpa only [List.flatMap_cons,List.count_append,headZero,Nat.zero_add] using tailBound
    · by_cases tailZero : (xs.flatMap Array.toList).count target = 0
      · simpa only [List.flatMap_cons,List.count_append,tailZero,Nat.add_zero] using headBound
      · have headMember := List.count_pos_iff.mp (Nat.pos_of_ne_zero headZero)
        have tailMember := List.count_pos_iff.mp (Nat.pos_of_ne_zero tailZero)
        obtain ⟨second,secondMember,targetMember⟩ := List.mem_flatMap.mp tailMember
        obtain ⟨k,kBound,kValue⟩ := List.getElem_of_mem headMember
        obtain ⟨j,jBound,jValue⟩ := List.getElem_of_mem secondMember
        obtain ⟨l,lBound,lValue⟩ := List.getElem_of_mem targetMember
        have rowAt : xs[j]? = some second := (List.getElem?_eq_getElem jBound).trans (congrArg some jValue)
        have headAt : row[k]? = some target := by
          simpa only [Array.getElem?_toList] using (List.getElem?_eq_getElem kBound).trans (congrArg some kValue)
        have secondAt : second[l]? = some target := by
          simpa only [Array.getElem?_toList] using (List.getElem?_eq_getElem lBound).trans (congrArg some lValue)
        have impossible := unique 0 (j+1) k l row second rfl rowAt headAt secondAt
        omega
private theorem predsOf_zip_length (xs : List (Array Nat)) (start target : Nat) :
    (predsOf target (xs.zipIdx start)).length = (xs.flatMap Array.toList).count target := by
  induction xs generalizing start with
  | nil => simp [predsOf]
  | cons row xs ih =>
    rw [List.zipIdx_cons]
    change (List.replicate (row.toList.count target) start ++ predsOf target (xs.zipIdx (start+1))).length =
      (row.toList ++ xs.flatMap Array.toList).count target
    rw [List.length_append,List.length_replicate,ih,List.count_append]

/-- The actual predecessor array has at most one entry when all actual
incoming indexed edges agree. Repeated predecessor blocks at distinct
successor indices are counted separately by the executable CFG. -/
theorem cfg_pred_size_le_one_of_unique {vc : VCode} {ss ps : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) {target : Nat} (bound : target < vc.blocks.size)
    (unique : ∀ (b j b' j' : Nat) (row row' : Array Nat),ss[b]? = some row → row[j]? = some target →
      ss[b']? = some row' → row'[j']? = some target → b = b' ∧ j = j') : (ps[target]!).size ≤ 1 := by
  have pred : ps[target]! = (predsOf target ss.toList.zipIdx).toArray := by rw [getElem!_def,cfg_preds cfg bound]
  rw [pred,List.size_toArray,predsOf_zip_length]
  apply rows_count_le_one
  intro i j k l first second atFirst atSecond firstEdge secondEdge
  exact unique i k j l first second (by simpa using atFirst) firstEdge (by simpa using atSecond) secondEdge

/-- Every actual edge into a multiply reached target has another distinct
indexed incoming edge. This inverts real predecessor multiplicities without
assuming distinct predecessor block numbers or distinct target labels. -/
theorem cfg_multiple_preds_other {vc : VCode} {ss ps : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) {b j target : Nat} {row : Array Nat}
    (atRow : ss[b]? = some row) (edge : row[j]? = some target) (shared : 1 < (ps[target]!).size) :
    ∃ (other index : Nat) (otherRow : Array Nat),ss[other]? = some otherRow ∧ otherRow[index]? = some target ∧
      (other ≠ b ∨ index ≠ j) := by
  apply Classical.byContradiction
  intro missing
  have fixed : ∀ (other index : Nat) (otherRow : Array Nat),ss[other]? = some otherRow → otherRow[index]? = some target →
      other = b ∧ index = j := by
    intro other index otherRow otherAt otherEdge
    constructor
    · apply Classical.byContradiction
      intro different
      exact missing ⟨other,index,otherRow,otherAt,otherEdge,.inl different⟩
    · apply Classical.byContradiction
      intro different
      exact missing ⟨other,index,otherRow,otherAt,otherEdge,.inr different⟩
  have bound := cfg_succ_lt cfg atRow (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  have small := cfg_pred_size_le_one_of_unique cfg bound (by
    intro b₁ j₁ b₂ j₂ row₁ row₂ atRow₁ edge₁ atRow₂ edge₂
    have first := fixed b₁ j₁ row₁ atRow₁ edge₁
    have second := fixed b₂ j₂ row₂ atRow₂ edge₂
    exact ⟨first.1.trans second.1.symm,first.2.trans second.2.symm⟩)
  omega

/-- A real edge into a target with at most one predecessor pins down every
other indexed incoming edge. The singleton is derived from membership and
size, rather than supplied as an array-shape certificate. -/
theorem cfg_pred_size_le_one_unique {vc : VCode} {ss ps : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) {b j target : Nat} {row : Array Nat}
    (atRow : ss[b]? = some row) (edge : row[j]? = some target) (small : (ps[target]!).size ≤ 1)
    {other index : Nat} {otherRow : Array Nat} (otherAt : ss[other]? = some otherRow)
    (otherEdge : otherRow[index]? = some target) : other = b ∧ index = j := by
  have bound := cfg_succ_lt cfg atRow (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  have pred := cfg_preds cfg bound
  have member := mem_predsOf target ss.toList.zipIdx (row,b) (mem_zipIdx_of atRow)
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  have size : (predsOf target ss.toList.zipIdx).length ≤ 1 := by
    simpa only [getElem!_def,pred,Option.getD_some,List.size_toArray] using small
  cases list : predsOf target ss.toList.zipIdx with
  | nil => rw [list] at member; cases member
  | cons p rest =>
    have empty : rest = [] := List.length_eq_zero_iff.mp (by rw [list] at size; simp only [List.length_cons] at size; omega)
    rw [empty] at list
    have same : b = p := by rw [list] at member; exact List.mem_singleton.mp member
    rw [← same] at list
    have one : ps[target]? = some #[b] := by rw [pred,list]
    have sourceSame := (preds_single cfg otherAt otherEdge one).1
    subst other
    have sameRow := Option.some.inj (otherAt.symm.trans atRow)
    subst otherRow
    exact ⟨rfl,(preds_single cfg atRow edge one).2 index otherEdge⟩

end Backend.Proof.Spill
