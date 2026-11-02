import FV.Backend.Proof.StockForwardRpo
import FV.Backend.Proof.StockSourceOrder

namespace Backend.Stock.Proof.ForwardSource
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- An original source edge strictly increases rank. This describes source
blocks and destination lookup, independently of the compiler's traversal. -/
def Ranked (f : Clif.Function) (rank : Nat → Nat) : Prop :=
  ∀ bi b ti destination,
    f.blocks[bi]? = some b → destination ∈ destinations b.term →
    f.blocks.findIdx? (·.id == destination.1) = some ti → rank bi < rank ti

private theorem mapM_lookup {α β : Type} {xs : Array α} {ys : Array β}
    {step : α → Except String β} (run : xs.mapM step = .ok ys)
    {i : Nat} {y : β} (lookup : ys[i]? = some y) :
    ∃ x,xs[i]? = some x ∧ step x = .ok y := by
  obtain ⟨sizes,calls⟩ := Prep.amapM_ok run
  obtain ⟨bound,eq⟩ := Array.getElem?_eq_some_iff.mp lookup
  have xb : i < xs.size := by omega
  obtain ⟨z,call,result⟩ := calls i xs[i] (by simp [xb])
  have same : z = y := by rw [lookup] at result; exact (Option.some.inj result).symm
  subst z
  exact ⟨xs[i],by simp [xb],call⟩

/-- Every edge in the compiler's actual source table comes from the original
block terminator and its successful destination lookup. -/
theorem source_edge {f : Clif.Function} {source : Array (Array Nat)}
    (computed : stockSourceTable f = .ok source) {bi ti : Nat}
    (edge : ti ∈ source[bi]!.toList) :
    ∃ b destination,f.blocks[bi]? = some b ∧ destination ∈ destinations b.term ∧
      f.blocks.findIdx? (·.id == destination.1) = some ti := by
  cases row : source[bi]? with
  | none => simp only [getElem!_def,row] at edge; cases edge
  | some successors =>
    obtain ⟨b,found,blockRun⟩ := mapM_lookup computed row
    have member : ti ∈ successors := by
      simpa only [getElem!_def,row,Array.mem_toList_iff] using edge
    obtain ⟨i,lookup⟩ := Array.mem_iff_getElem?.mp member
    obtain ⟨destination,present,destRun⟩ := mapM_lookup blockRun lookup
    have original : destination ∈ destinations b.term := by
      have actual := Array.mem_of_getElem? present
      simpa only [List.mem_toArray] using actual
    refine ⟨b,destination,?_,original,?_⟩
    · simpa only [List.getElem?_toArray] using found
    · cases target : f.blocks.findIdx? (·.id == destination.1) with
      | none => simp only [target,throw,throwThe,MonadExceptOf.throw] at destRun; cases destRun
      | some index =>
        simp only [target,pure,Except.pure,Except.ok.injEq] at destRun
        exact congrArg some destRun

/-- Actual destination mapping preserves the original source successor count. -/
theorem source_row_size {f : Clif.Function} {source : Array (Array Nat)}
    (computed : stockSourceTable f = .ok source) {bi : Nat} {b : Clif.Block}
    (found : f.blocks[bi]? = some b) : source[bi]!.size = (destinations b.term).length := by
  obtain ⟨row,mapped,present⟩ := (Prep.amapM_ok computed).2 bi b (by simpa only [List.getElem?_toArray] using found)
  have size := (Prep.amapM_ok mapped).1
  simpa only [getElem!_def,present,Option.getD_some,List.size_toArray] using size

/-- Original source ranking transfers to the actual computed graph. -/
theorem source_table_ranked {f : Clif.Function} {source : Array (Array Nat)} {rank : Nat → Nat}
    (computed : stockSourceTable f = .ok source) (ranked : Ranked f rank) :
    ∀ bi ti,ti ∈ source[bi]!.toList → rank bi < rank ti := by
  intro bi ti edge
  obtain ⟨b,destination,found,present,target⟩ := source_edge computed edge
  exact ranked bi b ti destination found present target

/-- The actual source RPO respects every reachable ranked source edge. -/
theorem source_successor_after {f : Clif.Function} {source : Array (Array Nat)} {rank : Nat → Nat}
    (computed : stockSourceTable f = .ok source) (nonempty : f.blocks.length ≠ 0)
    (ranked : Ranked f rank) :
    ∀ bi ∈ (rpo source).toList,∀ ti ∈ source[bi]!.toList,
      ∃ earlier later,(rpo source).toList = earlier ++ bi :: later ∧ ti ∈ later := by
  obtain ⟨size,bounded⟩ := stock_sourceTable_bounds computed
  exact ForwardRpo.successor_after bounded (by simpa only [size] using nonempty)
    (source_table_ranked computed ranked)

/-- Synthetic critical-edge insertion preserves the source-edge ordering of
original nodes. No compiled-order certificate is added to the source condition. -/
theorem original_successor_after {f : Clif.Function} {order : Order} {rank : Nat → Nat}
    (ordered : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0)
    (ranked : Ranked f rank) :
    ∃ source,stockSourceTable f = .ok source ∧
      ∀ bi ∈ stockOriginals order.nodes,∀ ti ∈ source[bi]!.toList,
        ∃ earlier later,stockOriginals order.nodes = earlier ++ bi :: later ∧ ti ∈ later := by
  obtain ⟨source,computed,projection⟩ := stock_blockOrder_originals ordered
  refine ⟨source,computed,?_⟩
  rw [projection]
  exact source_successor_after computed nonempty ranked

private def original : Node → Option Nat
  | .original bi => some bi
  | .edge .. => none

private theorem original_before {nodes : Array Node} {bi ti : Nat}
    {earlier later : List Nat} (parts : stockOriginals nodes = earlier ++ bi :: later)
    (target : ti ∈ later) :
    ∃ before after,nodes.toList = before ++ .original bi :: after ∧ .original ti ∈ after := by
  change nodes.toList.filterMap original = earlier ++ bi :: later at parts
  obtain ⟨left,right,raw,leftMap,rightMap⟩ := List.filterMap_eq_append_iff.mp parts
  obtain ⟨gap,node,after,rightParts,empty,nodeMap,afterMap⟩ := List.filterMap_eq_cons_iff.mp rightMap
  have which : node = .original bi := by cases node <;> simp_all [original]
  subst node
  refine ⟨left ++ gap,after,?_,?_⟩
  · rw [raw,rightParts,List.append_assoc]
  · rw [← afterMap] at target
    obtain ⟨node,present,nodeMap⟩ := List.mem_filterMap.mp target
    have which : node = .original ti := by cases node <;> simp_all [original]
    simpa only [which] using present

/-- Every ranked original source edge has increasing actual Stock node labels,
including when critical-edge nodes occur between its original endpoints. -/
theorem successor_labels {f : Clif.Function} {order : Order} {rank : Nat → Nat}
    (ordered : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0)
    (ranked : Ranked f rank) {source : Array (Array Nat)}
    (computed : stockSourceTable f = .ok source) {label targetLabel bi ti : Nat}
    (fromTag : order.nodes[label]? = some (.original bi))
    (toTag : order.nodes[targetLabel]? = some (.original ti))
    (edge : ti ∈ source[bi]!.toList) : label < targetLabel := by
  obtain ⟨actual,actualComputed,projection⟩ := stock_blockOrder_originals ordered
  have same : actual = source := Except.ok.inj (actualComputed.symm.trans computed)
  subst actual
  have member : bi ∈ (rpo source).toList := by
    rw [← projection]
    exact List.mem_filterMap.mpr ⟨.original bi,
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? fromTag),rfl⟩
  obtain ⟨earlier,later,parts,present⟩ := source_successor_after computed nonempty ranked bi member ti edge
  rw [← projection] at parts
  obtain ⟨before,after,raw,present⟩ := original_before parts present
  obtain ⟨gap,rest,afterParts⟩ := List.append_of_mem present
  have first : order.nodes[before.length]? = some (.original bi) := by
    rw [← Array.getElem?_toList,raw,List.getElem?_append_right (Nat.le_refl _)]
    simp
  have second : order.nodes[before.length + (gap.length + 1)]? = some (.original ti) := by
    rw [← Array.getElem?_toList,raw,List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,afterParts]
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  have firstLabel := stock_blockOrder_original_unique ordered nonempty fromTag first
  have secondLabel := stock_blockOrder_original_unique ordered nonempty toTag second
  omega

end Backend.Stock.Proof.ForwardSource
