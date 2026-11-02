import FV.Backend.Proof.StockLoopCarryGlobal
import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockSourceOrder
import FV.Backend.Proof.PrepareComplete

/-! `DefBefore` for every Stock lowering of an SSA function (#140, T7b-4).

`defCarry_cover` (T7b-3) needs `DefBefore f result`: a block that defines a value (as a parameter
or a body result) available at the entry of block `t` has a smaller label than `t` in Stock's
block order. This file proves it from the lowering and SSA alone (`stock_lower_defBefore_ssa`).

* `rpo_parent`: in `rpo`'s depth-first search, each block other than the entry is discovered from
  a predecessor, which ends later and so comes earlier in the reverse postorder. The invariant
  (`ParentList`) is kept over the sequence "stack from the bottom, then postorder reversed", which
  pushing a discovered block extends by one element right after its parent and popping a block
  leaves unchanged.
* `stock_blockOrder_parent`: each nonentry original node of Stock's block order has a source
  predecessor at a smaller label; the critical-edge nodes between them do not change the order of
  the originals (`stock_blockOrder_originals`).
* `stock_lower_defBefore_ssa`: strong induction on the label of `t`. A value available at `t`'s
  entry is available at the end of every predecessor (`FixOk.out`), so at the end of the smaller
  parent `p`: either `p` defines it (then `p` is its only defining block, by SSA) or it is
  available at `p`'s entry (induction). The entry block inherits nothing (`FixOk.cand`). A block
  never inherits its own definitions, since that would give its label a smaller label. -/

namespace Backend.Stock.Proof.LoopCarry
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Backend.Proof.Prep
set_option autoImplicit false
open scoped List

/-! ## Lists -/

/-- Two elements at increasing indices form a sublist. -/
theorem pair_sublist_of_getElem? {α : Type} : ∀ {l : List α} {i j : Nat} {a b : α},
    l[i]? = some a → l[j]? = some b → i < j → [a,b] <+ l
  | [],_,_,_,_,first,_,_ => by simp at first
  | _ :: _,0,_ + 1,_,_,first,second,_ => by
    simp only [List.getElem?_cons_zero,Option.some.injEq,List.getElem?_cons_succ] at first second
    subst first
    exact (List.singleton_sublist.mpr (List.mem_of_getElem? second)).cons_cons _
  | _ :: _,_ + 1,_ + 1,_,_,first,second,lt => by
    simp only [List.getElem?_cons_succ] at first second
    exact (pair_sublist_of_getElem? first second (by omega)).cons _
  | _ :: _,_,0,_,_,_,_,lt => by omega

/-- A duplicate-free list does not hold two elements in both orders. -/
theorem not_pair_both_orders : ∀ {L : List Nat} {a b : Nat},L.Nodup → [a,b] <+ L → [b,a] <+ L → False
  | [],_,_,_,ab,_ => by simp at ab
  | c :: L,a,b,nodup,ab,ba => by
    rw [List.nodup_cons] at nodup
    rcases List.sublist_cons_iff.mp ab with abTail | ⟨r,headEq,rest⟩
    · rcases List.sublist_cons_iff.mp ba with baTail | ⟨r',headEq',_⟩
      · exact not_pair_both_orders nodup.2 abTail baTail
      · simp only [List.cons.injEq] at headEq'
        obtain ⟨rfl,-⟩ := headEq'
        exact nodup.1 (abTail.subset (by simp : b ∈ [a,b]))
    · simp only [List.cons.injEq] at headEq
      obtain ⟨rfl,rfl⟩ := headEq
      rcases List.sublist_cons_iff.mp ba with baTail | ⟨r',headEq',_⟩
      · exact nodup.1 (baTail.subset (by simp : a ∈ [b,a]))
      · simp only [List.cons.injEq] at headEq'
        obtain ⟨rfl,-⟩ := headEq'
        exact nodup.1 (rest.subset (by simp : b ∈ [b]))

/-- In a list, the elements that a projection keeps are ordered as their positions. -/
theorem index_lt_of_filterMap_sublist {α : Type} {g : α → Option Nat} {l : List α}
    (nodup : (l.filterMap g).Nodup) {i j a b : Nat} {u v : α} (first : l[i]? = some u)
    (atFirst : g u = some a) (second : l[j]? = some v) (atSecond : g v = some b)
    (ordered : [a,b] <+ l.filterMap g) : i < j := by
  rcases Nat.lt_trichotomy i j with lt | eq | gt
  · exact lt
  · subst eq
    rw [first,Option.some.injEq] at second
    subst second
    rw [atFirst,Option.some.injEq] at atSecond
    subst atSecond
    exact absurd (nodup.sublist ordered) (by simp)
  · have mapped := (pair_sublist_of_getElem? second first gt).filterMap g
    simp only [List.filterMap_cons,atFirst,atSecond,List.filterMap_nil] at mapped
    exact (not_pair_both_orders nodup ordered mapped).elim

/-- In Stock's lowered node array, original nodes are ordered as their blocks in the projection
`stockOriginals`. -/
theorem label_lt_of_sublist {nodes : Array Node} (nodup : (stockOriginals nodes).Nodup)
    {i j a b : Nat} (first : nodes[i]? = some (.original a)) (second : nodes[j]? = some (.original b))
    (ordered : [a,b] <+ stockOriginals nodes) : i < j := by
  unfold stockOriginals at nodup ordered
  exact index_lt_of_filterMap_sublist nodup (by simpa using first) rfl (by simpa using second) rfl ordered

/-! ## The depth-first search of `rpo` -/

/-- Each listed block other than the entry has a predecessor listed before it. -/
def ParentList (succs : Array (Array Nat)) (L : List Nat) : Prop :=
  ∀ x ∈ L,x ≠ 0 → ∃ q,x ∈ (succs[q]! : Array Nat).toList ∧ [q,x] <+ L

/-- The blocks of a search state: the stack from the bottom, then the postorder reversed. -/
def dSeq (st : Prep.DState) : List Nat := (st.2.2.map Prod.fst).reverse ++ st.2.1.toList.reverse

/-- Inserting a successor `s` of `b` right after `b` keeps `ParentList`. -/
theorem parentList_insert {succs : Array (Array Nat)} {A P : List Nat} {b s : Nat}
    (held : ParentList succs (A ++ b :: P)) (successor : s ∈ (succs[b]! : Array Nat).toList) :
    ParentList succs (A ++ b :: s :: P) := by
  have grow : A ++ b :: P <+ A ++ b :: s :: P :=
    ((List.sublist_cons_self s P).cons_cons b).append_left A
  intro x member nonzero
  by_cases fresh : x = s
  · subst fresh
    exact ⟨b,successor,((((List.nil_sublist P).cons_cons x).cons_cons b)).trans
      (List.sublist_append_right A _)⟩
  · have old : x ∈ A ++ b :: P := by
      simp only [List.mem_append,List.mem_cons] at member ⊢
      rcases member with member | member | member | member
      · exact Or.inl member
      · exact Or.inr (Or.inl member)
      · exact absurd member fresh
      · exact Or.inr (Or.inr member)
    obtain ⟨q,edge,ordered⟩ := held x old nonzero
    exact ⟨q,edge,ordered.trans grow⟩

/-- One step of the search keeps `ParentList` of its blocks. -/
theorem dStep_parent {succs : Array (Array Nat)} {st : Prep.DState} (held : ParentList succs (dSeq st))
    {p : Nat × Nat} {rest : List (Nat × Nat)} (top : st.2.2 = p :: rest) :
    ParentList succs (dSeq (dStep succs st p rest)) := by
  rcases st with ⟨seen,post,stack⟩
  rcases p with ⟨b,i⟩
  simp only at top
  subst top
  have old : dSeq (seen,post,(b,i) :: rest) = (rest.map Prod.fst).reverse ++ b :: post.toList.reverse := by
    simp [dSeq]
  unfold dStep
  split
  · rename_i s found
    have successor : s ∈ (succs[b]! : Array Nat).toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
    split
    · have new : dSeq (seen.set! s true,post,(s,0) :: (b,i + 1) :: rest) =
          (rest.map Prod.fst).reverse ++ b :: s :: post.toList.reverse := by
        simp [dSeq]
      rw [old] at held
      rw [new]
      exact parentList_insert held successor
    · have same : dSeq (seen,post,(b,i + 1) :: rest) = dSeq (seen,post,(b,i) :: rest) := by
        simp [dSeq]
      rw [same]
      exact held
  · have same : dSeq (seen,post.push b,rest) = dSeq (seen,post,(b,i) :: rest) := by
      simp [dSeq]
    rw [same]
    exact held

/-- Any number of search steps keeps `ParentList`. -/
theorem iterD_parent {succs : Array (Array Nat)} : ∀ (m : Nat) (st : Prep.DState),ParentList succs (dSeq st) →
    ParentList succs (dSeq (iterW (fun st : Prep.DState => st.2.2) (dStep succs) m st))
  | 0,st,held => by simpa only [iterW] using held
  | m + 1,st,held => by
    simp only [iterW]
    split
    · exact held
    · rename_i p rest top
      exact iterD_parent m _ (dStep_parent held top)

/-- **The depth-first parent**: every block of `rpo` other than the entry has a predecessor
earlier in `rpo`. -/
theorem rpo_parent {succs : Array (Array Nat)} (hin : SuccsIn succs) (h0 : succs.size ≠ 0) :
    ParentList succs (rpo succs).toList := by
  have hn : 0 < succs.size := Nat.pos_of_ne_zero h0
  have hm0 : mk ((Array.replicate succs.size false).set! 0 true) 0 :=
    mk_set.mpr (.inl ⟨rfl,by simp; omega⟩)
  have hi0 : DInv succs ((Array.replicate succs.size false).set! 0 true,#[],[(0,0)]) := by
    refine ⟨by simp,?_,by simp,?_,?_,by simp,by simp,by simp,by simp⟩
    · intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact hm0
    · intro q hq j hj; simp only [List.mem_singleton] at hq; subst hq; simp at hj
    · intro b hb
      rcases mk_set.mp hb with ⟨rfl,-⟩ | hb
      · right; simp
      · exact absurd hb (not_mk_replicate _ _)
  have hw := wsum_set (Array.replicate succs.size false) (wt succs) 0 (by simp; omega)
    (Bool.eq_false_iff.mpr (not_mk_replicate _ _)) succs.size hn
  have hle := wsum_le (Array.replicate succs.size false) (wt succs) succs.size
  have hf := pot_le_fuel succs
  obtain ⟨-,he⟩ := iterD_inv hin (dFuel succs) _ hi0 (by
    simp only [pot,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.sub_zero]
    omega)
  have held := iterD_parent (succs := succs) (dFuel succs)
    (((Array.replicate succs.size false).set! 0 true,#[],[(0,0)]) : Prep.DState) (by
      intro x member nonzero
      simp [dSeq] at member
      exact absurd member nonzero)
  rw [rpo_eq succs h0]
  generalize iterW (fun st : Prep.DState => st.2.2) (dStep succs) (dFuel succs)
    ((Array.replicate succs.size false).set! 0 true,#[],[(0,0)]) = st at he held
  rcases st with ⟨seen,post,stack⟩
  simp only at he
  subst he
  simpa [dSeq] using held

/-! ## Stock's block order -/

private theorem mapM_lookup {α β : Type} {xs : Array α} {ys : Array β}
    {step : α → Except String β} (run : xs.mapM step = .ok ys)
    {i : Nat} {y : β} (lookup : ys[i]? = some y) :
    ∃ x,xs[i]? = some x ∧ step x = .ok y := by
  obtain ⟨size,calls⟩ := amapM_ok run
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp lookup
  have hx : i < xs.size := by omega
  obtain ⟨z,call,atZ⟩ := calls i xs[i] (Array.getElem?_eq_getElem hx)
  rw [lookup] at atZ
  cases atZ
  exact ⟨xs[i],Array.getElem?_eq_getElem hx,call⟩

private theorem destination_ids (term : Clif.Terminator) :
    (destinations term).map Prod.fst = succIds term := by
  cases term <;> simp [destinations,succIds,dests,List.map_map,Function.comp_def]

/-- A successor in Stock's source table is a source successor (`succIdx`). -/
theorem stock_sourceTable_succIdx {f : Clif.Function} {source : Array (Array Nat)}
    (run : stockSourceTable f = .ok source) {q x : Nat} (member : x ∈ (source[q]! : Array Nat).toList) :
    x ∈ succIdx f q := by
  cases row : source[q]? with
  | none => simp only [getElem!_def,row] at member; cases member
  | some successors =>
    have member' : x ∈ successors.toList := by simpa only [getElem!_def,row] using member
    obtain ⟨block,found,blockRun⟩ := mapM_lookup run row
    obtain ⟨k,lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member')
    obtain ⟨destination,atDest,destRun⟩ := mapM_lookup blockRun lookup
    have blockAt : f.blocks[q]? = some block := by simpa using found
    have destinationMember : destination.1 ∈ succIds block.term := by
      rw [← destination_ids]
      apply List.mem_map.mpr
      exact ⟨destination,by simpa using Array.mem_toList_iff.mpr (Array.mem_of_getElem? atDest),rfl⟩
    cases target : f.blocks.findIdx? (·.id == destination.1) with
    | none => simp only [target,throw,throwThe,MonadExceptOf.throw] at destRun; cases destRun
    | some index =>
      simp only [target,pure,Except.pure,Except.ok.injEq] at destRun
      subst index
      unfold succIdx
      rw [blockAt]
      exact List.mem_filterMap.mpr ⟨destination.1,destinationMember,target⟩

/-- **The block-order parent**: each nonentry original node of Stock's block order has a source
predecessor whose original node has a smaller label. -/
theorem stock_blockOrder_parent {f : Clif.Function} {order : Order} (run : blockOrder f = .ok order)
    (nonempty : f.blocks.length ≠ 0) {t lt : Nat} (tag : order.nodes[lt]? = some (.original t))
    (nonentry : t ≠ 0) :
    ∃ q lq,t ∈ succIdx f q ∧ order.nodes[lq]? = some (.original q) ∧ lq < lt := by
  obtain ⟨source,computed,projected⟩ := stock_blockOrder_originals run
  obtain ⟨size,bounds⟩ := stock_sourceTable_bounds computed
  have member : t ∈ (rpo source).toList := by
    rw [← projected]
    unfold stockOriginals
    exact List.mem_filterMap.mpr ⟨.original t,Array.mem_toList_iff.mpr (Array.mem_of_getElem? tag),rfl⟩
  obtain ⟨q,successor,ordered⟩ := rpo_parent bounds (by rw [size]; exact nonempty) t member nonentry
  have qMember : q ∈ stockOriginals order.nodes := by
    rw [projected]
    exact ordered.subset (by simp)
  obtain ⟨node,nodeMember,nodeEq⟩ := List.mem_filterMap.mp qMember
  have isQ : node = .original q := by
    cases node with
    | original bi => simp only [Option.some.injEq] at nodeEq; rw [nodeEq]
    | edge => simp at nodeEq
  subst isQ
  obtain ⟨lq,qTag⟩ := List.mem_iff_getElem?.mp nodeMember
  rw [Array.getElem?_toList] at qTag
  have nodup := (stock_blockOrder_originals_nodup run nonempty).1
  exact ⟨q,lq,stock_sourceTable_succIdx computed successor,qTag,
    label_lt_of_sublist nodup qTag tag (by rw [projected]; exact ordered)⟩

/-- The lowering's block order: each nonentry original node has a source predecessor whose
original node has a smaller label. -/
theorem stock_lower_parent {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result)
    (nonempty : f.blocks.length ≠ 0) {t lt : Nat} (tag : result.order.nodes[lt]? = some (.original t))
    (nonentry : t ≠ 0) :
    ∃ q lq,t ∈ succIdx f q ∧ result.order.nodes[lq]? = some (.original q) ∧ lq < lt :=
  stock_blockOrder_parent (stock_lower_order run) nonempty tag nonentry

/-! ## Definitions precede their inheritors -/

/-- Under SSA, a value is a parameter or a result of one block only. -/
theorem def_block_unique {f : Clif.Function} (ssa : (valueDefs f).Nodup) {d q x : Nat}
    (first : x ∈ parsOf f d ∨ x ∈ defsOf f d) (second : x ∈ parsOf f q ∨ x ∈ defsOf f q) : d = q := by
  have located : ∀ {k : Nat},x ∈ parsOf f k ∨ x ∈ defsOf f k →
      ∃ (bound : k < f.blocks.length),
        x ∈ f.blocks[k].params.map (·.1) ++ f.blocks[k].body.flatMap (·.results) := by
    intro k defines
    unfold parsOf defsOf at defines
    cases block : f.blocks[k]? with
    | none => simp [block] at defines
    | some B =>
      simp only [block] at defines
      obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp block
      exact ⟨bound,by rw [eq]; exact List.mem_append.mpr defines⟩
  obtain ⟨dBound,dMember⟩ := located first
  obtain ⟨qBound,qMember⟩ := located second
  unfold valueDefs at ssa
  obtain ⟨-,pairs⟩ := List.pairwise_flatMap.mp ssa
  rcases Nat.lt_trichotomy d q with lt | eq | gt
  · exact (List.pairwise_iff_getElem.mp pairs d q dBound qBound lt x dMember x qMember rfl).elim
  · exact eq
  · exact (List.pairwise_iff_getElem.mp pairs q d qBound dBound gt x qMember x dMember rfl).elim

/-- **`DefBefore` for every Stock lowering of an SSA function.** -/
theorem stock_lower_defBefore_ssa {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (ssa : (valueDefs f).Nodup) : DefBefore f result := by
  have ordered := stock_lower_order run
  have fixed := inFix_fixOk (f := f) (ctx := result.ctx) (gn := id)
  have key : ∀ (lt t : Nat),result.order.nodes[lt]? = some (Node.original t) → ∀ x : Nat,
      x ∈ (availIn f result.ctx).getD t [] → ∀ (d ld : Nat),result.order.nodes[ld]? = some (Node.original d) →
      x ∈ parsOf f d ∨ x ∈ defsOf f d → ld < lt := by
    intro lt
    induction lt using Nat.strongRecOn with
    | ind lt ih =>
      intro t tag x incoming d ld dTag defines
      obtain ⟨one,bound,-⟩ := fixed.cand t x incoming
      have nonempty : f.blocks.length ≠ 0 := by omega
      obtain ⟨q,lq,successor,qTag,lower⟩ := stock_blockOrder_parent ordered nonempty tag (by omega)
      rcases fixed.out t x incoming q successor with parameter | defined | inherited
      · have same := def_block_unique ssa defines (Or.inl parameter)
        subst same
        have := stock_blockOrder_original_unique ordered nonempty dTag qTag
        omega
      · have same := def_block_unique ssa defines (Or.inr defined)
        subst same
        have := stock_blockOrder_original_unique ordered nonempty dTag qTag
        omega
      · have := ih lq lower q qTag x inherited d ld dTag defines
        omega
  intro d t ld lt x dTag tTag incoming defines
  exact key lt t tTag x incoming d ld dTag defines

/-- **`DefBefore` for every Stock lowering of a dominated function.** -/
theorem stock_lower_defBefore {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f) : DefBefore f result :=
  stock_lower_defBefore_ssa run dominated.ssa

/-- A block does not inherit its own parameters or results. -/
theorem stock_lower_not_inherit_own {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (ssa : (valueDefs f).Nodup) {t lt x : Nat}
    (tag : result.order.nodes[lt]? = some (.original t))
    (incoming : x ∈ (availIn f result.ctx).getD t []) : x ∉ parsOf f t ∧ x ∉ defsOf f t := by
  have before := stock_lower_defBefore_ssa run ssa
  refine ⟨fun parameter => ?_,fun defined => ?_⟩
  · have := before t t lt lt x tag tag incoming (Or.inl parameter)
    omega
  · have := before t t lt lt x tag tag incoming (Or.inr defined)
    omega

/-- `defCarry_cover` without the `DefBefore` premise: the definition carry covers every source
edge of a Stock lowering of an SSA function, forward or back. -/
theorem stock_defCarry_cover {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {label : Nat} (tag : result.order.nodes[label]? = some (.original event.block))
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    {targetLabel : Nat} (targetTag : result.order.nodes[targetLabel]? = some (.original next.block))
    {targetBlock : Clif.Block} (destination : f.blocks[next.block]? = some targetBlock)
    (successor : next.block ∈ succIdx f event.block) :
    EdgeCover f result next.block (targetBlock.params.map (·.1)) next.output.state
      (defCarry f result next.block) term.output.state (defCarry f result event.block) :=
  defCarry_cover run scope (stock_lower_defBefore_ssa run ssa) events split tag nextEvent targetTag
    destination successor

end Backend.Stock.Proof.LoopCarry
