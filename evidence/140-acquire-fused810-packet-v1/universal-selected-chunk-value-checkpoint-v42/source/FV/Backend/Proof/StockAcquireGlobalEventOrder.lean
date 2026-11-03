import FV.Backend.Proof.StockAcquireSourceEvents

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Adjacent layout intervals are disjoint for every original source block. -/
theorem block_layout_before (blocks : List Clif.Block) (i j : Nat) (first : Clif.Block)
    (found : blocks[i]? = some first) (before : i < j) :
    bsl blocks i + first.body.length + 1 ≤ bsl blocks j := by
  induction blocks generalizing i j with
  | nil => simp at found
  | cons block blocks ih =>
    cases i with
    | zero =>
      have same : first = block := by simpa using found.symm
      subst first
      cases j with
      | zero => omega
      | succ j => simp only [bsl_zero,bsl_cons]; omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have tail : blocks[i]? = some first := by simpa using found
        have bound := ih i j tail (by omega)
        simp only [bsl_cons]
        omega

/-- Indexed traversal preserves strict block order without a supplied ordering certificate. -/
theorem source_blocks_index_order {α : Type} (xs : List α) (offset : Nat) :
    (xs.zipIdx offset).Pairwise (fun a b => a.2 < b.2) := by
  induction xs generalizing offset with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons,List.pairwise_cons]
    refine ⟨?_,ih (offset+1)⟩
    intro y member
    have bounds := List.le_snd_of_mem_zipIdx member
    omega

/-- All events in one block remain inside its allocated source interval. -/
theorem block_color_event_bounds {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (bi : Nat) (block : Clif.Block) (blockAt : f.blocks[bi]? = some block) (target : Nat)
    (member : some target ∈ blockColorEvents ranges (block,bi)) :
    blockStart f bi ≤ target ∧ target ≤ blockStart f bi+block.body.length := by
  rcases (block_color_events_member built bi block blockAt target).1 member with body | term
  · obtain ⟨stm,index,found,_,same⟩ := body
    obtain ⟨bounds,_⟩ := List.getElem?_eq_some_iff.mp found
    omega
  · omega

/-- Within each real source block, metadata effects have strict source-slot order. -/
theorem block_color_event_order {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (bi : Nat) (block : Clif.Block) (blockAt : f.blocks[bi]? = some block) :
    (blockColorEvents ranges (block,bi)).Pairwise sourceEventBefore := by
  have rangesAt := (ctxSpec_of built).ranges bi block blockAt
  have rangesValue : ranges[bi]! = (blockStart f bi,blockStart f bi+block.body.length+1) := by
    simp only [getElem!_def,rangesAt,Option.getD_some]
  simp only [blockColorEvents,rangesValue,Nat.add_sub_cancel,List.pairwise_cons]
  refine ⟨?_,List.pairwise_append.mpr ⟨body_color_events_order _ 0 _,by simp,?_⟩⟩
  · intro event member i impossible
    cases impossible
  · intro first member second singleton i same j equal
    have secondEq : second = some (blockStart f bi+block.body.length) := by simpa using singleton
    have jEq : j = blockStart f bi+block.body.length := (Option.some.inj (secondEq.symm.trans equal)).symm
    have bounds := body_color_events_bounds (blockStart f bi) 0 block.body i (same ▸ member)
    omega

/-- The complete original metadata event sequence has strict source-slot order. -/
theorem source_color_event_order {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial)) :
    (sourceColorEvents ctx ranges).Pairwise sourceEventBefore := by
  have spec := ctxSpec_of built
  rw [sourceColorEvents,spec.func]
  refine List.pairwise_flatMap.mpr ⟨?_,?_⟩
  · intro x member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    exact block_color_event_order built x.2 x.1 found
  · apply List.Pairwise.imp_of_mem (p := source_blocks_index_order f.blocks 0)
    intro a b aMember bMember before first firstMember second secondMember i firstEq j secondEq
    have aFound := List.mem_zipIdx_iff_getElem?.mp aMember
    have bFound := List.mem_zipIdx_iff_getElem?.mp bMember
    have aBounds := block_color_event_bounds built a.2 a.1 aFound i (firstEq ▸ firstMember)
    have bBounds := block_color_event_bounds built b.2 b.1 bFound j (secondEq ▸ secondMember)
    have separation := block_layout_before f.blocks a.2 b.2 a.1 aFound before
    simp only [blockStart_eq] at aBounds bBounds
    omega

end Backend.Stock.Proof.Acquire810
