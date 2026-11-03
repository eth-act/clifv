import FV.Backend.Proof.StockAcquireEventOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Metadata events name exactly the colored statements in their source sequence. -/
theorem body_color_events_member (start : Nat) (xs : List (Clif.Stmt × Nat)) (target : Nat) :
    some target ∈ bodyColorEvents start xs ↔
      ∃ stm index, (stm,index) ∈ xs ∧ Stock.colored stm.inst = true ∧ target = start+index := by
  induction xs with
  | nil => simp [bodyColorEvents]
  | cons x xs ih =>
    rcases x with ⟨stm,index⟩
    cases effect : Stock.colored stm.inst with
    | false =>
      simp only [bodyColorEvents,effect,Bool.false_eq_true,ite_false]
      constructor
      · intro member
        obtain ⟨s,i,located,colored,same⟩ := ih.mp member
        exact ⟨s,i,List.mem_cons_of_mem _ located,colored,same⟩
      · rintro ⟨s,i,located,colored,same⟩
        rcases List.mem_cons.mp located with equal | tail
        · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
          simp [effect] at colored
        · exact ih.mpr ⟨s,i,tail,colored,same⟩
    | true =>
      simp only [bodyColorEvents,effect,ite_true,List.mem_cons]
      constructor
      · intro member
        rcases member with equal | tail
        · exact ⟨stm,index,Or.inl rfl,effect,Option.some.inj equal⟩
        · obtain ⟨s,i,located,colored,same⟩ := ih.mp tail
          exact ⟨s,i,Or.inr located,colored,same⟩
      · rintro ⟨s,i,located,colored,same⟩
        rcases located with equal | tail
        · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
          exact Or.inl (congrArg some same)
        · exact Or.inr (ih.mpr ⟨s,i,tail,colored,same⟩)

/-- Every body event remains inside its original source interval. -/
theorem body_color_events_bounds (start offset : Nat) (body : List Clif.Stmt) (target : Nat)
    (member : some target ∈ bodyColorEvents start (body.zipIdx offset)) :
    start+offset ≤ target ∧ target < start+offset+body.length := by
  obtain ⟨stm,index,located,_,same⟩ := (body_color_events_member start _ target).1 member
  have bounds := List.mem_zipIdx located
  omega

/-- Event order ignores block boundaries while retaining strict source-slot order. -/
def sourceEventBefore (first second : Option Nat) : Prop :=
  ∀ i, first = some i → ∀ j, second = some j → i < j

/-- The actual colored body subsequence keeps its source positions in strict order. -/
theorem body_color_events_order (start offset : Nat) (body : List Clif.Stmt) :
    (bodyColorEvents start (body.zipIdx offset)).Pairwise sourceEventBefore := by
  induction body generalizing offset with
  | nil => simp [bodyColorEvents]
  | cons stm body ih =>
    rw [List.zipIdx_cons]
    cases effect : Stock.colored stm.inst with
    | false => simpa [bodyColorEvents,effect] using ih (offset+1)
    | true =>
      simp only [bodyColorEvents,effect,ite_true,List.pairwise_cons]
      refine ⟨?_,ih (offset+1)⟩
      intro event member i same j equal
      have iEq : i = start+offset := Option.some.inj same.symm
      subst event
      have bounds := body_color_events_bounds start (offset+1) body j member
      omega

/-- A block event names an actual colored statement or the block terminator. -/
theorem block_color_events_member {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (bi : Nat) (block : Clif.Block) (blockAt : f.blocks[bi]? = some block) (target : Nat) :
    some target ∈ blockColorEvents ranges (block,bi) ↔
      (∃ stm index, block.body[index]? = some stm ∧ Stock.colored stm.inst = true ∧
        target = blockStart f bi+index) ∨ target = blockStart f bi+block.body.length := by
  have rangesAt := (ctxSpec_of built).ranges bi block blockAt
  have rangesValue : ranges[bi]! = (blockStart f bi,blockStart f bi+block.body.length+1) := by
    simp only [getElem!_def,rangesAt,Option.getD_some]
  simp only [blockColorEvents,rangesValue,List.mem_cons,List.mem_append,List.mem_singleton]
  rw [body_color_events_member]
  simp only [List.mem_zipIdx_iff_getElem?,Nat.add_sub_cancel]
  constructor <;> intro h <;> grind

end Backend.Stock.Proof.Acquire810
