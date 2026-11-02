import FV.Backend.Proof.StockFenceMetadataModel

namespace Backend.Stock.Proof.FenceColors
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

private theorem set_keeps_nonzero (a : Array Nat) (i n q : Nat) (positive : n ≠ 0)
    (old : a[q]! ≠ 0) : (a.set! i n)[q]! ≠ 0 := by
  by_cases same : q = i
  · subst q
    by_cases inside : i < a.size
    · simp [getElem!_def,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,inside,positive]
    · simpa [Array.set!_eq_setIfInBounds,Array.setIfInBounds,inside] using old
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm same)]
    exact old

private theorem body_facts (start : Nat) (s : Colors) (xs : List (Clif.Stmt × Nat))
    (positive : 0 < s.2) :
    0 < (xs.foldl (bodyNext start) s).2 ∧
      (xs.foldl (bodyNext start) s).1.size = s.1.size ∧
      ∀ q, s.1[q]! ≠ 0 → (xs.foldl (bodyNext start) s).1[q]! ≠ 0 := by
  induction xs generalizing s with
  | nil => exact ⟨positive,rfl,fun _ h => h⟩
  | cons x xs ih =>
    have one : 0 < (bodyNext start s x).2 ∧ (bodyNext start s x).1.size = s.1.size ∧
        ∀ q,s.1[q]! ≠ 0 → (bodyNext start s x).1[q]! ≠ 0 := by
      unfold bodyNext
      split
      · exact ⟨by omega,by simp,fun q old => set_keeps_nonzero _ _ _ q (by omega) old⟩
      · exact ⟨positive,rfl,fun _ h => h⟩
    have tail := ih (bodyNext start s x) one.1
    exact ⟨tail.1,tail.2.1.trans one.2.1,fun q old => tail.2.2 q (one.2.2 q old)⟩

private theorem body_target (start : Nat) (s : Colors) (xs : List (Clif.Stmt × Nat))
    (positive : 0 < s.2) {stm : Clif.Stmt} {j : Nat}
    (member : (stm,j) ∈ xs) (barrier : colored stm.inst = true)
    (inside : start+j < s.1.size) :
    (xs.foldl (bodyNext start) s).1[start+j]! ≠ 0 := by
  induction xs generalizing s with
  | nil => cases member
  | cons x xs ih =>
    rcases List.mem_cons.mp member with same | member
    · subst x
      have hit : (bodyNext start s (stm,j)).1[start+j]! ≠ 0 := by
        simp [bodyNext,barrier,getElem!_def,Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds,inside,Nat.ne_of_gt positive]
      have next : 0 < (bodyNext start s (stm,j)).2 := by simp [bodyNext,barrier]
      exact (body_facts start _ xs next).2.2 _ hit
    · have one := body_facts start s [x] positive
      have next : 0 < (bodyNext start s x).2 := one.1
      have size : (bodyNext start s x).1.size = s.1.size := one.2.1
      exact ih _ next member (by rw [size]; exact inside)

private theorem block_facts (ranges : Array (Nat × Nat)) (s : Colors) (x : Clif.Block × Nat) :
    (blockNext ranges s x).1.size = s.1.size ∧
      ∀ q,s.1[q]! ≠ 0 → (blockNext ranges s x).1[q]! ≠ 0 := by
  have body := body_facts ranges[x.2]!.1 (s.1,s.2+1) x.1.body.zipIdx (by omega)
  constructor
  · simpa [blockNext] using body.2.1
  · intro q old
    exact set_keeps_nonzero _ _ _ q (Nat.ne_of_gt body.1) (body.2.2 q old)

private theorem blocks_keep (ranges : Array (Nat × Nat)) (s : Colors) (xs : List (Clif.Block × Nat)) :
    (xs.foldl (blockNext ranges) s).1.size = s.1.size ∧
      ∀ q,s.1[q]! ≠ 0 → (xs.foldl (blockNext ranges) s).1[q]! ≠ 0 := by
  induction xs generalizing s with
  | nil => exact ⟨rfl,fun _ h => h⟩
  | cons x xs ih =>
    have one := block_facts ranges s x
    have tail := ih (blockNext ranges s x)
    exact ⟨tail.1.trans one.1,fun q old => tail.2 q (one.2 q old)⟩

private theorem blocks_target (ranges : Array (Nat × Nat)) (s : Colors) (xs : List (Clif.Block × Nat))
    {b : Clif.Block} {bi j : Nat} {stm : Clif.Stmt}
    (block : (b,bi) ∈ xs) (statement : (stm,j) ∈ b.body.zipIdx)
    (barrier : colored stm.inst = true) (inside : ranges[bi]!.1+j < s.1.size) :
    (xs.foldl (blockNext ranges) s).1[ranges[bi]!.1+j]! ≠ 0 := by
  induction xs generalizing s with
  | nil => cases block
  | cons x xs ih =>
    rcases List.mem_cons.mp block with same | block
    · subst x
      have body := body_target ranges[bi]!.1 (s.1,s.2+1) b.body.zipIdx
        (by omega) statement barrier inside
      have facts := body_facts ranges[bi]!.1 (s.1,s.2+1) b.body.zipIdx (by omega)
      have hit : (blockNext ranges s (b,bi)).1[ranges[bi]!.1+j]! ≠ 0 :=
        set_keeps_nonzero _ _ _ _ (Nat.ne_of_gt facts.1) body
      exact (blocks_keep ranges _ xs).2 _ hit
    · have size := (block_facts ranges s x).1
      exact ih _ block (by rw [size]; exact inside)

/-- Every real colored source slot receives a nonzero metadata color.
Later body and terminator writes preserve it without any purity restriction. -/
theorem sourceMetadata_colored_positive (ctx : Ctx) (ranges : Array (Nat × Nat))
    {b : Clif.Block} {bi j : Nat} {stm : Clif.Stmt}
    (block : ctx.func.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (barrier : colored stm.inst = true) (inside : ranges[bi]!.1+j < ctx.insts.size) :
    (sourceMetadata ctx ranges).entryColor[ranges[bi]!.1+j]! ≠ 0 := by
  rw [sourceMetadata_projection]
  apply blocks_target ranges (Array.replicate ctx.insts.size 0,0) ctx.func.blocks.zipIdx
  · exact List.mem_zipIdx_iff_getElem?.mpr block
  · exact List.mem_zipIdx_iff_getElem?.mpr statement
  · exact barrier
  · simpa using inside

end Backend.Stock.Proof.FenceColors
