import FV.Backend.Proof.StockPureSourceColors
import FV.Backend.Proof.StockPureDriverUnsunk
namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
private abbrev ColorState := Array Nat × Array Nat × Array (List Nat) × Nat
private def bodyStep (start bi : Nat) (x : Clif.Stmt × Nat) (s : ColorState) : Id (ForInStep ColorState) :=
  if colored x.1.inst then
    pure (.yield (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
      s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1))
  else pure (.yield (s.1.set! (start+x.2) bi,s.2.1,
    s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2))
private theorem body_color_at (start bi q : Nat) (xs : List (Clif.Stmt × Nat))
    (separate : ∀ x ∈ xs, colored x.1.inst = true → start+x.2 ≠ q) (s : ColorState) :
    ((forIn xs s (bodyStep start bi)).run).2.1[q]! = s.2.1[q]! := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have tail : ∀ y ∈ xs, colored y.1.inst = true → start+y.2 ≠ q :=
      fun y hy => separate y (List.mem_cons_of_mem _ hy)
    rw [List.forIn_cons]
    cases coloredHere : colored x.1.inst with
    | false =>
      simp only [bodyStep,coloredHere,Bool.false_eq_true,ite_false]
      exact ih tail _
    | true =>
      simp only [bodyStep,coloredHere,ite_true]
      change ((forIn xs (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
        s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1) (bodyStep start bi)).run).2.1[q]! = s.2.1[q]!
      rw [ih tail]
      exact Array.getElem!_set!_ne _ _ _ _ (separate x (List.mem_cons_self ..) coloredHere)

/-- Only the selected source position must be quiet. Other instructions may
carry division/trap colors; their distinct indexed writes cannot color it. -/
theorem sourceMetadata_quiet_single_block (ctx : Ctx) (ranges : Array (Nat × Nat)) (b : Clif.Block)
    (blocks : ctx.func.blocks = [b]) (range : ranges[0]! = (0,b.body.length+1))
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) : (sourceMetadata ctx ranges).entryColor[q]! = 0 := by
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have sourceAt : b.body[q] = stm := by
    have found := List.getElem?_eq_getElem inside
    rw [statement] at found
    exact (Option.some.inj found).symm
  have separate : ∀ x ∈ b.body.zipIdx, colored x.1.inst = true → ranges[0]!.1+x.2 ≠ q := by
    intro x member coloredHere equal
    have index : x.2 = q := by simpa only [range,Nat.zero_add] using equal
    have item := (List.mem_zipIdx member).2.2
    simp only [Nat.sub_zero,index] at item
    have same : x.1 = stm := item.trans sourceAt
    rw [same,quiet] at coloredHere
    cases coloredHere
  have inner := body_color_at ranges[0]!.1 0 q b.body.zipIdx separate
    (Array.replicate ctx.insts.size 0,Array.replicate ctx.insts.size 0,
      Array.replicate ctx.insts.size [],0+1)
  simp only [sourceMetadata,blocks,List.zipIdx_cons,List.zipIdx_nil,
    List.forIn_cons,List.forIn_nil,Id.run_bind,Id.run_pure]
  change (((forIn b.body.zipIdx _ (bodyStep ranges[0]!.1 0)).run).2.1.set!
    (ranges[0]!.2-1) _)[q]! = 0
  have different : ranges[0]!.2-1 ≠ q := by rw [range]; simp only; omega
  rw [Array.getElem!_set!_ne _ _ _ _ different,inner]
  by_cases bound : q < ctx.insts.size <;> simp [getElem!_def,Array.getElem?_replicate,bound]

theorem buildCtx_quiet_single_block {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {b : Clif.Block} (blocks : f.blocks = [b])
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) :
    initial.entryColor[q]! = 0 ∧ initial.sunk[q]! = false := by
  obtain ⟨original,st0,requests,oldBuild,_,finished⟩ := buildCtx_allocation build
  have spec := ctxSpec_of oldBuild
  have originalBlocks : original.func.blocks = [b] := by rw [spec.func]; exact blocks
  have range : ranges[0]! = (0,b.body.length+1) := by
    have found : f.blocks[0]? = some b := by rw [blocks]; rfl
    have r := spec.ranges 0 b found
    simp only [getElem!_def,r,Option.getD_some]
    simp [blockStart]
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only at state
  rw [state]
  constructor
  · change (sourceMetadata original ranges).entryColor[q]! = 0
    exact sourceMetadata_quiet_single_block original ranges b originalBlocks range statement quiet
  · change (Array.replicate original.insts.size false)[q]! = false
    by_cases bound : q < original.insts.size <;>
      simp [getElem!_def,Array.getElem?_replicate,bound]


/-- Actual whole-driver unsunkness at one quiet source slot remains available
when other slots have division/trap colors. -/
theorem stock_lower_quiet_single_block_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {b : Clif.Block} (blocks : f.blocks = [b])
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) :
    result.initial.entryColor[q]! = 0 ∧ result.final.sunk[q]! = false ∧
      ∀ event ∈ result.blockScans.toList, event.input.sunk[q]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[q]! = false ∧ record.output.state.sunk[q]! = false := by
  have built : ∃ ctx ranges, Stock.buildCtx f = .ok (ctx,ranges,result.initial) := by
    have actual := run
    unfold Stock.lower at actual
    dsimp only at actual
    repeat' first
      | (solve | cases actual)
      | simp only [bind,Except.bind,pure,Except.pure] at actual
      | split at actual
    cases actual
    rename_i _ built hbuild _ order horder _ driver hdriver
    exact ⟨built.1,built.2.1,hbuild⟩
  obtain ⟨ctx,ranges,build⟩ := built
  obtain ⟨zero,safe⟩ := buildCtx_quiet_single_block build blocks statement quiet
  obtain ⟨final,events⟩ := stock_lower_zeroColorLe run
  refine ⟨zero,final.2 q zero safe,?_⟩
  intro event member
  obtain ⟨pre,records⟩ := events event member
  refine ⟨pre.2 q zero safe,?_⟩
  intro record retained
  obtain ⟨a,b⟩ := records record retained
  exact ⟨a.2 q zero safe,b.2 q zero safe⟩

end Backend.Stock.Proof.QuietSourceColors
#print axioms Backend.Stock.Proof.QuietSourceColors.sourceMetadata_quiet_single_block

#print axioms Backend.Stock.Proof.QuietSourceColors.buildCtx_quiet_single_block

#print axioms Backend.Stock.Proof.QuietSourceColors.stock_lower_quiet_single_block_unsunk
