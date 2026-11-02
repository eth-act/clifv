import FV.Backend.Proof.StockContext
import FV.Backend.Proof.LowerLoopCtx
import FV.Backend.Lowering.StockScalarAdd
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 4096
private abbrev ColorState := Array Nat × Array Nat × Array (List Nat) × Nat
private def bodyStep (start bi : Nat) (x : Clif.Stmt × Nat) (s : ColorState) : Id (ForInStep ColorState) :=
  if colored x.1.inst then
    pure (.yield (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
      s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1))
  else pure (.yield (s.1.set! (start+x.2) bi,s.2.1,
    s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2))
private theorem body_colors (start bi : Nat) (xs : List (Clif.Stmt × Nat))
    (quiet : ∀ x ∈ xs, colored x.1.inst = false) (s : ColorState) :
    ((forIn xs s (bodyStep start bi)).run).2.1 = s.2.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hx := quiet x (by simp)
    have tail : ∀ y ∈ xs, colored y.1.inst = false := fun y hy => quiet y (by simp [hy])
    rw [List.forIn_cons]
    simp only [bodyStep,hx,Bool.false_eq_true,ite_false]
    change ((forIn xs (s.1.set! (start+x.2) bi,s.2.1,
      s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2) (bodyStep start bi)).run).2.1 = s.2.1
    exact ih tail _
/-- The actual metadata loop leaves every ordinary slot uncolored for an
arbitrary pure single-block body, without fixed instruction identities. -/
theorem sourceMetadata_pure_single_block (ctx : Ctx) (ranges : Array (Nat × Nat)) (b : Clif.Block)
    (blocks : ctx.func.blocks = [b]) (range : ranges[0]! = (0,b.body.length+1))
    (pureBody : ∀ s ∈ b.body, colored s.inst = false) (q : Nat) (inside : q < b.body.length)
    : (sourceMetadata ctx ranges).entryColor[q]! = 0 := by
  have quiet : ∀ x ∈ b.body.zipIdx, colored x.1.inst = false :=
    fun x hx => pureBody x.1 (List.fst_mem_of_mem_zipIdx hx)
  have inner := body_colors ranges[0]!.1 0 b.body.zipIdx quiet
    (Array.replicate ctx.insts.size 0,Array.replicate ctx.insts.size 0,
      Array.replicate ctx.insts.size [],0+1)
  simp only [sourceMetadata,blocks,List.zipIdx_cons,List.zipIdx_nil,
    List.forIn_cons,List.forIn_nil,Id.run_bind,Id.run_pure]
  change (((forIn b.body.zipIdx _ (bodyStep ranges[0]!.1 0)).run).2.1.set!
    (ranges[0]!.2-1) _)[q]! = 0
  rw [inner]
  have different : q ≠ ranges[0]!.2-1 := by rw [range]; simp only; omega
  rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm different)]
  by_cases bound : q < ctx.insts.size <;>
    simp [getElem!_def,Array.getElem?_replicate,bound]

/-- Original successful context construction derives the pure metadata facts;
no scan certificate, extra input check or concrete native-data premise is used. -/
theorem buildCtx_pure_single_block {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {b : Clif.Block} (blocks : f.blocks = [b])
    (pureBody : ∀ s ∈ b.body, colored s.inst = false) {q : Nat} (inside : q < b.body.length) :
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
    exact sourceMetadata_pure_single_block original ranges b originalBlocks range pureBody q inside
  · change (Array.replicate original.insts.size false)[q]! = false
    by_cases bound : q < original.insts.size <;>
      simp [getElem!_def,Array.getElem?_replicate,bound]

private def pureFunction := ScalarAdd.source "pure_metadata" .systemVI64 []
private def pureResult : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx pureFunction).toOption.getD ({func := pureFunction, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := []},#[],default)
private theorem pureBuild : Stock.buildCtx pureFunction = .ok pureResult := rfl

/-- A successful nonempty arithmetic source inhabits the general metadata and
context-construction theorems using only ordinary kernel reduction. -/
theorem buildCtx_pure_single_block_witness :
    Stock.buildCtx pureFunction = .ok pureResult ∧
    pureResult.2.2.entryColor[0]! = 0 ∧ pureResult.2.2.sunk[0]! = false := by
  refine ⟨pureBuild,?_⟩
  apply buildCtx_pure_single_block pureBuild (b := pureFunction.blocks[0]!) rfl
  · intro stm member
    change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
    have same := List.mem_singleton.mp member
    subst stm
    rfl
  · decide
end Backend.Stock.Proof
