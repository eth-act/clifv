module

public import FV.Backend.Proof.PerEdgeSpillEntryFixture

@[expose] public section

namespace Backend.Stock.Proof.IndexedInstFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.SpillEntryFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def firstInstructions (indirect : Bool) : Array MInst := #[
  .movWide .movZ (.vreg (ordinaryV indirect) .int) ⟨9,0⟩ .size64,
  if indirect then .movWide .movZ (.vreg (retV indirect+8) .int) ⟨4096,0⟩ .size64
    else .loadExtNameGot (.vreg (retV indirect+8) .int) "callee",
  last indirect]
def classesB (p : EdgeVCode) : Bool := p.code.blocks.all fun vb => vb.insts.all fun i =>
  match i.operands with
  | .error _ => false
  | .ok ops => ops.all fun o => decide (p.code.classes[o.vreg]? = some o.cls)
def Layout (indirect : Bool) (p : EdgeVCode) : Prop :=
  (p.code.blocks[0]!).insts = firstInstructions indirect ∧
  (p.code.blocks[1]!).insts = #[.rets [(.vreg (retV indirect+3) .int,.x 0)]] ∧
  (p.code.blocks[2]!).insts = #[.rets [(.vreg (retV indirect+5) .int,.x 0)]] ∧ classesB p = true
private instance layoutDecidable (indirect : Bool) (p : EdgeVCode) : Decidable (Layout indirect p) := by
  unfold Layout
  infer_instance
private def view (indirect : Bool) : Except String Bool := do
  let result ← Stock.lower (function indirect)
  let p ← prepareAt result.code result.edgeArgs
  pure (decide (Layout indirect p))
private theorem observed (indirect : Bool) : (view indirect).toOption = some true := by cases indirect <;> decide +kernel

/-- Cached actual instruction/class layout for complete direct/indirect Stock
TryCall sources. Kernel evaluation is isolated here so subsequent invariant
proofs reuse this complete fixture instead of re-evaluating lowering. -/
theorem indexed_inst_layout {indirect : Bool} {result : Result} {p : EdgeVCode}
    (run : Stock.lower (function indirect) = .ok result)
    (raw : prepareAt result.code result.edgeArgs = .ok p) : Layout indirect p := by
  have layout := observed indirect
  unfold view at layout
  rw [run] at layout
  simp only [bind,Except.bind] at layout
  rw [raw] at layout
  simpa only [bind,Except.bind,pure,Except.pure,Except.toOption,Option.some.injEq,decide_eq_true_eq] using layout

end Backend.Stock.Proof.IndexedInstFixture
