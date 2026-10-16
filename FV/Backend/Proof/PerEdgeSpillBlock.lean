import FV.Backend.Proof.PerEdgeSpillInst
import FV.Backend.Proof.PerEdgeSpillRoutes

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Every actual body item before the last instruction passes the indexed
checker and re-establishes dense-home availability. This is the real allocator
body, with its selected-copy placement condition; the last instruction and
entry stores/copies are separate stages of the whole-block invariant. -/
theorem spill_body_prefix_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (slots : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    (saved : c.rf.saved = calleeSaved)
    {succs preds : Array (Array Nat)} {b : Nat} {vb : VBlock} (block : vc.blocks[b]? = some vb)
    (static : ∀ (k : Nat) (i : MInst),vb.insts[k]? = some i → SpillInstOk i)
    (classes : ∀ (k : Nat) (i : MInst) (ops : Array Operand),vb.insts[k]? = some i →
      i.operands = .ok ops → ∀ o ∈ ops.toList,vc.classes[o.vreg]? = some o.cls)
    {A : Nat → Bool}
    (uses : ∀ (k : Nat) (i : MInst) (ops : Array Operand),vb.insts[k]? = some i →
      i.operands = .ok ops → ∀ o ∈ ops.toList,o.kind = .use → availAt vb.insts A k o.vreg = true)
    {n : Nat} (beforeLast : n < vb.insts.size) {a : AState} (good : GoodAt vc edges A a) :
    Runs c vb 0 ((vb.insts.toList.take n).zipIdx.flatMap (bodyItem vc edges succs preds b vb)) a
      (fun k' a' => k' = n ∧ GoodAt vc edges (availAt vb.insts A n) a') := by
  induction n with
  | zero => exact Runs.nil ⟨rfl,good⟩
  | succ n ih =>
    have nBound : n < vb.insts.size := by omega
    have atInst : vb.insts[n]? = some vb.insts[n] := Array.getElem?_eq_getElem nBound
    have prefixLength : (vb.insts.toList.take n).length = n := by simp only [List.length_take,Array.length_toList]; omega
    rw [List.take_add_one,Array.getElem?_toList,atInst,List.zipIdx_append,List.flatMap_append,prefixLength]
    simp only [List.zipIdx_cons,List.zipIdx_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,Option.toList_some,Nat.zero_add]
    have noCopies : bodyItem vc edges succs preds b vb (vb.insts[n],n) =
        spillInstAt (spillHomesAt vc edges) n vb.insts[n] := by
      simp only [bodyItem,show (n+1 == vb.insts.size) = false from by simp only [beq_eq_false_iff_ne]; omega,
        Bool.false_eq_true,ite_false,List.nil_append]
    rw [noCopies]
    refine Runs.append (ih nBound) fun k mid ⟨same,midGood⟩ => ?_
    subst k
    obtain ⟨ops,operands,valid,returns⟩ := static n vb.insts[n] atInst
    refine (spillInstAt_runs slots saved block atInst operands valid returns
      (fun last => by omega) (classes n _ ops atInst operands) (uses n _ ops atInst operands) midGood).mono ?_
    intro k final ⟨same,finalGood,_⟩
    refine ⟨same,?_⟩
    rw [availAt_succ atInst]
    exact finalGood

end Backend.Proof.PerEdgeSpill
