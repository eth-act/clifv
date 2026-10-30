import FV.Backend.Proof.PerEdgeSpillRoutes
import FV.Backend.Proof.PerEdgeSpillStateAt

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Real return blocks pass runBlock after the proved entry prefix. The actual
allocated block, empty CFG successor row, absence of jump copies, restores,
loads and return instruction are all connected to that prefix. -/
theorem spill_return_block_after_entry {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (code : c.vc = vc) (allocated : c.rf = spillAllocAt vc edges)
    {preds : Array (Array Nat)} (cfg : vc.cfg = .ok (c.succs,preds))
    {target : Nat} {tb : VBlock} {us : List (Reg × Reg)}
    (targetBlock : vc.blocks[target]? = some tb) (notEntry : target ≠ 0) (instructions : tb.insts = #[.rets us])
    (static : SpillInstOk (.rets us))
    (classes : ∀ ops,(MInst.rets us).operands = .ok ops → ∀ o ∈ ops.toList,vc.classes[o.vreg]? = some o.cls)
    {wanted : Nat → Bool} (uses : ∀ ops,(MInst.rets us).operands = .ok ops → ∀ o ∈ ops.toList,
      o.kind = .use → wanted o.vreg = true)
    {e : AState} (entry : Spill.Runs c tb 0
      (spillEntryStoresAt (spillHomesAt vc edges) vc c.succs preds target ++
       spillEntryCopiesAt (spillHomesAt vc edges) vc edges c.succs preds target) e
      (fun k a => k = 0 ∧ GoodAt vc edges wanted a)) :
    ∃ final,c.runBlock target e = .ok final ∧ GoodAt vc edges (availInst (.rets us) wanted) final ∧
      (bodyStateAt vc edges (availInst (.rets us) wanted)).le final = true := by
  have slots : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges := by
    rw [allocated]; exact (spillAllocAt_storage _ _).1
  have saved : c.rf.saved = calleeSaved := by rw [allocated]; unfold spillAllocAt; split <;> rfl
  obtain ⟨T,ts,last,_,successors,count,_⟩ := (Prep.cfg_spec cfg).blk target tb targetBlock
  have lastRet : tb.insts.back? = some (.rets us) := by rw [instructions]; rfl
  rw [lastRet] at last
  cases last
  have tsEmpty : ts = #[] := Array.eq_empty_iff_size_eq_zero.mpr count
  rw [tsEmpty] at successors
  have noCopies : jumpCopies vc edges c.succs preds target = [] := by
    unfold jumpCopies
    rw [successors]
    rfl
  have body : tb.insts.toList.zipIdx.flatMap (bodyItem vc edges c.succs preds target tb) =
      spillInstAt (spillHomesAt vc edges) 0 (.rets us) := by
    rw [instructions]
    simp [bodyItem,noCopies]
  have installed := spillAllocAt_block (edges := edges) cfg targetBlock
  rw [← allocated] at installed
  have noSaves : (target == 0) = false := by simpa using notEntry
  simp only [noSaves,Bool.false_eq_true,ite_false,List.nil_append,body,List.append_assoc] at installed
  obtain ⟨ops,operands,valid,returns⟩ := static
  have atRet : tb.insts[0]? = some (.rets us) := by rw [instructions]; rfl
  have whole : Spill.Runs c tb 0
      ((spillEntryStoresAt (spillHomesAt vc edges) vc c.succs preds target ++
        spillEntryCopiesAt (spillHomesAt vc edges) vc edges c.succs preds target) ++
        spillInstAt (spillHomesAt vc edges) 0 (.rets us)) e
      (fun k a => k = tb.insts.size ∧ GoodAt vc edges (availInst (.rets us) wanted) a) := by
    refine Spill.Runs.append entry fun k mid ⟨same,good⟩ => ?_
    subst k
    refine (spillInstAt_runs slots saved targetBlock atRet operands valid returns (fun _ => rfl)
      (classes ops operands) (uses ops operands) good).mono ?_
    intro k final ⟨same,good,_⟩
    exact ⟨same.trans (by rw [instructions]; rfl),good⟩
  obtain ⟨final,run,good⟩ := whole.run
  refine ⟨final,?_,good,bodyStateAt_le good⟩
  unfold CheckCtx.runBlock
  rw [code,targetBlock,installed]
  simpa only [List.toList_toArray,List.append_assoc] using run

end Backend.Proof.PerEdgeSpill
