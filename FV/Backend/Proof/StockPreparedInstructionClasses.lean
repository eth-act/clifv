import FV.Backend.Proof.StockWholeInstructionClasses
import FV.Backend.Proof.StockPrepareComplete
import FV.Backend.Proof.PerEdgePrepareFacts
namespace Backend.Stock.Proof.PreparedInstructionClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.WholeInstructionClassDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem inst_origin {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) {vb' : VBlock} (block : vb' ∈ p.code.blocks.toList)
    {i' : MInst} (inst : i' ∈ vb'.insts.toList) :
    (∃ vb ∈ vc.blocks.toList, i' ∈ vb.insts.toList) ∨
      (∃ vb ∈ vc.blocks.toList, ∃ i ∈ vb.insts.toList, ∃ ls, i.setTargets ls = some i') ∨
      ∃ l, i' = .jump l := by
  obtain ⟨_,ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,_,cfg1,inv,cfg2,result⟩ := prepareAt_kept_facts run
  have cs0 := Prep.cfg_spec cfg0
  have nonzero : ss0.size ≠ 0 := by rw [cs0.size]; omega
  obtain ⟨keptNonempty,_⟩ := Prep.keep_zero nonempty
    (Prep.reachable_spec (Prep.succsIn_of cs0) nonzero).2.1
  obtain ⟨_,bounds,_⟩ := outer_order_facts inv (Prep.cfg_spec cfg1) (Prep.cfg_spec cfg2)
    (Prep.keep_lbls labels (reachable ss0)) keptNonempty
  rw [result] at block
  rw [Array.mem_toList_iff,Array.mem_map] at block
  obtain ⟨k,hk,rfl⟩ := block
  have bound : k < (st.2.1 ++ st.2.2.2.1).size := bounds k (by simpa using hk)
  rw [getElem!_pos _ k bound] at inst
  by_cases old : k < st.2.1.size
  · rw [Array.getElem_append_left old] at inst
    have hkV : k < (Prep.keep vc.blocks (reachable ss0)).size := by rw [← inv.graph.size]; exact old
    obtain ⟨b,hb,source,_⟩ := Prep.keep_src hkV
    have member : (Prep.keep vc.blocks (reachable ss0))[k] ∈ vc.blocks.toList := by rw [source]; simp
    rcases inv.graph.rw k hkV old with same | ⟨t,t',ls,back,_,retarget,rewrite,_⟩
    · rw [same] at inst
      exact .inl ⟨_,member,inst⟩
    · rw [rewrite] at inst
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at inst
      rcases inst with inst | rfl
      · exact .inl ⟨_,member,Prep.pop_mem inst⟩
      · exact .inr (.inl ⟨_,member,t,Array.mem_toList_iff.mpr (Array.mem_of_back? back),ls,retarget⟩)
  · rw [Array.getElem_append_right (Nat.le_of_not_lt old)] at inst
    have he : k - st.2.1.size < st.2.2.2.1.size := by simp at bound; omega
    obtain ⟨l,shape⟩ := inv.graph.edges (k - st.2.1.size) (by simpa using he)
    have insts : st.2.2.2.1[k - st.2.1.size].insts = #[.jump l] := by
      have h := congrArg VBlock.insts shape
      simpa only [Array.getElem_map,graphBlock] using h
    rw [insts] at inst
    simp at inst
    exact .inr (.inr ⟨l,inst⟩)

/-- Actual indexed preparation retains every instruction's operand classes,
including terminator retargeting, filtering, splitting and RPO. All producer
and graph-domain facts derive from actual Stock lowering and original scope. -/
theorem stock_prepared_instruction_classes {f : Clif.Function} {result : Result}
    (scope : LowerScope f) (run : Stock.lower f = .ok result) {prepared : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok prepared) :
    ∀ block ∈ prepared.code.blocks.toList,∀ i ∈ block.insts.toList,InstCls prepared.code.classes i := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  have classes := (prepareAt_fields raw).2.1
  intro block member i inside
  rw [classes]
  rcases inst_origin raw nonempty labels member inside with
    ⟨original,present,retained⟩ | ⟨original,present,old,retained,targets,retargeted⟩ | ⟨label,rfl⟩
  · exact stock_lower_instruction_classes scope run original present i retained
  · intro ops operands
    have same := (Driver.setTargets_facts retargeted).1
    exact stock_lower_instruction_classes scope run original present old retained ops (same.symm.trans operands)
  · intro ops operands r member
    cases operands
    simp at member
end Backend.Stock.Proof.PreparedInstructionClassDraft
