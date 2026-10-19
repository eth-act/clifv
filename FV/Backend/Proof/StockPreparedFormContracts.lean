import FV.Backend.Proof.StockWholeFormContracts
import FV.Backend.Proof.StockPrepareComplete

namespace Backend.Stock.Proof.Coverage.PreparedFormsDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.Coverage.WholeFormsDraft
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

/-- Actual indexed preparation preserves the complete Stock producer's forms
and ordinary spill-static facts through filtering, retargeting, splitting and
RPO. Original source scope supplies all graph-domain premises internally. -/
theorem stock_prepared_form_coverage {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {prepared : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok prepared) :
    ∀ block ∈ prepared.code.blocks.toList,∀ i ∈ block.insts.toList,
      Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  intro block member i inside
  rcases inst_origin raw nonempty labels member inside with
    ⟨original,present,retained⟩ | ⟨original,present,old,retained,targets,retargeted⟩ | ⟨label,rfl⟩
  · exact stock_lower_form_coverage run scope original present i retained
  · have control := setTargets_isCtl retargeted
    refine ⟨?_,?_⟩
    · simp only [Covered,control,Bool.true_or]
    · intro ordinary
      rw [control] at ordinary
      cases ordinary
  · exact ⟨rfl,fun ordinary => by cases ordinary⟩

/-- The real prepared per-successor Stock output supplies the existing
FormsCovered consumer interface without a caller instruction certificate. -/
theorem stock_prepared_formsCovered {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {prepared : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok prepared) (ctx : FnCtx) :
    FormsCovered ctx prepared.code := by
  intro b block k i placed emitted
  have form := (stock_prepared_form_coverage run scope raw block
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? placed)) i
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? emitted))).1
  have irrelevant : FormOk ctx i = FormOk default i := by unfold FormOk; rfl
  rw [irrelevant]
  exact (Bool.or_eq_true _ _).mp form

end Backend.Stock.Proof.Coverage.PreparedFormsDraft
