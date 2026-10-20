import FV.Backend.Proof.StockPreparedIncoming
import FV.Backend.Proof.StockPreparedJump

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- Every actual prepared predecessor of a shared target ends in the exact
jump to that target's real label. Actual preparation/RPO/incoming origins,
source-kind classification and emitted jump correctness are derived under
original scope. No extra input filter or caller jump certificate is needed. -/
theorem stock_prepare_shared_jump_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {p : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok p)
    {ss ps : Array (Array Nat)} (cfg : p.code.cfg = .ok (ss,ps))
    {b j target : Nat} {row : Array Nat} (atRow : ss[b]? = some row) (edge : row[j]? = some target)
    (shared : 1 < ps[target]!.size) :
    ∃ (vb : VBlock),p.code.blocks[b]? = some vb ∧
      vb.insts.back? = some (.jump p.code.blocks[target]!.label) ∧
      ss[b]? = some #[target] ∧ j = 0 := by
  have cs := Prep.cfg_spec cfg
  have bBound : b < p.code.blocks.size := by rw [← cs.size]; exact (Array.getElem?_eq_some_iff.mp atRow).1
  have targetBound := cfg_succ_lt cfg atRow (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  obtain ⟨other,index,otherRow,otherAt,otherEdge,distinct⟩ := cfg_multiple_preds_other cfg atRow edge shared
  have otherBound : other < p.code.blocks.size := by rw [← cs.size]; exact (Array.getElem?_eq_some_iff.mp otherAt).1
  obtain ⟨ss0,ps0,origin,cfg0,provenance,injective,incoming⟩ := stock_prepared_incoming run scope raw cfg
  obtain ⟨oldRow,oldAt,oldEdge,_⟩ := incoming b j target row atRow edge
  obtain ⟨oldOtherRow,oldOtherAt,oldOtherEdge,_⟩ := incoming other index target otherRow otherAt otherEdge
  have oldDistinct : origin b ≠ origin other ∨ j ≠ index := by
    rcases distinct with different | different
    · exact .inl (fun equal => different (injective b other bBound otherBound equal).symm)
    · exact .inr (Ne.symm different)
  obtain ⟨vb0,atOld,oldBack,_,_⟩ := stock_lower_shared_jump_cfg run scope oldAt oldEdge oldOtherAt oldOtherEdge oldDistinct
  obtain ⟨originBound,labelSame,live⟩ := provenance b bBound
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨preparedLabels,_⟩ := prepareAt_cfg raw nonempty labels
  have sigmaHere : sigmaOf result.code p.code (origin b) = some b := by
    unfold sigmaOf
    rw [atOld]
    change Prep.lab p.code.blocks vb0.label = some b
    apply Prep.lab_of preparedLabels bBound
    have actualLabel : result.code.blocks[origin b]!.label = vb0.label := by rw [getElem!_def,atOld]
    rw [actualLabel,getElem!_pos p.code.blocks b bBound] at labelSame
    exact labelSame.symm
  obtain ⟨ss3,ps3,q,vb,label,cfg3,sigma,atNew,back,size,params⟩ :=
    stock_prepare_jump_counterpart run scope raw cfg0 atOld live oldBack
  rw [sigmaHere] at sigma
  cases sigma
  obtain ⟨t,row',back',_,atRow',count,targets⟩ := cs.blk b vb atNew
  rw [back] at back'
  cases back'
  rw [atRow] at atRow'
  cases atRow'
  have one : row.size = 1 := by simpa only [MInst.targets,List.length_singleton] using count
  have zero : j = 0 := by have bound := (Array.getElem?_eq_some_iff.mp edge).1; omega
  subst j
  obtain ⟨destination,atDest,find⟩ := targets 0 label rfl
  rw [edge] at atDest
  cases atDest
  obtain ⟨targetBound',targetLabel⟩ := Prep.lab_some find
  have exactLabel : p.code.blocks[target]!.label = label := by rw [getElem!_pos p.code.blocks target targetBound']; exact targetLabel
  obtain ⟨chosen,single⟩ := Array.size_eq_one_iff.mp one
  have same : chosen = target := by rw [single] at edge; exact Option.some.inj edge
  rw [same] at single
  exact ⟨vb,atNew,by rw [exactLabel]; exact back,by rw [atRow,single],rfl⟩

end Backend.Stock.Proof
