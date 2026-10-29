module

public import FV.Backend.Proof.PerEdgePrepareFilterFacts

@[expose] public section

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof

private theorem cfgSpec_fields {V W : Array VBlock} {ss : Array (Array Nat)}
    (size : W.size = V.size) (labels : W.map VBlock.label = V.map VBlock.label)
    (insts : W.map VBlock.insts = V.map VBlock.insts) (cfg : Prep.CfgSpec V ss) :
    Prep.CfgSpec W ss := by
  have lab : ∀ l, Prep.lab W l = Prep.lab V l := by
    intro l
    have h := congrArg (fun a : Array Label => a.findIdx? (· == l)) labels
    simpa only [Prep.lab,Array.findIdx?_map,Function.comp_def] using h
  refine ⟨by rw [cfg.size, size], ?_⟩
  intro k b hb
  have hk := (Array.getElem?_eq_some_iff.mp hb).1
  have hv : k < V.size := by rw [← size]; exact hk
  obtain ⟨t,ts,back,term,succs,count,targets⟩ := cfg.blk k V[k] (Array.getElem?_eq_getElem hv)
  have same : b.insts = V[k].insts := by
    have h := congrArg (fun a : Array (Array MInst) => a[k]?) insts
    simp only [Array.getElem?_map,hb,Array.getElem?_eq_getElem hv,Option.map_some,
      Option.some.injEq] at h
    exact h
  exact ⟨t,ts,by rw [same]; exact back,term,succs,count,
    fun j l hl => by
      obtain ⟨s,hs,hlab⟩ := targets j l hl
      exact ⟨s,hs,by rw [lab]; exact hlab⟩⟩

private theorem shadow_labels (B E : Array VBlock) :
    (B ++ E.map graphBlock).map VBlock.label = (B ++ E).map VBlock.label := by
  simp [Array.map_append,Array.map_map,graphBlock,Function.comp_def]

private theorem shadow_cfg {B E : Array VBlock} {ss : Array (Array Nat)}
    (cfg : Prep.CfgSpec (B ++ E) ss) : Prep.CfgSpec (B ++ E.map graphBlock) ss :=
  cfgSpec_fields (by simp) (shadow_labels B E)
    (by simp [Array.map_append,Array.map_map,graphBlock,Function.comp_def]) cfg

/-- RPO covers every reachable kept block, with distinct executable labels,
entry first and successor closure. Synthetic jump arguments are retained in
the real graph; erasing them is only an intermediate proof projection. -/
theorem outer_order_facts {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss1 ss2 : Array (Array Nat)} {st : OuterState}
    (inv : OuterInv V outgoing (Prep.next0Of V) V.size st)
    (cfg1 : Prep.CfgSpec V ss1) (cfg2 : Prep.CfgSpec (st.2.1 ++ st.2.2.2.1) ss2)
    (labels : Prep.Lbls V) (nonempty : 0 < V.size) :
    Prep.Lbls (st.2.1 ++ st.2.2.2.1) ∧
    (∀ i ∈ (rpo ss2).toList, i < (st.2.1 ++ st.2.2.2.1).size) ∧
    (rpo ss2).toList.Nodup ∧ (rpo ss2)[0]? = some 0 ∧
    (∀ i ∈ (rpo ss2).toList, ∀ s ∈ (ss2[i]! : Array Nat).toList, s ∈ (rpo ss2).toList) ∧
    (∀ b, Prep.Reach ss2 b → b ∈ (rpo ss2).toList) ∧
    (∀ k, Prep.Reach ss1 k → k < V.size ∧ k ∈ (rpo ss2).toList) := by
  have shadow : Prep.CfgSpec (st.2.1 ++ st.2.2.2.1.map graphBlock) ss2 := shadow_cfg cfg2
  have shadowLabels := Prep.lbls2 inv.graph labels
  have executableLabels : Prep.Lbls (st.2.1 ++ st.2.2.2.1) := by
    unfold Prep.Lbls at shadowLabels ⊢
    have h := congrArg Array.toList (shadow_labels st.2.1 st.2.2.2.1)
    simp only [Array.toList_map] at h
    rw [h] at shadowLabels
    exact shadowLabels
  have nonzero : ss2.size ≠ 0 := by
    have keptCount : st.2.1.size = V.size := inv.graph.size
    rw [cfg2.size,Array.size_append,keptCount]
    omega
  obtain ⟨bounds,nodup,entry,closed,complete⟩ := Prep.rpo_spec (Prep.succsIn_of cfg2) nonzero
  refine ⟨executableLabels,fun i hi => cfg2.size ▸ bounds i hi,nodup,entry,closed,complete,?_⟩
  intro k hk
  obtain ⟨bound,reach⟩ := Prep.reach12 inv.graph cfg1 shadow labels nonempty hk
  exact ⟨bound,complete k reach⟩

/-- The actual final reorder has a CFG and distinct labels. This uses the real
argument-carrying synthetic blocks, without a second executable preparation. -/
theorem ordered_cfg {vc : VCode} {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss1 ss2 : Array (Array Nat)} {st : OuterState}
    (inv : OuterInv V outgoing (Prep.next0Of V) V.size st)
    (cfg1 : Prep.CfgSpec V ss1) (cfg2 : Prep.CfgSpec (st.2.1 ++ st.2.2.2.1) ss2)
    (labels : Prep.Lbls V) (nonempty : 0 < V.size) :
    Prep.Lbls ((rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!) ∧
    ∃ ss3 ps3, ({vc with blocks := (rpo ss2).map fun i =>
      (st.2.1 ++ st.2.2.2.1)[i]!} : VCode).cfg = .ok (ss3,ps3) := by
  obtain ⟨lbls,bounds,nodup,_,closed,_⟩ := outer_order_facts inv cfg1 cfg2 labels nonempty
  refine ⟨Prep.lbls3 bounds lbls nodup,?_⟩
  apply Prep.cfg_of
  intro q b hq
  have hqR : q < (rpo ss2).size := by
    have := (Array.getElem?_eq_some_iff.mp hq).1
    simpa using this
  obtain ⟨hi,lookup⟩ := Prep.v3_get bounds hqR
  rw [lookup] at hq
  cases hq
  obtain ⟨t,ts,back,term,_,_,targets⟩ := cfg2.blk _ _ (Array.getElem?_eq_getElem hi)
  refine ⟨t,back,term,?_⟩
  intro l hl
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hl
  have target := List.getElem?_eq_getElem hj
  obtain ⟨s,_,find⟩ := targets j _ target
  have inOrder := closed _ (by simp) s (Prep.succ_mem cfg2 hi back target find)
  obtain ⟨q',_,_,atLabel⟩ := Prep.lab3 bounds lbls nodup inOrder
  obtain ⟨hs,sourceLabel⟩ := Prep.lab_some find
  rw [getElem!_pos _ s hs,sourceLabel] at atLabel
  exact ⟨q',atLabel⟩

/-- Every successful actual indexed preparation of nonempty distinctly labelled
VCode has a CFG after its real RPO reorder, and still has distinct labels. No
legacy single-vector or empty-branch-argument restriction is needed. -/
theorem prepareAt_cfg {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) :
    Prep.Lbls p.code.blocks ∧ ∃ ss ps : Array (Array Nat), p.code.cfg = .ok (ss,ps) := by
  obtain ⟨_,ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,_,cfg1,inv,cfg2,result⟩ := prepareAt_kept_facts run
  have cs0 := Prep.cfg_spec cfg0
  have nonzero : ss0.size ≠ 0 := by rw [cs0.size]; omega
  have entry := (Prep.reachable_spec (Prep.succsIn_of cs0) nonzero).2.1
  obtain ⟨keptNonempty,_⟩ := Prep.keep_zero nonempty entry
  have keptLabels := Prep.keep_lbls labels (reachable ss0)
  have facts := ordered_cfg (vc := vc) inv (Prep.cfg_spec cfg1) (Prep.cfg_spec cfg2)
    keptLabels keptNonempty
  cases result
  exact facts

/-- The original entry is the actual prepared entry after filtering, splitting
and RPO. This supplies the entry clause of the indexed preparation relation. -/
theorem prepareAt_entry {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) : Driver.sigmaOf vc p.code 0 = some 0 := by
  obtain ⟨_,ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,_,cfg1,inv,cfg2,result⟩ := prepareAt_kept_facts run
  have cs0 := Prep.cfg_spec cfg0
  have nonzero : ss0.size ≠ 0 := by rw [cs0.size]; omega
  have entry := (Prep.reachable_spec (Prep.succsIn_of cs0) nonzero).2.1
  obtain ⟨keptNonempty,keptEntry⟩ := Prep.keep_zero nonempty entry
  obtain ⟨_,bounds,_,first,_,_⟩ := outer_order_facts inv (Prep.cfg_spec cfg1) (Prep.cfg_spec cfg2)
    (Prep.keep_lbls labels (reachable ss0)) keptNonempty
  have rpoNonempty := (Array.getElem?_eq_some_iff.mp first).1
  have orderZero : (rpo ss2)[0] = 0 := (Array.getElem?_eq_some_iff.mp first).2
  have blockNonempty : 0 < st.2.1.size := by rw [inv.graph.size]; exact keptNonempty
  have allNonempty : 0 < (st.2.1 ++ st.2.2.2.1).size := by simp; omega
  have blockLabel : st.2.1[0].label = vc.blocks[0].label := by
    rw [(Prep.rw_fields (inv.graph.rw 0 keptNonempty blockNonempty)).1,keptEntry]
  cases result
  unfold Driver.sigmaOf
  rw [Array.getElem?_eq_getElem nonempty]
  change Prep.lab _ _ = some 0
  apply Prep.lab_zero (by simpa using rpoNonempty)
  simp only [Array.getElem_map]
  rw [orderZero,getElem!_pos _ 0 allNonempty,Array.getElem_append_left blockNonempty]
  exact blockLabel

end Backend.Proof.PerEdgePrep
