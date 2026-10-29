module

public import FV.Backend.Proof.PerEdgePrepareOuterFacts
public import FV.Backend.Proof.PerEdgePrepareFilterFacts
public import FV.Backend.Proof.PerEdgePrepareOrderFacts
public import FV.Backend.Proof.PerEdgePrepareLoopWitness

@[expose] public section

namespace Backend.Proof.PerEdgePrepOuterWitness
open Backend Backend.Proof.PerEdgePrep

private def blocks : Array VBlock := #[
  {label := 10,insts := #[.condBr 20 30 (.notZero (.vreg 192 .int) .size64)]},
  {label := 20,insts := #[.jump 30],params := #[.vreg 193 .int]},
  {label := 30,insts := #[.rets [(.vreg 195 .int,.x 0)]],params := #[.vreg 195 .int]}]
private def edges : Array EdgeRow := #[
  #[#[.vreg 192 .int],#[.vreg 194 .int]],#[#[.vreg 193 .int]],#[]]
private def code : VCode := {
  name := "indexed_outer_split",classes := Array.replicate 196 .int,
  slotBytes := 0,outgoing := 0,rulesFired := #[],blocks := blocks}
private def successors : Array (Array Nat) := #[#[1,2],#[2],#[]]
private def predecessors : Array (Array Nat) := #[#[],#[0],#[0,1]]
private def initial : OuterState := (31,#[],#[],#[],#[])
private def first : OuterState := (32,
  #[{label := 10,insts := #[.condBr 20 31 (.notZero (.vreg 192 .int) .size64)]}],
  #[#[#[.vreg 192 .int],#[]]],
  #[{label := 31,insts := #[.jump 30],branchArgs := #[.vreg 194 .int]}],
  #[#[#[.vreg 194 .int]]])
private def finalState : OuterState := (32,
  #[{label := 10,insts := #[.condBr 20 31 (.notZero (.vreg 192 .int) .size64)]},
    blocks[1]!,blocks[2]!],
  #[#[#[.vreg 192 .int],#[]],#[#[.vreg 193 .int]],#[]],
  #[{label := 31,insts := #[.jump 30],branchArgs := #[.vreg 194 .int]}],
  #[#[#[.vreg 194 .int]]])

private theorem cfg : Prep.CfgSpec blocks successors := by
  apply Prep.cfg_spec (vc := code) (ps := predecessors)
  have observed : code.cfg.toOption = some (successors,predecessors) := by decide +kernel
  cases run : code.cfg with
  | error err => simp [run,Except.toOption] at observed
  | ok pair =>
    rw [run] at observed
    simp only [Except.toOption,Option.some.injEq] at observed
    exact congrArg Except.ok observed

private theorem initial_inv : OuterInv blocks edges 31 0 initial := by
  refine ⟨⟨by simp [initial],?_,rfl,?_⟩,rfl,?_,?_⟩
  · intro e he
    simp [initial] at he
  · intro j _ hj
    simp [initial] at hj
  · exact ⟨rfl,fun e _ he => by simp [initial] at he⟩
  · intro j _ hj
    simp [initial] at hj

private theorem first_run : outerStepAt successors predecessors edges (blocks[0]!,0)
    initial = .ok (.yield first) := by
  simp [outerStepAt,initial,first,successors,predecessors,blocks,edges,innerStepAt,
    MInst.targets,MInst.setTargets]

private theorem whole_run : forIn blocks.zipIdx (Prep.next0Of blocks,#[],#[],#[],#[])
    (outerStepAt successors predecessors edges) = .ok finalState := by
  rw [← Array.forIn_toList]
  simp [blocks,Prep.next0Of,outerStepAt,successors,predecessors,edges,finalState,
    innerStepAt,MInst.targets,MInst.setTargets,List.forIn_cons,bind,Except.bind]

/-- A real critical edge is split in the first block, and its selected copy
route survives both later blocks. All three outer-invariant roots are inhabited
by actual executions rather than assumed invariant certificates. -/
theorem indexed_outer_loop_witness :
    OuterInv blocks edges 31 1 first ∧
    OuterInv blocks edges (Prep.next0Of blocks) blocks.size finalState ∧
    BlockCopies finalState.2.2.2.1 finalState.2.2.2.2 blocks[0]! finalState.2.1[0]!
      edges[0]! finalState.2.2.1[0]! ∧
    finalState.2.2.2.1[0]!.branchArgs = #[.vreg 194 .int] ∧
    finalState.2.2.2.2[0]? = some #[#[.vreg 194 .int]] := by
  have one := outerStepAt_inv cfg (k := 0) (vb := blocks[0]!) rfl initial_inv first_run
  have all := outerLoopAt_inv cfg whole_run
  exact ⟨one,all,all.copies 0 (by decide +kernel) (by decide +kernel),rfl,rfl⟩

/-- Actual unreachable-block filtering and RPO also supply the full outer
graph/copy invariant before the final reorder, with no added source premise. -/
theorem indexed_prepare_outer_facts_witness :
    ∃ (vc : VCode) (edges : Array EdgeRow) (p : EdgeVCode),
      prepareAt vc edges = .ok p ∧ vc.blocks.size = 5 ∧
      p.code.blocks.map (·.label) = #[10,31,20,30] ∧
      ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
        vc.cfg = .ok (ss0,ps0) ∧
        ({vc with blocks := (keptAt vc edges ss0).map Prod.fst} : VCode).cfg = .ok (ss1,ps1) ∧
        OuterInv ((keptAt vc edges ss0).map Prod.fst) ((keptAt vc edges ss0).map Prod.snd)
          (Prep.next0Of ((keptAt vc edges ss0).map Prod.fst))
          ((keptAt vc edges ss0).map Prod.fst).size st ∧
        ({vc with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
        p = ⟨{vc with blocks := (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!},
          (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!⟩ := by
  obtain ⟨vc,rows,p,run,size,labels,_⟩ := PerEdgePrepLoopWitness.indexed_prepare_stages_witness
  exact ⟨vc,rows,p,run,size,labels,prepareAt_outer_facts run⟩

/-- The real five-block fixture inhabits the input-dimension checks and keeps
each live block paired with its original row, while retaining the full outer
copy invariant and actual final reorder. -/
theorem indexed_prepare_filter_facts_witness :
    ∃ (vc : VCode) (edges : Array EdgeRow) (p : EdgeVCode),
      prepareAt vc edges = .ok p ∧ vc.blocks.size = 5 ∧ edges.size = vc.blocks.size ∧
      p.code.blocks.map (·.label) = #[10,31,20,30] ∧
      ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
        vc.cfg = .ok (ss0,ps0) ∧
        (∀ (b : Nat) (row : EdgeRow), edges[b]? = some row → row.size = ss0[b]!.size) ∧
        (keptAt vc edges ss0).map Prod.fst = Prep.keep vc.blocks (reachable ss0) ∧
        (∀ (k : Nat) (hk : k < (keptAt vc edges ss0).size), ∃ b : Nat,
          vc.blocks[b]? = some (keptAt vc edges ss0)[k].1 ∧
          edges[b]? = some (keptAt vc edges ss0)[k].2 ∧ Prep.mk (reachable ss0) b) ∧
        ({vc with blocks := Prep.keep vc.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1) ∧
        OuterInv (Prep.keep vc.blocks (reachable ss0)) ((keptAt vc edges ss0).map Prod.snd)
          (Prep.next0Of (Prep.keep vc.blocks (reachable ss0)))
          (Prep.keep vc.blocks (reachable ss0)).size st ∧
        ({vc with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
        p = ⟨{vc with blocks := (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!},
          (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!⟩ := by
  obtain ⟨vc,rows,p,run,size,labels,_⟩ := PerEdgePrepLoopWitness.indexed_prepare_stages_witness
  obtain ⟨count,ss0,ps0,ss1,ps1,ss2,ps2,st,cfg,dimensions,cfg1,inv,cfg2,result⟩ :=
    prepareAt_kept_facts run
  exact ⟨vc,rows,p,run,size,count,labels,ss0,ps0,ss1,ps1,ss2,ps2,st,cfg,dimensions,
    keptAt_blocks count,fun _ hk => keptAt_source hk,cfg1,inv,cfg2,result⟩

private def splitSuccs : Array (Array Nat) := #[#[1,3],#[2],#[],#[2]]
private def splitPreds : Array (Array Nat) := #[#[],#[0],#[1,3],#[0]]
private def splitCode : VCode := {code with blocks := finalState.2.1 ++ finalState.2.2.2.1}

private theorem splitCfg : Prep.CfgSpec (finalState.2.1 ++ finalState.2.2.2.1) splitSuccs := by
  apply Prep.cfg_spec (vc := splitCode) (ps := splitPreds)
  have observed : splitCode.cfg.toOption = some (splitSuccs,splitPreds) := by decide +kernel
  cases run : splitCode.cfg with
  | error err => simp [run,Except.toOption] at observed
  | ok pair =>
    rw [run] at observed
    simp only [Except.toOption,Option.some.injEq] at observed
    exact congrArg Except.ok observed

/-- RPO really moves the new critical-edge block ahead of another original
block, covers the reachable graph, and supplies a CFG of the real blocks with
their nonempty synthetic jump arguments. -/
theorem indexed_rpo_witness :
    rpo splitSuccs = #[0,3,1,2] ∧
    Prep.Lbls (finalState.2.1 ++ finalState.2.2.2.1) ∧
    (∀ i ∈ (rpo splitSuccs).toList, i < (finalState.2.1 ++ finalState.2.2.2.1).size) ∧
    (rpo splitSuccs).toList.Nodup ∧ (rpo splitSuccs)[0]? = some 0 ∧
    (∀ i ∈ (rpo splitSuccs).toList, ∀ s ∈ (splitSuccs[i]! : Array Nat).toList,
      s ∈ (rpo splitSuccs).toList) ∧
    (∀ b, Prep.Reach splitSuccs b → b ∈ (rpo splitSuccs).toList) ∧
    (∀ k, Prep.Reach successors k → k < blocks.size ∧ k ∈ (rpo splitSuccs).toList) ∧
    Prep.Lbls ((rpo splitSuccs).map fun i => (finalState.2.1 ++ finalState.2.2.2.1)[i]!) ∧
    ∃ ss ps, ({code with blocks := (rpo splitSuccs).map fun i =>
      (finalState.2.1 ++ finalState.2.2.2.1)[i]!} : VCode).cfg = .ok (ss,ps) := by
  have inv := outerLoopAt_inv cfg whole_run
  have labels : Prep.Lbls blocks := by unfold Prep.Lbls; decide +kernel
  have nonempty : 0 < blocks.size := by decide +kernel
  have facts := outer_order_facts inv cfg splitCfg labels nonempty
  have finalCfg := ordered_cfg (vc := code) inv cfg splitCfg labels nonempty
  exact ⟨by decide +kernel,facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,
    facts.2.2.2.2.1,facts.2.2.2.2.2.1,facts.2.2.2.2.2.2,finalCfg⟩

/-- A complete actual preparation with filtering and a new critical edge has
the original entry at prepared entry zero, distinct labels and a final CFG. -/
theorem indexed_prepared_entry_cfg_witness :
    ∃ (vc : VCode) (edges : Array EdgeRow) (p : EdgeVCode),
      prepareAt vc edges = .ok p ∧ vc.blocks.size = 5 ∧
      p.code.blocks.map (·.label) = #[10,31,20,30] ∧
      Driver.sigmaOf vc p.code 0 = some 0 ∧ Prep.Lbls p.code.blocks ∧
      ∃ ss ps : Array (Array Nat), p.code.cfg = .ok (ss,ps) := by
  obtain ⟨p,run,labels,_⟩ := PerEdgePrepareWitness.per_edge_prepare_split_copy_witness (fun _ => 0)
  have finalCfg := prepareAt_cfg run (by decide +kernel) (by unfold Prep.Lbls; decide +kernel)
  have entry := prepareAt_entry run (by decide +kernel) (by unfold Prep.Lbls; decide +kernel)
  exact ⟨_,_,p,run,rfl,labels,entry,finalCfg⟩

end Backend.Proof.PerEdgePrepOuterWitness
