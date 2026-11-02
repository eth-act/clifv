import FV.Backend.Proof.PerEdgePrepareComplete
import FV.Backend.Proof.PerEdgePrepareTotal
import FV.Backend.Proof.SpillEdgesPrep

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof

/-- Reachability filtering preserves a valid nonempty distinctly-labelled CFG.
No predecessor or outgoing-copy assumptions are needed for this stage. -/
theorem kept_cfg {vc : VCode} {ss ps : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks) :
    ∃ ss' ps',({vc with blocks := Prep.keep vc.blocks (reachable ss)} : VCode).cfg = .ok (ss',ps') := by
  have cs := Prep.cfg_spec cfg
  have nonzero : ss.size ≠ 0 := by rw [cs.size]; omega
  have closed := (Prep.reachable_spec (Prep.succsIn_of cs) nonzero).2.2.1
  apply Prep.cfg_of
  intro k b atBlock
  obtain ⟨hk,same⟩ := Array.getElem?_eq_some_iff.mp atBlock
  obtain ⟨original,hb,source,live⟩ := Prep.keep_src hk
  obtain ⟨t,ts,back,term,_,_,targets⟩ := cs.blk original vc.blocks[original]
    (Array.getElem?_eq_getElem hb)
  have blockEq : b = vc.blocks[original] := same.symm.trans source
  refine ⟨t,by rw [blockEq]; exact back,term,?_⟩
  intro l hl
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hl
  have target := List.getElem?_eq_getElem hj
  obtain ⟨s,_,find⟩ := targets j _ target
  obtain ⟨hs,atLabel⟩ := Prep.lab_some find
  have liveS := closed original live s (Prep.succ_mem cs hb back target find)
  obtain ⟨k',hk',kept⟩ := Prep.keep_dst hs liveS
  exact ⟨k',Prep.lab_of (Prep.keep_lbls labels _) hk' (by rw [kept,atLabel])⟩

/-- Filtering retains the original parameterless entry, and cannot introduce
an entry predecessor when no original instruction targets the entry label. -/
theorem kept_entry {vc : VCode} {ss ps ss' ps' : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) (nonempty : 0 < vc.blocks.size)
    (cfg' : ({vc with blocks := Prep.keep vc.blocks (reachable ss)} : VCode).cfg = .ok (ss',ps'))
    (params : vc.blocks[0].params = #[])
    (noEntry : ∀ b ∈ vc.blocks.toList,∀ t,b.insts.back? = some t → vc.blocks[0].label ∉ t.targets) :
    (ps'[0]?.getD #[]).isEmpty = true ∧
      (((Prep.keep vc.blocks (reachable ss))[0]?.map (fun b => b.params.isEmpty)).getD true) = true := by
  have cs := Prep.cfg_spec cfg
  have cs' := Prep.cfg_spec cfg'
  have nonzero : ss.size ≠ 0 := by rw [cs.size]; omega
  obtain ⟨keptNonempty,first⟩ := Prep.keep_zero nonempty
    (Prep.reachable_spec (Prep.succsIn_of cs) nonzero).2.1
  have noIncoming : ∀ (q : Nat) (sq : Array Nat) (j : Nat),ss'[q]? = some sq → sq[j]? = some 0 → False := by
    intro q sq j atQ edge
    have hq : q < (Prep.keep vc.blocks (reachable ss)).size := by
      have h := (Array.getElem?_eq_some_iff.mp atQ).1
      rw [cs'.size] at h
      exact h
    obtain ⟨t,ts,back,_,row,count,targets⟩ := cs'.blk q _ (Array.getElem?_eq_getElem hq)
    rw [atQ] at row
    cases row
    have hj := (Array.getElem?_eq_some_iff.mp edge).1
    obtain ⟨l,hl⟩ : ∃ l,t.targets[j]? = some l :=
      ⟨_,List.getElem?_eq_getElem (by rw [← count]; exact hj)⟩
    obtain ⟨s,atS,find⟩ := targets j l hl
    rw [edge] at atS
    cases atS
    obtain ⟨_,label⟩ := Prep.lab_some find
    rw [first] at label
    obtain ⟨b,hb,source,_⟩ := Prep.keep_src hq
    rw [source] at back
    exact noEntry vc.blocks[b] (Array.getElem_mem_toList hb) t back
      (by rw [label]; exact List.mem_of_getElem? hl)
  have preds := Spill.preds_nil cfg' keptNonempty noIncoming
  refine ⟨by simp [preds],?_⟩
  simp [Array.getElem?_eq_getElem keptNonempty,first,params]

private def rowBody (ss : Array (Array Nat)) (x : EdgeRow × Nat) (_ : PUnit.{1}) :
    Except String (ForInStep PUnit.{1}) := do
  if x.1.size != ss[x.2]!.size then throw s!"block {x.2}: per-successor vector count differs"
  pure (.yield PUnit.unit)

private theorem rowList_total (ss : Array (Array Nat)) :
    ∀ (xs : List (EdgeRow × Nat)),(∀ x ∈ xs,x.1.size = ss[x.2]!.size) →
      forIn xs PUnit.unit (rowBody ss) = .ok PUnit.unit
  | [], valid => rfl
  | x :: xs, valid => by
    have head := valid x (by simp)
    have tail := rowList_total ss xs (fun x hx => valid x (List.mem_cons_of_mem _ hx))
    rw [List.forIn_cons]
    simp only [rowBody,head,bne_self_eq_false,Bool.false_eq_true,ite_false,pure,Except.pure,
      bind,Except.bind]
    exact tail

private theorem rows_total {ss : Array (Array Nat)} {edges : Array EdgeRow}
    (valid : ∀ (b : Nat) (row : EdgeRow),edges[b]? = some row → row.size = ss[b]!.size) :
    forIn edges.zipIdx PUnit.unit (rowBody ss) = .ok PUnit.unit := by
  rw [← Array.forIn_toList]
  apply rowList_total
  intro x member
  exact valid x.2 x.1 (Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp member))

/-- Raw indexed preparation is total on its original graph and copy dimensions.
These are internal producer obligations to derive for Stock's original source
scope, not additional source-program certificates or runtime acceptance filters. -/
theorem prepareAt_total {vc : VCode} {edges : Array EdgeRow} {ss ps : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    (count : edges.size = vc.blocks.size)
    (arity : ∀ (b : Nat) (row : EdgeRow),edges[b]? = some row → row.size = ss[b]!.size)
    (params : vc.blocks[0].params = #[])
    (noEntry : ∀ b ∈ vc.blocks.toList,∀ t,b.insts.back? = some t → vc.blocks[0].label ∉ t.targets) :
    ∃ prepared,prepareAt vc edges = .ok prepared := by
  obtain ⟨ss1,ps1,cfg1⟩ := kept_cfg cfg nonempty labels
  obtain ⟨preds,entry⟩ := kept_entry cfg nonempty cfg1 params noEntry
  have cs1 := Prep.cfg_spec cfg1
  have keptLabels := Prep.keep_lbls labels (reachable ss)
  obtain ⟨st,loop,inv,targets⟩ := outerLoopAt_total_targets
    (outgoing := (keptAt vc edges ss).map Prod.snd) (ps := ps1) cs1
  obtain ⟨ss2,ps2,cfg2⟩ := split_cfg (vc := vc) inv cs1 keptLabels targets
  let prepared : EdgeVCode := ⟨{vc with blocks := (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!},
    (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!⟩
  have checkedRows := rows_total arity
  change forIn edges.zipIdx PUnit.unit (fun x state => rowBody ss x state) = .ok PUnit.unit at checkedRows
  simp only [rowBody,bind,Except.bind] at checkedRows
  refine ⟨prepared,?_⟩
  unfold prepareAt
  rw [cfg]
  simp only [bind,Except.bind]
  simp only [count,bne_self_eq_false,Bool.false_eq_true,ite_false]
  rw [checkedRows]
  rw [← keptAt_blocks (ss := ss) count] at cfg1
  simp only [keptAt] at cfg1
  rw [cfg1]
  simp only [preds,Bool.not_true,Bool.false_eq_true,ite_false]
  rw [← keptAt_blocks (ss := ss) count] at entry
  simp only [keptAt] at entry
  rw [entry]
  simp only [Bool.not_true,Bool.false_eq_true,ite_false]
  rw [← keptAt_blocks (ss := ss) count] at loop
  change forIn ((keptAt vc edges ss).map Prod.fst).zipIdx
    (Prep.next0Of ((keptAt vc edges ss).map Prod.fst),#[],#[],#[],#[])
    (fun x state => outerStepAt ss1 ps1 ((keptAt vc edges ss).map Prod.snd) x state) = .ok st at loop
  let finish (state : OuterState) : Except String EdgeVCode := do
    let (succs,_) ← ({vc with blocks := state.2.1 ++ state.2.2.2.1} : VCode).cfg
    pure ⟨{vc with blocks := (rpo succs).map fun i => (state.2.1 ++ state.2.2.2.1)[i]!},
      (rpo succs).map fun i => (state.2.2.1 ++ state.2.2.2.2)[i]!⟩
  have done : (forIn ((keptAt vc edges ss).map Prod.fst).zipIdx
      (Prep.next0Of ((keptAt vc edges ss).map Prod.fst),#[],#[],#[],#[])
      (fun x state => outerStepAt ss1 ps1 ((keptAt vc edges ss).map Prod.snd) x state)).bind finish =
      .ok prepared := by
    rw [loop]
    simp only [Except.bind,finish,cfg2,bind,pure,Except.pure]
    rfl
  refine Eq.trans ?_ done
  dsimp only [Except.bind,finish]
  congr 2
  funext x state
  simp only [outerStepAt,innerForInAt_eq,throw,throwThe,MonadExceptOf.throw,keptAt]
  rfl

/-- Once the producer's original graph/copy obligations hold, both raw and
checked indexed preparation succeed and return the proved structural relation. -/
theorem prepareCheckedAt_total {vc : VCode} {edges : Array EdgeRow} {ss ps : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    (count : edges.size = vc.blocks.size)
    (arity : ∀ (b : Nat) (row : EdgeRow),edges[b]? = some row → row.size = ss[b]!.size)
    (params : vc.blocks[0].params = #[])
    (noEntry : ∀ b ∈ vc.blocks.toList,∀ t,b.insts.back? = some t → vc.blocks[0].label ∉ t.targets) :
    ∃ prepared,prepareAt vc edges = .ok prepared ∧ prepareCheckedAt vc edges = .ok prepared ∧
      prepCheckAt vc edges prepared = true := by
  obtain ⟨prepared,run⟩ := prepareAt_total cfg nonempty labels count arity params noEntry
  exact ⟨prepared,run,prepareCheckedAt_complete run nonempty labels,
    prepCheckAt_complete run nonempty labels⟩

end Backend.Proof.PerEdgePrep
