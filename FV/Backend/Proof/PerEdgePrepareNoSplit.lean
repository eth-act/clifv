import FV.Backend.Proof.PerEdgePrepareFilterFacts
import FV.Backend.Proof.FilteredGraphIncoming

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem inner_no_new_edges (preds : Array (Array Nat)) :
    ∀ (xs : List ((Nat × Label) × Nat)) (st : InnerState),
      (∀ x ∈ xs,(preds[x.1.1]!).size ≤ 1) →
      let out := xs.foldl (innerStepAt preds) st
      out.1 = st.1 ∧ out.2.1 = st.2.1 ∧ out.2.2.1 = st.2.2.1 ∧ out.2.2.2.1 = st.2.2.2.1 := by
  intro xs
  induction xs with
  | nil => intro st low; exact ⟨rfl,rfl,rfl,rfl⟩
  | cons x xs ih =>
    intro st low
    have notShared : ¬(preds[x.1.1]!).size > 1 := by have := low x List.mem_cons_self; omega
    change _
    simp only [List.foldl_cons,innerStepAt,if_neg notShared]
    exact ih _ (fun x member => low x (List.mem_cons_of_mem _ member))
private theorem outer_no_new_edges {V : Array VBlock} {ss ps : Array (Array Nat)} {rows : Array EdgeRow}
    (cfg : Prep.CfgSpec V ss) (noCritical : NoCriticalEdges ss ps)
    {b : Nat} {vb : VBlock} {st out : OuterState} (block : V[b]? = some vb)
    (run : outerStepAt ss ps rows (vb,b) st = .ok (.yield out)) :
    out.1 = st.1 ∧ out.2.2.2.1 = st.2.2.2.1 ∧ out.2.2.2.2 = st.2.2.2.2 := by
  obtain ⟨T,successors,last,term,atRow,count,targets⟩ := cfg.blk b vb block
  have row : ss[b]! = successors := by rw [getElem!_def,atRow]
  unfold outerStepAt at run
  dsimp only at run
  split at run
  · cases run
    exact ⟨rfl,rfl,rfl⟩
  · rename_i multi
    have multiple : 2 ≤ successors.size := by rw [row] at multi; omega
    have low : ∀ x ∈ ((ss[b]!.zip T.targets.toArray).zipIdx).toList,(ps[x.1.1]!).size ≤ 1 := by
      intro x member
      have selected := Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp member)
      have original : ss[b]![x.2]? = some x.1.1 := (Array.getElem?_zip_eq_some.mp selected).1
      rw [row] at original
      exact noCritical b successors atRow multiple x.2 x.1.1 original
    rw [last] at run
    dsimp only at run
    let inner := ((ss[b]!.zip T.targets.toArray).zipIdx).toList.foldl (innerStepAt ps)
      (st.1,st.2.2.2.1,st.2.2.2.2,rows[b]!,#[])
    have facts := inner_no_new_edges ps _ (st.1,st.2.2.2.1,st.2.2.2.2,rows[b]!,#[]) low
    split at run
    · simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at run
      subst out
      exact ⟨facts.1,facts.2.1,facts.2.2.1⟩
    · simp [throw,throwThe,MonadExceptOf.throw] at run

private theorem outer_not_done (ss ps : Array (Array Nat)) (rows : Array EdgeRow)
    (x : VBlock × Nat) (st out : OuterState) : outerStepAt ss ps rows x st ≠ .ok (.done out) := by
  unfold outerStepAt
  dsimp only
  split
  · simp [pure,Except.pure]
  · split
    · split <;> simp [pure,Except.pure,throw,throwThe,MonadExceptOf.throw]
    · simp [throw,throwThe,MonadExceptOf.throw]

/-- The actual indexed outer loop adds no synthetic blocks/rows or fresh
labels when its computed input graph has no critical edges. Outgoing vectors
and source program conditions are unrestricted. -/
theorem outerLoopAt_no_new_edges {V : Array VBlock} {ss ps : Array (Array Nat)} {rows : Array EdgeRow}
    (cfg : Prep.CfgSpec V ss) (noCritical : NoCriticalEdges ss ps) {initial out : OuterState}
    (run : forIn V.zipIdx initial (outerStepAt ss ps rows) = .ok out) :
    out.1 = initial.1 ∧ out.2.2.2.1 = initial.2.2.2.1 ∧ out.2.2.2.2 = initial.2.2.2.2 := by
  rw [← Array.forIn_toList] at run
  apply Prep.forIn_inv _ V.zipIdx.toList
    (fun _ st => st.1 = initial.1 ∧ st.2.2.2.1 = initial.2.2.2.1 ∧ st.2.2.2.2 = initial.2.2.2.2) ?_
    (outer_not_done ss ps rows) _ _ ⟨rfl,rfl,rfl⟩ run
  intro k x st st' atX before step
  have block := Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp (List.mem_of_getElem? atX))
  have facts := outer_no_new_edges cfg noCritical block step
  exact ⟨facts.1.trans before.1,facts.2.1.trans before.2.1,facts.2.2.trans before.2.2⟩

/-- Successful actual prepareAt creates no additional synthetic block/row
when the original graph is critical-edge free. Filtering preserves that graph
property; the actual outer execution proves emptiness before final RPO. -/
theorem prepareAt_no_new_edges {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (labels : Prep.Lbls vc.blocks)
    {ss0 ps0 : Array (Array Nat)} (cfg0 : vc.cfg = .ok (ss0,ps0)) (noCritical : NoCriticalEdges ss0 ps0) :
    ∃ (ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
      ({vc with blocks := Prep.keep vc.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1) ∧
      forIn ((keptAt vc edges ss0).map Prod.fst).zipIdx
        (Prep.next0Of ((keptAt vc edges ss0).map Prod.fst),#[],#[],#[],#[])
        (outerStepAt ss1 ps1 ((keptAt vc edges ss0).map Prod.snd)) = .ok st ∧
      st.2.2.2.1 = #[] ∧ st.2.2.2.2 = #[] ∧ st.1 = Prep.next0Of (Prep.keep vc.blocks (reachable ss0)) ∧
      ({vc with blocks := st.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
      p = ⟨{vc with blocks := (rpo ss2).map fun i => st.2.1[i]!},(rpo ss2).map fun i => st.2.2.1[i]!⟩ := by
  obtain ⟨count,_⟩ := prepareAt_input_facts run
  obtain ⟨ssA,psA,ss1,ps1,ss2,ps2,st,cfgA,cfg1,loop,cfg2,result⟩ := prepareAt_stages run
  rw [cfg0] at cfgA
  cases cfgA
  have keptBlocks := keptAt_blocks (ss := ss0) count
  rw [keptBlocks] at cfg1
  have keptCritical := keep_no_critical cfg0 cfg1 labels noCritical
  have facts := outerLoopAt_no_new_edges (by rw [keptBlocks]; exact Prep.cfg_spec cfg1) keptCritical loop
  have empty : st.2.2.2.1 = #[] := facts.2.1
  have emptyRows : st.2.2.2.2 = #[] := facts.2.2
  rw [empty,Array.append_empty] at cfg2
  rw [empty,emptyRows,Array.append_empty,Array.append_empty] at result
  exact ⟨ss1,ps1,ss2,ps2,st,cfg1,loop,empty,emptyRows,by rw [facts.1,keptBlocks],cfg2,result⟩

end Backend.Proof.PerEdgePrep
