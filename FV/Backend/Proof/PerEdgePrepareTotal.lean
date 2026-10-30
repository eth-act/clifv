import FV.Backend.Proof.PerEdgePrepareOuterFacts

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof

private theorem two_labels {ls : List Label} (h : ls.length = 2) :
    ∃ a b,ls = [a,b] := by
  cases ls with
  | nil => simp at h
  | cons a rest =>
    cases rest with
    | nil => simp at h
    | cons b rest =>
      have empty : rest = [] := by simpa using h
      exact ⟨a,b,by rw [empty]⟩

/-- Retargeting cannot fail when an instruction with at least two successors
receives exactly its original number of labels, including jump tables and
TryCall handlers. This is the actual preparation loop's setTargets gate. -/
theorem setTargets_total {i : MInst} (many : 2 ≤ i.targets.length) (ls : List Label)
    (count : ls.length = i.targets.length) : ∃ i',i.setTargets ls = some i' := by
  cases i <;> simp only [MInst.targets,List.length_nil,List.length_cons,
    List.length_append,List.length_map] at many count <;> try omega
  case condBr t e kind =>
    obtain ⟨a,b,rfl⟩ := two_labels count
    exact ⟨_,rfl⟩
  case testBitAndBranch kind t e reg bit =>
    obtain ⟨a,b,rfl⟩ := two_labels count
    exact ⟨_,rfl⟩
  case jtSequence d targets index temp1 temp2 =>
    cases ls with
    | nil => simp at count
    | cons d' targets' =>
      have length : targets'.length = targets.length := by simp at count; omega
      simp [MInst.setTargets,length]
  case tryCall info ti =>
    simp [MInst.setTargets,count]

private theorem forIn_total {α β : Type} (f : α → β → Except String (ForInStep β)) :
    ∀ (xs : List α) (P : Nat → β → Prop),
      (∀ k x st,xs[k]? = some x → P k st → ∃ st',f x st = .ok (.yield st') ∧ P (k+1) st') →
      ∀ st,P 0 st → ∃ out,forIn xs st f = .ok out ∧ P xs.length out
  | [], P, step, st, initial => by exact ⟨st,rfl,initial⟩
  | x :: xs, P, step, st, initial => by
    obtain ⟨next,first,inv⟩ := step 0 x st rfl initial
    obtain ⟨out,rest,last⟩ := forIn_total f xs (fun k => P (k+1))
      (fun k y state hy hi => by
        obtain ⟨result,run,done⟩ := step (k+1) y state (by simpa using hy) hi
        exact ⟨result,run,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using done⟩)
      next inv
    refine ⟨out,?_,by simpa using last⟩
    rw [List.forIn_cons,first]
    simp only [bind,Except.bind]
    exact rest

/-- The actual normalized outer step always succeeds on a block of its real
CFG when the splitting invariant holds. No outgoing-vector shape is assumed. -/
theorem outerStepAt_total {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss ps : Array (Array Nat)} (cfg : Prep.CfgSpec V ss)
    {next0 k : Nat} {st : OuterState} {vb : VBlock}
    (lookup : V[k]? = some vb) (inv : OuterInv V outgoing next0 k st) :
    ∃ st',outerStepAt ss ps outgoing (vb,k) st = .ok (.yield st') ∧
      OuterInv V outgoing next0 (k+1) st' := by
  by_cases small : ss[k]!.size < 2
  · have run : outerStepAt ss ps outgoing (vb,k) st =
        .ok (.yield (st.1,st.2.1.push vb,st.2.2.1.push outgoing[k]!,st.2.2.2.1,st.2.2.2.2)) := by
      simp [outerStepAt,small,pure,Except.pure]
    exact ⟨_,run,outerStepAt_inv cfg lookup inv run⟩
  · obtain ⟨t,ts,back,_,succs,count,_⟩ := cfg.blk k vb lookup
    have ssEq : ss[k]! = ts := by
      rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,succs]
      rfl
    have many : 2 ≤ t.targets.length := by rw [ssEq] at small; omega
    let inner := ((ss[k]!.zip t.targets.toArray).zipIdx).toList.foldl (innerStepAt ps)
      (st.1,st.2.2.2.1,st.2.2.2.2,outgoing[k]!,#[])
    have facts := innerFoldAt_facts ps next0 ((ss[k]!.zip t.targets.toArray).zipIdx).toList
      (st.1,st.2.2.2.1,st.2.2.2.2,outgoing[k]!,#[]) (by simpa using inv.graph.next) inv.graph.edges
    have length : inner.2.2.2.2.toList.length = t.targets.length := by
      have size : inner.2.2.2.2.size = ((ss[k]!.zip t.targets.toArray).zipIdx).toList.length := by
        simpa only [Array.size_empty,Nat.zero_add] using facts.2.2.2.1
      rw [Array.length_toList,size]
      simp [ssEq,count]
    obtain ⟨t',retarget⟩ := setTargets_total many inner.2.2.2.2.toList length
    have run : outerStepAt ss ps outgoing (vb,k) st = .ok (.yield
        (inner.1,st.2.1.push {vb with insts := vb.insts.pop.push t'},
          st.2.2.1.push inner.2.2.2.1,inner.2.1,inner.2.2.1)) := by
      simp only [outerStepAt,small,ite_false,back]
      rw [retarget]
      rfl
    exact ⟨_,run,outerStepAt_inv cfg lookup inv run⟩

/-- The entire actual critical-edge splitting loop succeeds on a valid CFG,
and returns the full graph and selected-copy invariant. -/
theorem outerLoopAt_total {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss ps : Array (Array Nat)} (cfg : Prep.CfgSpec V ss) :
    ∃ st,forIn V.zipIdx (Prep.next0Of V,#[],#[],#[],#[])
      (outerStepAt ss ps outgoing) = .ok st ∧
      OuterInv V outgoing (Prep.next0Of V) V.size st := by
  have init : OuterInv V outgoing (Prep.next0Of V) 0 (Prep.next0Of V,#[],#[],#[],#[]) := by
    refine ⟨⟨by simp,?_,rfl,?_⟩,rfl,?_,?_⟩
    · intro e he
      simp at he
    · intro j _ hj
      simp at hj
    · exact ⟨rfl,fun e _ he => by simp at he⟩
    · intro j _ hj
      simp at hj
  obtain ⟨st,run,inv⟩ := forIn_total (outerStepAt ss ps outgoing) V.zipIdx.toList
    (OuterInv V outgoing (Prep.next0Of V)) (fun k x state lookup invariant => by
      rw [Array.toList_zipIdx,List.getElem?_zipIdx] at lookup
      obtain ⟨vb,hv,rfl⟩ : ∃ vb,V.toList[k]? = some vb ∧ x = (vb,k) := by
        cases hv : V.toList[k]? with
        | none => rw [hv] at lookup; cases lookup
        | some vb =>
          rw [hv] at lookup
          simp only [Option.map_some,Option.some.injEq,Nat.zero_add] at lookup
          exact ⟨vb,rfl,lookup.symm⟩
      exact outerStepAt_total cfg (by simpa only [Array.getElem?_toList] using hv) invariant)
    _ init
  exact ⟨st,by rwa [Array.forIn_toList] at run,
    by simpa only [Array.length_toList,Array.size_zipIdx] using inv⟩

/-- Every synthetic jump targets a label of the original kept graph. -/
def EdgeTargets (V E : Array VBlock) : Prop :=
  ∀ b ∈ E.toList,∀ l,b.insts = #[.jump l] → ∃ k,Prep.lab V l = some k

private theorem edgeTargets_push {V E : Array VBlock} (h : EdgeTargets V E)
    (next label : Nat) (args : Array Reg) (target : ∃ k,Prep.lab V label = some k) :
    EdgeTargets V (E.push {label := next,insts := #[.jump label],branchArgs := args}) := by
  intro b member l insts
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with member | rfl
  · exact h b member l insts
  · have same : label = l := by
      have h := congrArg (fun a : Array MInst => a[0]?) insts
      change some (MInst.jump label) = some (MInst.jump l) at h
      exact MInst.jump.inj (Option.some.inj h)
    rw [← same]
    exact target

private theorem inner_targets {V : Array VBlock} (ps : Array (Array Nat)) :
    ∀ (xs : List ((Nat × Label) × Nat)) (st : InnerState),
      EdgeTargets V st.2.1 → (∀ x ∈ xs,∃ k,Prep.lab V x.1.2 = some k) →
      EdgeTargets V (xs.foldl (innerStepAt ps) st).2.1
  | [], st, initial, targets => initial
  | x :: xs, st, initial, targets => by
    have next : EdgeTargets V (innerStepAt ps st x).2.1 := by
      unfold innerStepAt
      split
      · exact edgeTargets_push initial _ _ _ (targets x (by simp))
      · exact initial
    exact inner_targets ps xs _ next (fun x hx => targets x (List.mem_cons_of_mem _ hx))

private theorem outerStep_targets {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss ps : Array (Array Nat)} (cfg : Prep.CfgSpec V ss)
    {k : Nat} {vb : VBlock} {st st' : OuterState}
    (lookup : V[k]? = some vb) (initial : EdgeTargets V st.2.2.2.1)
    (run : outerStepAt ss ps outgoing (vb,k) st = .ok (.yield st')) :
    EdgeTargets V st'.2.2.2.1 := by
  unfold outerStepAt at run
  dsimp only at run
  split at run
  · simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at run
    subst st'
    exact initial
  · split at run
    · rename_i t back
      split at run
      · simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at run
        subst st'
        apply inner_targets ps _ _ initial
        intro x member
        have pair := Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp member)
        rw [← Array.getElem?_toList,Array.toList_zip] at pair
        have target : t.targets[x.2]? = some x.1.2 := by
          simpa only [List.getElem?_toArray] using (List.getElem?_zip_eq_some.mp pair).2
        obtain ⟨t0,_,back0,_,_,_,targets⟩ := cfg.blk k vb lookup
        rw [back] at back0
        cases back0
        obtain ⟨s,_,find⟩ := targets x.2 x.1.2 target
        exact ⟨s,find⟩
      · simp [throw,throwThe,MonadExceptOf.throw] at run
    · simp [throw,throwThe,MonadExceptOf.throw] at run

/-- Total splitting also establishes target validity for every generated edge,
starting with no synthetic edges. These facts will discharge the final CFG gate. -/
theorem outerLoopAt_total_targets {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss ps : Array (Array Nat)} (cfg : Prep.CfgSpec V ss) :
    ∃ st,forIn V.zipIdx (Prep.next0Of V,#[],#[],#[],#[])
      (outerStepAt ss ps outgoing) = .ok st ∧
      OuterInv V outgoing (Prep.next0Of V) V.size st ∧ EdgeTargets V st.2.2.2.1 := by
  obtain ⟨st,run,inv⟩ := outerLoopAt_total (outgoing := outgoing) (ps := ps) cfg
  refine ⟨st,run,inv,?_⟩
  rw [← Array.forIn_toList] at run
  have result := Prep.forIn_inv (outerStepAt ss ps outgoing) V.zipIdx.toList
    (fun _ state => EdgeTargets V state.2.2.2.1) ?_ ?_
    (Prep.next0Of V,#[],#[],#[],#[]) st (by intro b member; simp at member) run
  · exact result
  · intro k x state state' hx hi hs
    have lookup : V[x.2]? = some x.1 :=
      Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp (List.mem_of_getElem? hx))
    exact outerStep_targets cfg lookup hi hs
  · intro x state state' hs
    unfold outerStepAt at hs
    dsimp only at hs
    split at hs
    · cases hs
    · split at hs
      · split at hs
        · cases hs
        · simp [throw,throwThe,MonadExceptOf.throw] at hs
      · simp [throw,throwThe,MonadExceptOf.throw] at hs

private theorem retarget_term {i i' : MInst} {ls : List Label}
    (h : i.setTargets ls = some i') : i'.isTerminator = true := by
  unfold MInst.setTargets at h
  split at h
  all_goals try split at h
  all_goals cases h
  all_goals rfl

/-- The real split graph has a CFG. The actual loop supplies the invariant
and original-target provenance; no erased-argument graph is executed. -/
theorem split_cfg {vc : VCode} {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss : Array (Array Nat)} {st : OuterState}
    (inv : OuterInv V outgoing (Prep.next0Of V) V.size st)
    (cfg : Prep.CfgSpec V ss) (labels : Prep.Lbls V)
    (targets : EdgeTargets V st.2.2.2.1) :
    ∃ ss' ps',({vc with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss',ps') := by
  have shadowLabels := Prep.lbls2 inv.graph labels
  have actualLabels : Prep.Lbls (st.2.1 ++ st.2.2.2.1) := by
    unfold Prep.Lbls at shadowLabels ⊢
    simpa [Array.toList_append,Array.toList_map,List.map_map,graphBlock,Function.comp_def]
      using shadowLabels
  have oldLabel : ∀ l s,Prep.lab V l = some s → Prep.lab (st.2.1 ++ st.2.2.2.1) l = some s := by
    intro l s find
    obtain ⟨hs,sLabel⟩ := Prep.lab_some find
    have hsB : s < st.2.1.size := by rw [inv.graph.size]; exact hs
    apply Prep.lab_of actualLabels (show s < (st.2.1 ++ st.2.2.2.1).size by simp; omega)
    rw [Array.getElem_append_left hsB,(Prep.rw_fields (inv.graph.rw s hs hsB)).1,sLabel]
  apply Prep.cfg_of
  intro i b placed
  obtain ⟨bound,rfl⟩ := Array.getElem?_eq_some_iff.mp placed
  by_cases old : i < st.2.1.size
  · rw [Array.getElem_append_left old]
    have hi : i < V.size := by rw [← inv.graph.size]; exact old
    obtain ⟨_,t,t',back,back',_,_,_,_,_,last,_,related⟩ := Prep.blk2 inv.graph cfg hi
    obtain ⟨t0,_,back0,term0,_,_,target0⟩ := cfg.blk i V[i] (Array.getElem?_eq_getElem hi)
    rw [back] at back0
    cases back0
    refine ⟨t',back',?_,?_⟩
    · rcases last with rfl | retarget
      · exact term0
      · exact retarget_term retarget
    · intro l hl
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hl
      obtain ⟨original,atOriginal,route⟩ := related j _ (List.getElem?_eq_getElem hj)
      rcases route with same | ⟨_,e,edge⟩
      · obtain ⟨s,_,find⟩ := target0 j original atOriginal
        exact ⟨s,by rw [same]; exact oldLabel original s find⟩
      · obtain ⟨he,shape⟩ := Array.getElem?_eq_some_iff.mp edge
        have heE : e < st.2.2.2.1.size := by simpa only [Array.size_map] using he
        have realLabel : st.2.2.2.1[e].label = t'.targets[j] := by
          have h := congrArg VBlock.label shape
          simpa only [Array.getElem_map,graphBlock] using h
        refine ⟨st.2.1.size+e,Prep.lab_of actualLabels (by simp; omega) ?_⟩
        rw [Array.getElem_append_right (by omega)]
        simpa using realLabel
  · rw [Array.getElem_append_right (Nat.le_of_not_lt old)]
    have he : i-st.2.1.size < st.2.2.2.1.size := by simp at bound; omega
    obtain ⟨l,shape⟩ := inv.graph.edges (i-st.2.1.size) (by simpa only [Array.size_map] using he)
    have insts : st.2.2.2.1[i-st.2.1.size].insts = #[.jump l] := by
      have h := congrArg VBlock.insts shape
      simpa only [Array.getElem_map,graphBlock] using h
    refine ⟨.jump l,by rw [insts]; rfl,rfl,?_⟩
    intro l' member
    have same : l' = l := by simpa only [MInst.targets,List.mem_singleton] using member
    subst l'
    obtain ⟨s,find⟩ := targets _ (Array.getElem_mem_toList he) l insts
    exact ⟨s,oldLabel l s find⟩

end Backend.Proof.PerEdgePrep
