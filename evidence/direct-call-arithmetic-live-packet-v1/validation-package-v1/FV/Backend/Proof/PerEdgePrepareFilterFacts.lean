import FV.Backend.Proof.PerEdgePrepareOuterFacts

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof

private theorem select_fst {α β : Type} : ∀ (xs : List α) (ys : List β) (live : List Bool),
    ys.length = xs.length →
    (((xs.zip ys).zip live).filterMap (fun (x,b) => if b then some x else none)).map Prod.fst =
      (xs.zip live).filterMap (fun (x,b) => if b then some x else none)
  | [], ys, live, h => by simp
  | x :: xs, [], live, h => by simp at h
  | x :: xs, y :: ys, [], h => by simp
  | x :: xs, y :: ys, b :: live, h => by
    have tail : ys.length = xs.length := by simpa using h
    cases b <;> simp [select_fst xs ys live tail]

/-- Indexed filtering keeps exactly the original legacy kept blocks whenever
the input row count matches the input block count. -/
theorem keptAt_blocks {vc : VCode} {edges : Array EdgeRow} {ss : Array (Array Nat)}
    (count : edges.size = vc.blocks.size) :
    (keptAt vc edges ss).map Prod.fst = Prep.keep vc.blocks (reachable ss) := by
  apply Array.toList_inj.mp
  simp only [keptAt,Array.toList_map,Array.toList_filterMap,Array.toList_zip]
  exact select_fst _ _ _ (by simpa using count)

/-- Filtering never separates a retained block from its original selected-copy
row. Both components originate at the same live input index. -/
theorem keptAt_source {vc : VCode} {edges : Array EdgeRow} {ss : Array (Array Nat)}
    {k : Nat} (hk : k < (keptAt vc edges ss).size) :
    ∃ b : Nat, vc.blocks[b]? = some (keptAt vc edges ss)[k].1 ∧
      edges[b]? = some (keptAt vc edges ss)[k].2 ∧ Prep.mk (reachable ss) b := by
  have member := Array.getElem_mem_toList hk
  change (keptAt vc edges ss)[k] ∈ (keptAt vc edges ss).toList at member
  unfold keptAt at member
  rw [Array.toList_filterMap,Array.toList_zip] at member
  obtain ⟨b,pair,live⟩ := Prep.kept_mem.mp member
  rw [Array.toList_zip] at pair
  obtain ⟨block,row⟩ := List.getElem?_zip_eq_some.mp pair
  rw [Array.getElem?_toList] at block row
  exact ⟨b,block,row,Prep.mk_iff.mpr live⟩

private def rowCheck (ss : Array (Array Nat)) (x : EdgeRow × Nat) (_ : PUnit.{1}) :
    Except String (ForInStep PUnit.{1}) := do
  if x.1.size != ss[x.2]!.size then
    throw s!"block {x.2}: per-successor vector count differs"
  pure (.yield PUnit.unit)

private theorem rowCheck_valid {ss : Array (Array Nat)} {x : EdgeRow × Nat}
    {state state' : PUnit.{1}} (run : rowCheck ss x state = .ok (.yield state')) :
    x.1.size = ss[x.2]!.size := by
  unfold rowCheck at run
  split at run
  · simp [bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at run
  · rename_i valid
    simpa using valid

private theorem rowCheck_not_done (ss : Array (Array Nat)) (x : EdgeRow × Nat)
    (state state' : PUnit.{1}) : rowCheck ss x state ≠ .ok (.done state') := by
  unfold rowCheck
  split <;> simp [bind,Except.bind,throw,throwThe,MonadExceptOf.throw,pure,Except.pure]

private theorem rowLoop_valid {ss : Array (Array Nat)} {edges : Array EdgeRow}
    (run : forIn edges.zipIdx PUnit.unit (rowCheck ss) = .ok PUnit.unit) :
    ∀ (b : Nat) (row : EdgeRow), edges[b]? = some row → row.size = ss[b]!.size := by
  rw [← Array.forIn_toList] at run
  let P : Nat → PUnit.{1} → Prop := fun k _ => ∀ b row,
    b < k → edges[b]? = some row → row.size = ss[b]!.size
  have all := Prep.forIn_inv (rowCheck ss) edges.zipIdx.toList P ?_
    (rowCheck_not_done ss) PUnit.unit PUnit.unit ?_ run
  · intro b row hb
    apply all b row ?_ hb
    simpa using (Array.getElem?_eq_some_iff.mp hb).1
  · intro k x state state' hx hi hs
    rw [Array.toList_zipIdx,List.getElem?_zipIdx] at hx
    obtain ⟨row,hr,hx⟩ : ∃ row, edges.toList[k]? = some row ∧ x = (row,k) := by
      cases hr : edges.toList[k]? with
      | none => rw [hr] at hx; cases hx
      | some row =>
        rw [hr] at hx
        simp only [Option.map_some,Option.some.injEq,Nat.zero_add] at hx
        exact ⟨row,rfl,hx.symm⟩
    subst x
    intro b row' hb hr'
    by_cases old : b < k
    · exact hi b row' old hr'
    · have eq : b = k := by omega
      subst b
      rw [Array.getElem?_toList,hr'] at hr
      cases hr
      exact rowCheck_valid hs
  · intro b row hb
    omega

/-- Actual success internally establishes both input dimensions checked by
prepareAt. They are consequences of execution, not new accepted-input premises. -/
theorem prepareAt_input_facts {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) :
    edges.size = vc.blocks.size ∧ ∃ ss ps : Array (Array Nat),
      vc.cfg = .ok (ss,ps) ∧
      ∀ (b : Nat) (row : EdgeRow), edges[b]? = some row → row.size = ss[b]!.size := by
  unfold prepareAt at run
  obtain ⟨⟨ss,ps⟩,cfg,run⟩ := Except.bind_ok run
  dsimp only at run
  cases count : (edges.size != vc.blocks.size) with
  | true => simp [count,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at run
  | false =>
    simp only [count,Bool.false_eq_true,ite_false] at run
    obtain ⟨answer,rows,_⟩ := Except.bind_ok run
    cases answer
    refine ⟨by simpa using count,ss,ps,cfg,?_⟩
    apply rowLoop_valid
    exact rows

/-- The actual producer's checked input dimensions, original kept-block graph,
and full graph/copy splitting invariant are established together. This connects
the indexed proof directly to the original reachability and RPO lemmas. -/
theorem prepareAt_kept_facts {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) :
    edges.size = vc.blocks.size ∧
    ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
      vc.cfg = .ok (ss0,ps0) ∧
      (∀ (b : Nat) (row : EdgeRow), edges[b]? = some row → row.size = ss0[b]!.size) ∧
      ({vc with blocks := Prep.keep vc.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1) ∧
      OuterInv (Prep.keep vc.blocks (reachable ss0)) ((keptAt vc edges ss0).map Prod.snd)
        (Prep.next0Of (Prep.keep vc.blocks (reachable ss0)))
        (Prep.keep vc.blocks (reachable ss0)).size st ∧
      ({vc with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
      p = ⟨{vc with blocks := (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!},
        (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!⟩ := by
  obtain ⟨count,ss,ps,cfg,rows⟩ := prepareAt_input_facts run
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,inv,cfg2,result⟩ := prepareAt_outer_facts run
  rw [cfg] at cfg0
  cases cfg0
  rw [keptAt_blocks count] at cfg1 inv
  exact ⟨count,ss,ps,ss1,ps1,ss2,ps2,st,cfg,rows,cfg1,inv,cfg2,result⟩

end Backend.Proof.PerEdgePrep
