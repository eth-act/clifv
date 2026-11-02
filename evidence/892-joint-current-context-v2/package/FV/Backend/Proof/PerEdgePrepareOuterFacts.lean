import FV.Backend.Proof.PerEdgePrepareLoopFacts

/-! Outer-loop graph and selected-copy invariants for actual indexed preparation.
All legacy preparation and runtime definitions remain unchanged. -/
namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof

private def ArrayExt {α : Type} (a b : Array α) : Prop :=
  a.size ≤ b.size ∧ ∀ i, i < a.size → b[i]? = a[i]?

private theorem arrayExt_refl {α : Type} (a : Array α) : ArrayExt a a :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem arrayExt_push {α : Type} (a : Array α) (x : α) : ArrayExt a (a.push x) :=
  ⟨by simp, fun i hi => by simp [Array.getElem?_push, Nat.ne_of_lt hi]⟩

private theorem arrayExt_trans {α : Type} {a b c : Array α}
    (h : ArrayExt a b) (h' : ArrayExt b c) : ArrayExt a c :=
  ⟨Nat.le_trans h.1 h'.1, fun i hi => by rw [h'.2 i (Nat.lt_of_lt_of_le hi h.1), h.2 i hi]⟩

private theorem innerFoldAt_ext (preds : Array (Array Nat))
    (xs : List ((Nat × Label) × Nat)) (st : InnerState) :
    ArrayExt st.2.1 (xs.foldl (innerStepAt preds) st).2.1 ∧
    ArrayExt st.2.2.1 (xs.foldl (innerStepAt preds) st).2.2.1 := by
  induction xs generalizing st with
  | nil => exact ⟨arrayExt_refl _, arrayExt_refl _⟩
  | cons x xs ih =>
    have step : ArrayExt st.2.1 (innerStepAt preds st x).2.1 ∧
        ArrayExt st.2.2.1 (innerStepAt preds st x).2.2.1 := by
      unfold innerStepAt
      split
      · exact ⟨arrayExt_push _ _, arrayExt_push _ _⟩
      · exact ⟨arrayExt_refl _, arrayExt_refl _⟩
    have later := ih (innerStepAt preds st x)
    exact ⟨arrayExt_trans step.1 later.1, arrayExt_trans step.2 later.2⟩

private theorem copyRoute_ext {E E' : Array VBlock} {rows rows' : Array EdgeRow}
    (hE : ArrayExt E E') (hrows : ArrayExt rows rows')
    {row : EdgeRow} {labels : Array Label} {j : Nat} {target : Label} {args : Array Reg}
    (h : CopyRoute (0,E,rows,row,labels) j target args) :
    CopyRoute (0,E',rows',row,labels) j target args := by
  rcases h with ⟨label,hl,h⟩
  refine ⟨label,hl,?_⟩
  rcases h with direct | ⟨empty,e,block,edge⟩
  · exact .inl direct
  · refine .inr ⟨empty,e,?_,?_⟩
    · rw [hE.2 e (Array.getElem?_eq_some_iff.mp block).1]
      exact block
    · rw [hrows.2 e (Array.getElem?_eq_some_iff.mp edge).1]
      exact edge

/-- A retained block keeps its whole row, or every selected vector has the
direct/synthetic route established by its actual inner loop. -/
def BlockCopies (E : Array VBlock) (rows : Array EdgeRow)
    (vb vb' : VBlock) (original row : EdgeRow) : Prop :=
  (vb' = vb ∧ row = original) ∨
  ∃ (t t' : MInst) (labels : Array Label),
    vb.insts.back? = some t ∧ t.setTargets labels.toList = some t' ∧
    vb' = {vb with insts := vb.insts.pop.push t'} ∧
    ∀ (j : Nat) (target : Label) (args : Array Reg),
      t.targets[j]? = some target → original[j]? = some args →
      CopyRoute (0,E,rows,row,labels) j target args

private theorem blockCopies_ext {E E' : Array VBlock} {rows rows' : Array EdgeRow}
    (hE : ArrayExt E E') (hrows : ArrayExt rows rows')
    {vb vb' : VBlock} {original row : EdgeRow} (h : BlockCopies E rows vb vb' original row) :
    BlockCopies E' rows' vb vb' original row := by
  rcases h with direct | ⟨t,t',labels,ht,ht',hb,routes⟩
  · exact .inl direct
  · exact .inr ⟨t,t',labels,ht,ht',hb,fun j target args hj ha =>
      copyRoute_ext hE hrows (routes j target args hj ha)⟩

/-- Invariant after processing exactly k kept source blocks. Graph facts reuse
the legacy invariant on synthetic blocks with proof-only erased branchArgs;
copy facts retain the executable blocks and their exact per-successor rows. -/
structure OuterInv (V : Array VBlock) (outgoing : Array EdgeRow)
    (next0 k : Nat) (st : OuterState) : Prop where
  graph : Prep.SInv V next0 k (st.1, st.2.1, st.2.2.2.1.map graphBlock)
  rowCount : st.2.2.1.size = st.2.1.size
  paired : EdgeRowsAgree st.2.2.2.1 st.2.2.2.2
  copies : ∀ (j : Nat) (hj : j < V.size) (hb : j < st.2.1.size),
    BlockCopies st.2.2.2.1 st.2.2.2.2 V[j] st.2.1[j] outgoing[j]! st.2.2.1[j]!

private theorem outerStepAt_not_done (ss ps : Array (Array Nat)) (rows : Array EdgeRow)
    (x : VBlock × Nat) (st st' : OuterState) :
    outerStepAt ss ps rows x st ≠ .ok (.done st') := by
  unfold outerStepAt
  dsimp only
  split
  · simp [pure, Except.pure]
  · split
    · split <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    · simp [throw, throwThe, MonadExceptOf.throw]

/-- The actual successful outer step preserves both graph and selected-copy
invariants. The only graph premise is derived by cfg_spec from its real CFG. -/
theorem outerStepAt_inv {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss ps : Array (Array Nat)} (cfg : Prep.CfgSpec V ss)
    {next0 k : Nat} {st st' : OuterState} {vb : VBlock}
    (lookup : V[k]? = some vb) (inv : OuterInv V outgoing next0 k st)
    (run : outerStepAt ss ps outgoing (vb,k) st = .ok (.yield st')) :
    OuterInv V outgoing next0 (k + 1) st' := by
  obtain ⟨hk,hvb⟩ := Array.getElem?_eq_some_iff.mp lookup
  have processed : st.2.1.size = k := inv.graph.size
  have rowPush (row : EdgeRow) : (st.2.2.1.push row).size = (st.2.1.push vb).size := by
    simpa using inv.rowCount
  unfold outerStepAt at run
  dsimp only at run
  split at run
  · simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at run
    subst st'
    refine ⟨⟨inv.graph.next, inv.graph.edges, by simp [inv.graph.size], ?_⟩,
      rowPush _, inv.paired, ?_⟩
    · intro j hV hB
      by_cases old : j < st.2.1.size
      · simpa only [Array.getElem_push, old, dite_true] using inv.graph.rw j hV old
      · have eq : j = k := by have := inv.graph.size; simp only [Array.size_push] at hB; omega
        subst j
        simp only [Array.getElem_push, old, dite_false]
        exact .inl hvb.symm
    · intro j hV hB
      by_cases old : j < st.2.1.size
      · have oldRow : j < st.2.2.1.size := by rw [inv.rowCount]; exact old
        simpa [Array.getElem_push, old, Array.getElem!_eq_getD,
          Array.getD_eq_getD_getElem?, Array.getElem?_push,
          Nat.ne_of_lt oldRow] using inv.copies j hV old
      · have eq : j = k := by have := inv.graph.size; simp only [Array.size_push] at hB; omega
        subst j
        have eqRows : k = st.2.2.1.size := by rw [inv.rowCount,inv.graph.size]
        simp only [Array.getElem_push, old, dite_false]
        exact .inl ⟨hvb.symm, by simp [eqRows]⟩
  · rename_i many
    split at run
    · rename_i t ht
      split at run
      · rename_i t' ht'
        simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at run
        subst st'
        let inner := ((ss[k]!.zip t.targets.toArray).zipIdx).toList.foldl (innerStepAt ps)
          (st.1,st.2.2.2.1,st.2.2.2.2,outgoing[k]!,#[])
        have facts := innerFoldAt_facts ps next0
          ((ss[k]!.zip t.targets.toArray).zipIdx).toList
          (st.1,st.2.2.2.1,st.2.2.2.2,outgoing[k]!,#[])
          (by simpa using inv.graph.next) inv.graph.edges
        have ext := innerFoldAt_ext ps ((ss[k]!.zip t.targets.toArray).zipIdx).toList
          (st.1,st.2.2.2.1,st.2.2.2.2,outgoing[k]!,#[])
        obtain ⟨t0,ts,back,_,succs,count,_⟩ := cfg.blk k vb lookup
        rw [ht] at back
        cases back
        have ssEq : ss[k]! = ts := by
          rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,succs]
          rfl
        have ssSize : ss[k]!.size = t.targets.toArray.size := by simp [ssEq,count]
        have copies := innerFoldAt_copies ps ss[k]! t.targets.toArray outgoing[k]!
          st.1 st.2.2.2.1 st.2.2.2.2 inv.paired ssSize
        refine ⟨⟨by simpa only [Array.size_map] using facts.1,
          facts.2.1,by simp [inv.graph.size],?_⟩,
          by simpa using inv.rowCount, copies.2.1, ?_⟩
        · intro j hV hB
          by_cases old : j < st.2.1.size
          · simp only [Array.getElem_push,old,dite_true]
            exact Prep.rwOk_ext facts.2.2.1 (inv.graph.rw j hV old)
          · have eq : j = k := by have := inv.graph.size; simp only [Array.size_push] at hB; omega
            subst j
            simp only [Array.getElem_push,old,dite_false]
            rw [hvb]
            refine .inr ⟨t,t',inner.2.2.2.2.toList,ht,?_,ht',rfl,?_⟩
            · rw [ssEq] at many
              omega
            · intro m label hm
              rw [Array.getElem?_toList] at hm
              have bound := (Array.getElem?_eq_some_iff.mp hm).1
              rw [copies.1] at bound
              have target : ∃ l, t.targets.toArray[m]? = some l :=
                ⟨_,Array.getElem?_eq_getElem bound⟩
              rcases target with ⟨l,hl⟩
              have ssBound : m < ss[k]!.size := by rw [ssSize]; exact bound
              have item : ((ss[k]!.zip t.targets.toArray).zipIdx).toList[m]? =
                  some ((ss[k]![m],l),m) := by
                rw [Array.toList_zipIdx,List.getElem?_zipIdx]
                have pair : (ss[k]!.zip t.targets.toArray).toList[m]? = some (ss[k]![m],l) := by
                  rw [Array.toList_zip]
                  apply List.getElem?_zip_eq_some.mpr
                  exact ⟨by simp [Array.getElem?_eq_getElem ssBound], by simpa using hl⟩
                rw [pair]
                simp only [Option.map_some,Nat.zero_add]
              obtain ⟨label',atLabel,route⟩ := facts.2.2.2.2.2 m _ item
              simp only [Array.size_empty,Nat.zero_add] at atLabel
              rw [hm] at atLabel
              cases atLabel
              have oldTarget : t.targets[m]? = some l := by simpa using hl
              rcases route with same | ⟨e,edge⟩
              · exact .inl (by simpa [same] using oldTarget)
              · exact .inr ⟨e,l,edge,oldTarget⟩
        · intro j hV hB
          by_cases old : j < st.2.1.size
          · have oldRow : j < st.2.2.1.size := by rw [inv.rowCount]; exact old
            simp only [Array.getElem_push,old,dite_true]
            have preserved := blockCopies_ext ext.1 ext.2 (inv.copies j hV old)
            simpa [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,
              Array.getElem?_push,Nat.ne_of_lt oldRow] using preserved
          · have eq : j = k := by have := inv.graph.size; simp only [Array.size_push] at hB; omega
            subst j
            simp only [Array.getElem_push,old,dite_false]
            rw [hvb]
            have eqRows : k = st.2.2.1.size := by rw [inv.rowCount,inv.graph.size]
            refine .inr ⟨t,t',inner.2.2.2.2,ht,ht',rfl,?_⟩
            intro m target args hm ha
            have route := copies.2.2 m target args (by simpa using hm) ha
            have rowEq : (st.2.2.1.push inner.2.2.2.1)[k]! = inner.2.2.2.1 := by
              rw [eqRows]
              simp
            change CopyRoute (0,inner.2.1,inner.2.2.1,
              (st.2.2.1.push inner.2.2.2.1)[k]!,inner.2.2.2.2) m target args
            rw [rowEq]
            exact route
      · simp [throw,throwThe,MonadExceptOf.throw] at run
    · simp [throw,throwThe,MonadExceptOf.throw] at run

/-- Every completed actual splitting loop establishes the full graph and
selected-copy invariant for all kept blocks. -/
theorem outerLoopAt_inv {V : Array VBlock} {outgoing : Array EdgeRow}
    {ss ps : Array (Array Nat)} (cfg : Prep.CfgSpec V ss) {st : OuterState}
    (run : forIn V.zipIdx (Prep.next0Of V,#[],#[],#[],#[])
      (outerStepAt ss ps outgoing) = .ok st) :
    OuterInv V outgoing (Prep.next0Of V) V.size st := by
  rw [← Array.forIn_toList] at run
  have invariant := Prep.forIn_inv (outerStepAt ss ps outgoing) V.zipIdx.toList
    (OuterInv V outgoing (Prep.next0Of V)) ?_ (outerStepAt_not_done ss ps outgoing)
    (Prep.next0Of V,#[],#[],#[],#[]) st ?_ run
  · simpa only [Array.length_toList,Array.size_zipIdx] using invariant
  · intro k x state state' hx hi hs
    rw [Array.toList_zipIdx,List.getElem?_zipIdx] at hx
    have input : ∃ vb, V.toList[k]? = some vb ∧ x = (vb,k) := by
      cases hv : V.toList[k]? with
      | none => rw [hv] at hx; cases hx
      | some vb =>
        rw [hv] at hx
        simp only [Option.map_some,Option.some.injEq,Nat.zero_add] at hx
        exact ⟨vb,rfl,hx.symm⟩
    rcases input with ⟨vb,hv,rfl⟩
    exact outerStepAt_inv cfg (by simpa only [Array.getElem?_toList] using hv) hi hs
  · refine ⟨⟨?_,?_,rfl,?_⟩,rfl,?_,?_⟩
    · simp
    · intro e he
      simp at he
    · intro j _ hj
      simp at hj
    · exact ⟨rfl,fun e _ he => by simp at he⟩
    · intro j _ hj
      simp at hj

/-- Actual successful prepareAt establishes the complete outer-loop invariant
internally, together with its exact filtering and final RPO stages. -/
theorem prepareAt_outer_facts {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) :
    ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
      vc.cfg = .ok (ss0,ps0) ∧
      ({vc with blocks := (keptAt vc edges ss0).map Prod.fst} : VCode).cfg = .ok (ss1,ps1) ∧
      OuterInv ((keptAt vc edges ss0).map Prod.fst) ((keptAt vc edges ss0).map Prod.snd)
        (Prep.next0Of ((keptAt vc edges ss0).map Prod.fst))
        ((keptAt vc edges ss0).map Prod.fst).size st ∧
      ({vc with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
      p = ⟨{vc with blocks := (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!},
        (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!⟩ := by
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,loop,cfg2,result⟩ := prepareAt_stages run
  exact ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,
    outerLoopAt_inv (Prep.cfg_spec cfg1) loop,cfg2,result⟩

end Backend.Proof.PerEdgePrep
