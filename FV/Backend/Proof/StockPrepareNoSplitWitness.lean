import FV.Backend.Proof.StockPrepareNoSplit
import FV.Backend.Proof.StockIncomingWitness

namespace Backend.Stock.Proof.PrepareNoSplitWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem cfgSpec_unique {V : Array VBlock} {ss ss' : Array (Array Nat)}
    (left : Prep.CfgSpec V ss) (right : Prep.CfgSpec V ss') : ss = ss' := by
  apply Array.ext
  · rw [left.size,right.size]
  · intro b hb hb'
    have hV : b < V.size := by rw [← left.size]; exact hb
    obtain ⟨t,sb,back,_,atRow,count,targets⟩ := left.blk b V[b] (Array.getElem?_eq_getElem hV)
    obtain ⟨t',sb',back',_,atRow',count',targets'⟩ := right.blk b V[b] (Array.getElem?_eq_getElem hV)
    rw [back] at back'
    cases back'
    have row : ss[b] = sb := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb]; exact atRow)
    have row' : ss'[b] = sb' := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb']; exact atRow')
    rw [row,row']
    apply Array.ext
    · rw [count,count']
    · intro j hj hj'
      obtain ⟨l,hl⟩ : ∃ l,t.targets[j]? = some l :=
        ⟨_,List.getElem?_eq_getElem (by rw [← count]; exact hj)⟩
      obtain ⟨s,hs,find⟩ := targets j l hl
      obtain ⟨s',hs',find'⟩ := targets' j l hl
      rw [find] at find'
      cases find'
      rw [Array.getElem?_eq_getElem hj] at hs
      rw [Array.getElem?_eq_getElem hj'] at hs'
      exact (Option.some.inj hs).trans (Option.some.inj hs').symm


/-- Complete original-scope source, raw preparation, global checked
fallback and physical lowering inhabit the actual no-additional-split stages. -/
theorem stock_cycle_no_additional_split_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ ArityOk IndexedSpillFixture.function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      (∃ (ss0 ps0 : Array (Array Nat)), result.code.cfg = .ok (ss0,ps0) ∧
      NoCriticalEdges ss0 ps0 ∧
    ∃ (ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
      ({result.code with blocks := Prep.keep result.code.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1) ∧
      forIn ((keptAt result.code result.edgeArgs ss0).map Prod.fst).zipIdx
        (Prep.next0Of ((keptAt result.code result.edgeArgs ss0).map Prod.fst),#[],#[],#[],#[])
        (outerStepAt ss1 ps1 ((keptAt result.code result.edgeArgs ss0).map Prod.snd)) = .ok st ∧
      st.2.2.2.1 = #[] ∧ st.2.2.2.2 = #[] ∧ st.1 = Prep.next0Of (Prep.keep result.code.blocks (reachable ss0)) ∧
      ({result.code with blocks := st.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
      ss2 = ss1 ∧
      p = ⟨{result.code with blocks := (rpo ss2).map fun i => st.2.1[i]!},(rpo ss2).map fun i => st.2.2.1[i]!⟩) := by
  obtain ⟨fixture⟩ := IndexedSpillFixture.cycle_fixture
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,raw,fallback,accepted,physical,rest⟩
  have arity : ArityOk IndexedSpillFixture.function := arityOk_of (by decide +kernel)
  exact ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,
    stock_prepare_no_new_edges run scope raw⟩

/-- Complete original-scope source, raw preparation, global checked
fallback and physical lowering inhabit the actual no-additional-split stages. -/
theorem stock_forced_try_no_additional_split_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc),
      Stock.lower (CriticalSplitFixture.function indirect) = .ok result ∧ LowerScope (CriticalSplitFixture.function indirect) ∧
      Dominated (CriticalSplitFixture.function indirect) ∧ ArityOk (CriticalSplitFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      (∃ (ss0 ps0 : Array (Array Nat)), result.code.cfg = .ok (ss0,ps0) ∧
      NoCriticalEdges ss0 ps0 ∧
    ∃ (ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
      ({result.code with blocks := Prep.keep result.code.blocks (reachable ss0)} : VCode).cfg = .ok (ss1,ps1) ∧
      forIn ((keptAt result.code result.edgeArgs ss0).map Prod.fst).zipIdx
        (Prep.next0Of ((keptAt result.code result.edgeArgs ss0).map Prod.fst),#[],#[],#[],#[])
        (outerStepAt ss1 ps1 ((keptAt result.code result.edgeArgs ss0).map Prod.snd)) = .ok st ∧
      st.2.2.2.1 = #[] ∧ st.2.2.2.2 = #[] ∧ st.1 = Prep.next0Of (Prep.keep result.code.blocks (reachable ss0)) ∧
      ({result.code with blocks := st.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
      ss2 = ss1 ∧
      p = ⟨{result.code with blocks := (rpo ss2).map fun i => st.2.1[i]!},(rpo ss2).map fun i => st.2.2.1[i]!⟩) := by
  obtain ⟨result,p,rf,af,source,run,scope,dominated,arity,raw,fallback,accepted,physical,rest⟩ :=
    IncomingWitness.stock_incoming_single_try_witness indirect
  exact ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,
    stock_prepare_no_new_edges run scope raw⟩

private theorem keep_four {V : Array VBlock} (size : V.size = 4) :
    Prep.keep V #[true,true,true,true] = V := by
  have form : V = #[V[0]'(by omega),V[1]'(by omega),V[2]'(by omega),V[3]'(by omega)] := by
    apply Array.toList_inj.mp
    exact List.eq_getElem_of_length_eq_four V.toList (by simpa using size)
  calc
    Prep.keep V #[true,true,true,true] =
        Prep.keep #[V[0],V[1],V[2],V[3]] #[true,true,true,true] :=
      congrArg (fun W => Prep.keep W #[true,true,true,true]) form
    _ = V := by simpa [Prep.keep] using form.symm

/-- Complete cyclic source inhabits actual distinct incoming multiplicities,
low-degree indexed uniqueness and selected-edge reflection through the real
reachable filter. All original conditions and checked/physical stages remain. -/
theorem stock_cycle_filtered_incoming_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ss ps : Array (Array Nat)),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ ArityOk IndexedSpillFixture.function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      result.code.cfg = .ok (ss,ps) ∧ NoCriticalEdges ss ps ∧
      1 < ps[1]!.size ∧ ps[3]!.size ≤ 1 ∧
      (∃ other index row,ss[other]? = some row ∧ row[index]? = some 1 ∧ (other ≠ 0 ∨ index ≠ 0)) ∧
      (∀ other index row,ss[other]? = some row → row[index]? = some 3 → other = 1 ∧ index = 1) ∧
      Prep.keep result.code.blocks (reachable ss) = result.code.blocks ∧
      keepOrigin result.code.blocks (reachable ss) 0 = 0 ∧
      (∃ oldRow,ss[keepOrigin result.code.blocks (reachable ss) 0]? = some oldRow ∧
        oldRow[0]? = some (keepOrigin result.code.blocks (reachable ss) 1) ∧ oldRow.size = 1) := by
  obtain ⟨result,p,rf,af,source,run,scope,dominated,arity,raw,fallback,accepted,physical,
    nodup,node,sourceRun,first,second,exitUnique,rest⟩ := IncomingWitness.stock_incoming_cycle_witness
  obtain ⟨_,ss,ps,cfg,_⟩ := prepareAt_input_facts raw
  have orderRun : blockOrder IndexedSpillFixture.function = .ok {
      nodes := #[.original 0,.original 1,.edge 1 0 1,.original 2],successors := #[#[1],#[2,3],#[1],#[]]} := by cbv
  have order := Except.ok.inj ((stock_lower_order run).symm.trans orderRun)
  have actual := cfgSpec_unique (Prep.cfg_spec cfg) (stock_lower_cfg run scope)
  have rows : ss = #[#[1],#[2,3],#[1],#[]] := by rw [actual,order]
  have count : result.code.blocks.size = 4 := by rw [← (Prep.cfg_spec cfg).size,rows]; rfl
  have atFirst : ss[0]? = some #[1] := by rw [rows]; rfl
  have atCritical : ss[2]? = some #[1] := by rw [rows]; rfl
  have atExit : ss[1]? = some #[2,3] := by rw [rows]; rfl
  have unique : ∀ (b j : Nat) (row : Array Nat),ss[b]? = some row → row[j]? = some 3 → b = 1 ∧ j = 1 := by
    intro b j row atRow edge
    exact exitUnique b j row (by rw [← actual]; exact atRow) edge
  have small := cfg_pred_size_le_one_of_unique cfg (target := 3) (by omega) (by
    intro b j b' j' row row' atRow edge atRow' edge'
    have left := unique b j row atRow edge
    have right := unique b' j' row' atRow' edge'
    exact ⟨left.1.trans right.1.symm,left.2.trans right.2.symm⟩)
  have shared : 1 < ps[1]!.size := by
    apply Nat.lt_of_not_ge
    intro low
    have same := cfg_pred_size_le_one_unique cfg (j := 0) atFirst rfl low (index := 0) atCritical rfl
    omega
  have graph := stock_lower_no_critical_edges run scope cfg
  have live : reachable ss = #[true,true,true,true] := by rw [rows]; cbv
  have kept : Prep.keep result.code.blocks (reachable ss) = result.code.blocks := by rw [live]; exact keep_four count
  have cfg1 : ({result.code with blocks := Prep.keep result.code.blocks (reachable ss)} : VCode).cfg = .ok (ss,ps) := by
    rw [kept]; exact cfg
  obtain ⟨_,labels⟩ := stock_prepare_domain run scope
  have origin : keepOrigin result.code.blocks (reachable ss) 0 = 0 := by
    unfold keepOrigin
    rw [kept,getElem!_pos result.code.blocks 0 (by omega),Prep.lab_of labels (by omega) rfl]
    rfl
  have reflected := keep_cfg_edge cfg cfg1 labels (j := 0) atFirst rfl
  have keptGraph := stock_kept_no_critical_edges run scope cfg cfg1
  have sameEdge : ∀ other index row,ss[other]? = some row → row[index]? = some 3 → other = 1 ∧ index = 1 := by
    intro other index row otherAt otherEdge
    exact cfg_pred_size_le_one_unique cfg (j := 1) atExit rfl small otherAt otherEdge
  exact ⟨result,p,rf,af,ss,ps,run,scope,dominated,arity,raw,fallback,accepted,physical,cfg,keptGraph,
    shared,small,cfg_multiple_preds_other cfg (j := 0) atFirst rfl shared,sameEdge,kept,origin,reflected⟩

end Backend.Stock.Proof.PrepareNoSplitWitness
