import FV.Backend.Proof.StockPreparedJump
import FV.Backend.Proof.StockIncomingWitness
import FV.Backend.Proof.StockCfgTotal

namespace Backend.Stock.Proof.JumpCfgWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep
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

private theorem reachable_of_reach {ss : Array (Array Nat)} (bounds : Prep.SuccsIn ss) (nonzero : ss.size ≠ 0)
    {b : Nat} (reach : Prep.Reach ss b) : Prep.mk (reachable ss) b := by
  have facts := Prep.reachable_spec bounds nonzero
  induction reach with
  | entry => exact facts.2.1
  | step reach member ih => exact facts.2.2.1 _ ih _ member

private def source (synthetic : Bool) : Nat := if synthetic then 2 else 0
private def other (synthetic : Bool) : Nat := if synthetic then 0 else 2
private theorem cycle_order : blockOrder IndexedSpillFixture.function = .ok {
    nodes := #[.original 0,.original 1,.edge 1 0 1,.original 2],successors := #[#[1],#[2,3],#[1],#[]]} := by cbv
private theorem try_order (indirect : Bool) : blockOrder (CriticalSplitFixture.function indirect) = .ok {
    nodes := #[.original 0,.edge 0 0 1,.original 1],successors := #[#[1],#[2],#[]]} := by cases indirect <;> cbv

/-- Both actual shared-loop predecessor kinds in a complete cyclic source end
in exact emitted jumps and have real prepared jump counterparts. Original
scope/dominance/arity, source CFG reachability, labels, installed blocks,
instruction counts, parameters and checked/physical stages are retained. -/
theorem stock_shared_jump_counterpart_witness (synthetic : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ss0 ps0 : Array (Array Nat)) (q : Nat) (vb vb' : VBlock) (label : Label),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ ArityOk IndexedSpillFixture.function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      result.code.cfg = .ok (ss0,ps0) ∧ Prep.mk (reachable ss0) (source synthetic) ∧
      result.order.successors[source synthetic]? = some #[1] ∧
      result.order.successors[other synthetic]? = some #[1] ∧
      result.code.blocks[source synthetic]? = some vb ∧ vb.insts.back? = some (.jump 1) ∧
      sigmaOf result.code p.code (source synthetic) = some q ∧ p.code.blocks[q]? = some vb' ∧
      vb'.insts.back? = some (.jump label) ∧ vb'.insts.size = vb.insts.size ∧ vb'.params = vb.params := by
  obtain ⟨fixture⟩ := IndexedSpillFixture.cycle_fixture
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,raw,fallback,accepted,physical,rest⟩
  have order := Except.ok.inj ((stock_lower_order run).symm.trans cycle_order)
  obtain ⟨_,ss0,ps0,cfg0,_⟩ := prepareAt_input_facts raw
  have actual := cfgSpec_unique (Prep.cfg_spec cfg0) (stock_lower_cfg run scope)
  have row : result.order.successors[source synthetic]? = some #[1] := by rw [order]; cases synthetic <;> rfl
  have otherRow : result.order.successors[other synthetic]? = some #[1] := by rw [order]; cases synthetic <;> rfl
  obtain ⟨nonempty,_⟩ := stock_prepare_domain run scope
  have notZero : ss0.size ≠ 0 := by rw [(Prep.cfg_spec cfg0).size]; omega
  have reach : Prep.Reach ss0 (source synthetic) := by
    rw [actual,order]
    cases synthetic
    · exact .entry
    · exact .step (b := 1) (s := 2) (.step (b := 0) (s := 1) .entry (by decide)) (by decide)
  have live := reachable_of_reach (Prep.succsIn_of (Prep.cfg_spec cfg0)) notZero reach
  obtain ⟨ss3,ps3,q,vb,vb',label,atSource,back,cfg3,sigma,atNew,newBack,size,params⟩ :=
    stock_prepare_shared_jump_counterpart run scope raw cfg0 (j := 0) (j₂ := 0) row rfl otherRow rfl
      (.inl (by cases synthetic <;> decide)) live
  exact ⟨result,p,rf,af,ss0,ps0,q,vb,vb',label,run,scope,dominated,arityOk_of (by decide +kernel),
    raw,fallback,accepted,physical,cfg0,live,row,otherRow,atSource,back,sigma,atNew,newBack,size,params⟩

/-- Complete direct/indirect forced one-successor TryCall programs preserve
the actual synthetic jump through preparation and RPO. Original unreachable
source predecessor and every original condition/pipeline stage remain. -/
theorem stock_forced_try_jump_counterpart_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ss0 ps0 : Array (Array Nat)) (q : Nat) (vb vb' : VBlock) (old label : Label),
      Stock.lower (CriticalSplitFixture.function indirect) = .ok result ∧ LowerScope (CriticalSplitFixture.function indirect) ∧
      Dominated (CriticalSplitFixture.function indirect) ∧ ArityOk (CriticalSplitFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      result.order.nodes[1]? = some (.edge 0 0 1) ∧ result.code.cfg = .ok (ss0,ps0) ∧
      Prep.mk (reachable ss0) 1 ∧ result.code.blocks[1]? = some vb ∧ vb.insts = #[.jump old] ∧
      sigmaOf result.code p.code 1 = some q ∧ p.code.blocks[q]? = some vb' ∧
      vb'.insts.back? = some (.jump label) ∧ vb'.insts.size = 1 ∧ vb'.params = vb.params := by
  obtain ⟨result,p,rf,af,source,run,scope,dominated,arity,raw,fallback,accepted,physical,rest⟩ :=
    IncomingWitness.stock_incoming_single_try_witness indirect
  have order := Except.ok.inj ((stock_lower_order run).symm.trans (try_order indirect))
  have critical : result.order.nodes[1]? = some (.edge 0 0 1) := by rw [order]; rfl
  obtain ⟨input,next,args,old,call,succs,target,placed⟩ := stock_lower_critical_code run critical
  obtain ⟨_,ss0,ps0,cfg0,_⟩ := prepareAt_input_facts raw
  have actual := cfgSpec_unique (Prep.cfg_spec cfg0) (stock_lower_cfg run scope)
  obtain ⟨nonempty,_⟩ := stock_prepare_domain run scope
  have notZero : ss0.size ≠ 0 := by rw [(Prep.cfg_spec cfg0).size]; omega
  have reach : Prep.Reach ss0 1 := by rw [actual,order]; exact .step .entry (by decide)
  have live := reachable_of_reach (Prep.succsIn_of (Prep.cfg_spec cfg0)) notZero reach
  obtain ⟨ss3,ps3,q,vb',label,cfg3,sigma,atNew,newBack,size,params⟩ :=
    stock_prepare_jump_counterpart run scope raw cfg0 placed live (by rfl)
  exact ⟨result,p,rf,af,ss0,ps0,q,_,vb',old,label,run,scope,dominated,arity,raw,fallback,accepted,physical,
    critical,cfg0,live,placed,rfl,sigma,atNew,newBack,size,params⟩

end Backend.Stock.Proof.JumpCfgWitness
