import FV.Backend.Proof.StockPreparedSharedJump
import FV.Backend.Proof.StockJumpCfgWitness
import FV.Backend.Proof.PerEdgeSpillJumpWitness

namespace Backend.Stock.Proof.PreparedIncomingWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem incoming_of_pred {vc : VCode} {ss ps : Array (Array Nat)}
    (cfg : vc.cfg = .ok (ss,ps)) {target b : Nat} (bound : target < vc.blocks.size)
    (member : b ∈ (ps[target]!).toList) :
    ∃ (j : Nat) (row : Array Nat),ss[b]? = some row ∧ row[j]? = some target := by
  have pred := cfg_preds cfg bound
  rw [getElem!_def,pred] at member
  simp only [Option.getD_some,List.toList_toArray] at member
  unfold predsOf at member
  obtain ⟨⟨row,source⟩,atSource,replicated⟩ := List.mem_flatMap.mp member
  obtain ⟨positive,same⟩ := List.mem_replicate.mp replicated
  change b = source at same
  subst source
  have targetMember : target ∈ row.toList := List.count_pos_iff.mp (Nat.pos_of_ne_zero positive)
  obtain ⟨j,jBound,atTarget⟩ := List.getElem_of_mem targetMember
  have atRow := List.mem_zipIdx_iff_getElem?.mp atSource
  refine ⟨j,row,by simpa using atRow,?_⟩
  rw [Array.getElem?_eq_getElem (by simpa using jBound)]
  exact congrArg some atTarget

/-- Both original and inserted shared-loop predecessors in a complete checked
source instantiate universal actual prepared incoming reflection and exact
shared-target jump classification. All source conditions/stages are retained. -/
theorem stock_prepared_shared_jump_witness (synthetic : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ss ps ss0 ps0 : Array (Array Nat)) (origin : Nat → Nat) (vb : VBlock),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ ArityOk IndexedSpillFixture.function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      p.code.cfg = .ok (ss,ps) ∧ result.code.cfg = .ok (ss0,ps0) ∧
      (∀ q,q < p.code.blocks.size → origin q < result.code.blocks.size ∧
        result.code.blocks[origin q]!.label = p.code.blocks[q]!.label ∧ Prep.mk (reachable ss0) (origin q)) ∧
      (∀ q r,q < p.code.blocks.size → r < p.code.blocks.size → origin q = origin r → q = r) ∧
      (∀ (q j target : Nat) (row : Array Nat),ss[q]? = some row → row[j]? = some target →
        ∃ oldRow,result.order.successors[origin q]? = some oldRow ∧
          oldRow[j]? = some (origin target) ∧ oldRow.size = row.size) ∧
      1 < ps[1]!.size ∧ ss[if synthetic then 3 else 0]? = some #[1] ∧
      p.code.blocks[if synthetic then 3 else 0]? = some vb ∧
      vb.insts.back? = some (.jump p.code.blocks[1]!.label) := by
  obtain ⟨result,p,rf,af,tb,ss,ps,run,scope,dominated,raw,fallback,accepted,physical,cfg,
    atSynthetic,preds,target,copies,installed⟩ := SpillJumpWitness.stock_spill_jump_route_witness
  have shared : 1 < ps[1]!.size := by rw [getElem!_def,preds]; decide
  have targetBound := (Array.getElem?_eq_some_iff.mp target).1
  obtain ⟨j,row,atOriginal,edgeOriginal⟩ := incoming_of_pred cfg targetBound
    (b := 0) (by rw [getElem!_def,preds]; decide)
  have selected : ∃ (j : Nat) (row : Array Nat),ss[if synthetic then 3 else 0]? = some row ∧ row[j]? = some 1 := by
    cases synthetic
    · exact ⟨j,row,atOriginal,edgeOriginal⟩
    · exact ⟨0,#[1],atSynthetic,rfl⟩
  obtain ⟨j,row,atRow,edge⟩ := selected
  obtain ⟨vb,block,back,single,zero⟩ := stock_prepare_shared_jump_cfg run scope raw cfg atRow edge shared
  obtain ⟨ss0,ps0,origin,cfg0,provenance,injective,incoming⟩ := stock_prepared_incoming run scope raw cfg
  exact ⟨result,p,rf,af,ss,ps,ss0,ps0,origin,vb,run,scope,dominated,arityOk_of (by decide +kernel),
    raw,fallback,accepted,physical,cfg,cfg0,provenance,injective,incoming,shared,single,block,back⟩

/-- Complete direct/indirect forced one-successor TryCall sources retain their
actual inserted jump and live original-block origins through real preparation.
Unreachable source predecessors, original conditions and all stages remain. -/
theorem stock_prepared_forced_try_incoming_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ss ps ss0 ps0 : Array (Array Nat)) (origin : Nat → Nat) (q : Nat) (vb : VBlock) (label : Label),
      Stock.lower (CriticalSplitFixture.function indirect) = .ok result ∧ LowerScope (CriticalSplitFixture.function indirect) ∧
      Dominated (CriticalSplitFixture.function indirect) ∧ ArityOk (CriticalSplitFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      p.code.cfg = .ok (ss,ps) ∧ result.code.cfg = .ok (ss0,ps0) ∧
      (∀ b,b < p.code.blocks.size → origin b < result.code.blocks.size ∧
        result.code.blocks[origin b]!.label = p.code.blocks[b]!.label ∧ Prep.mk (reachable ss0) (origin b)) ∧
      (∀ b r,b < p.code.blocks.size → r < p.code.blocks.size → origin b = origin r → b = r) ∧
      (∀ (b j target : Nat) (row : Array Nat),ss[b]? = some row → row[j]? = some target →
        ∃ oldRow,result.order.successors[origin b]? = some oldRow ∧
          oldRow[j]? = some (origin target) ∧ oldRow.size = row.size) ∧
      result.order.nodes[1]? = some (.edge 0 0 1) ∧ p.code.blocks[q]? = some vb ∧
      vb.insts.back? = some (.jump label) ∧ vb.insts.size = 1 := by
  obtain ⟨result,p,rf,af,ssA,psA,q,vb0,vb,old,label,run,scope,dominated,arity,raw,fallback,accepted,physical,
    critical,cfgA,live,atOld,oldBack,sigma,atNew,back,size,params⟩ :=
    JumpCfgWitness.stock_forced_try_jump_counterpart_witness indirect
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨_,ss,ps,cfg⟩ := prepareAt_cfg raw nonempty labels
  obtain ⟨ss0,ps0,origin,cfg0,provenance,injective,incoming⟩ := stock_prepared_incoming run scope raw cfg
  exact ⟨result,p,rf,af,ss,ps,ss0,ps0,origin,q,vb,label,run,scope,dominated,arity,raw,fallback,accepted,physical,
    cfg,cfg0,provenance,injective,incoming,critical,atNew,back,size⟩

end Backend.Stock.Proof.PreparedIncomingWitness
