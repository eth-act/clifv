import FV.Backend.Proof.PerEdgePrepareWitness
import FV.Backend.Proof.StockPreparedArity
import FV.Backend.Proof.PerEdgeSpillEntryFixture
import FV.Backend.Proof.PerEdgeSpillJumpWitness

namespace Backend.Stock.Proof.PreparedArityWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.IndexedSpillFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def inputCode {vc : VCode} {edges : Array PerEdgePrep.EdgeRow} {p : EdgeVCode}
    (_ : prepareAt vc edges = .ok p) : VCode := vc
private def inputEdges {vc : VCode} {edges : Array PerEdgePrep.EdgeRow} {p : EdgeVCode}
    (_ : prepareAt vc edges = .ok p) : Array PerEdgePrep.EdgeRow := edges

/-- The real generic split/filter/RPO fixture inhabits output reachability,
both segments of a newly split nonempty edge, and global prepared arity. -/
theorem generic_prepared_arity_witness :
    ∃ (vc : VCode) (edges : Array PerEdgePrep.EdgeRow) (p : EdgeVCode)
      (ss0 ps0 ss3 ps3 : Array (Array Nat)) (q target : Nat),
      prepareAt vc edges = .ok p ∧ vc.blocks.size = 5 ∧
      p.code.blocks.map (·.label) = #[10,31,20,30] ∧
      vc.cfg = .ok (ss0,ps0) ∧ p.code.cfg = .ok (ss3,ps3) ∧
      EdgeArityAt vc edges ss0 ∧ EdgeArityAt p.code p.edges ss3 ∧
      (∀ b,b < p.code.blocks.size → Prep.Reach ss3 b) ∧
      (∀ b,b ∈ (rpo ss0).toList → Prep.Reach ss0 b) ∧
      sigmaOf vc p.code 0 = some q ∧ sigmaOf vc p.code 2 = some target ∧
      PerEdgePrep.RoutedEdgeArity p ss3 q 1 target #[.vreg 194 .int] ∧
      p.edges[0]? = some #[#[Reg.vreg 192 .int],#[]] ∧
      p.edges[1]? = some #[#[Reg.vreg 194 .int]] := by
  obtain ⟨p,run,labels,rest⟩ := PerEdgePrepareWitness.per_edge_prepare_split_copy_witness (fun _ => 0)
  let vc := inputCode run
  let edges := inputEdges run
  have domain : Prep.Lbls vc.blocks := by dsimp only [vc,inputCode]; unfold Prep.Lbls; decide +kernel
  obtain ⟨_,ss0,ps0,cfg0,_⟩ := PerEdgePrep.prepareAt_input_facts run
  obtain ⟨_,ss3,ps3,cfg3⟩ := PerEdgePrep.prepareAt_cfg run (by decide +kernel) domain
  have cfg0Exact : ss0 = #[#[1,2],#[2],#[],#[4],#[]] := by
    have actual : vc.cfg = Except.ok (#[#[1,2],#[2],#[],#[4],#[]],#[#[],#[0],#[0,1],#[],#[3]]) := by dsimp only [vc,inputCode]; cbv
    exact congrArg Prod.fst (Except.ok.inj (cfg0.symm.trans actual))
  subst ss0
  have originalArity : EdgeArityAt vc edges #[#[1,2],#[2],#[],#[4],#[]] := by
    intro b j target ss row args tb atSuccs edge atRow atArgs atTarget
    have bBound : b < 5 := (Array.getElem?_eq_some_iff.mp atSuccs).1
    have choices : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl
    all_goals cases atSuccs
    all_goals have jBound := (Array.getElem?_eq_some_iff.mp edge).1
    all_goals first | change j < 2 at jBound | change j < 1 at jBound | change j < 0 at jBound
    all_goals try omega
    all_goals have choices : j = 0 ∨ j = 1 := by omega
    all_goals rcases choices with rfl | rfl
    all_goals cases edge
    all_goals cases atRow
    all_goals cases atArgs
    all_goals cases atTarget
    all_goals rfl
  have allArity := PerEdgePrep.prepareAt_edge_arity run (by decide +kernel) domain cfg0 originalArity cfg3
  have allReach := PerEdgePrep.prepareAt_all_reachable run (by decide +kernel) domain cfg3
  have cs0 := Prep.cfg_spec cfg0
  have live := (Prep.reachable_spec (Prep.succsIn_of cs0) (by decide +kernel)).2.1
  obtain ⟨ssB,psB,q,target,cfgB,sigma,targetSigma,route⟩ := PerEdgePrep.prepareAt_routed_edge_arity run
    (by decide +kernel) domain cfg0 originalArity live (b := 0) (j := 1) (target := 2)
    (by rfl) (by rfl) (by rfl) (by rfl)
  rw [cfg3] at cfgB
  cases cfgB
  have rows : p.edges[0]? = some #[#[Reg.vreg 192 .int],#[]] ∧ p.edges[1]? = some #[#[Reg.vreg 194 .int]] := by
    rcases rest with ⟨_,_,emptyCopy,realCopy⟩
    -- Recover the actual indexed vectors from the same successful executable fixture.
    have observed : (prepareAt vc edges).toOption.map (fun p => decide (
        p.edges[0]? = some #[#[Reg.vreg 192 .int],#[]] ∧ p.edges[1]? = some #[#[Reg.vreg 194 .int]])) = some true := by dsimp only [vc,edges,inputCode,inputEdges]; decide +kernel
    change (prepareAt (inputCode run) (inputEdges run)).toOption.map _ = _ at observed
    dsimp only [inputCode,inputEdges] at observed
    rw [run] at observed
    simpa only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] using observed
  exact ⟨_,_,p,_,_,ss3,ps3,q,target,run,rfl,labels,cfg0,cfg3,originalArity,allArity,allReach,
    fun b hb => Prep.rpo_selected_reachable _ b hb,sigma,targetSigma,route,rows.1,rows.2⟩

/-- The complete checked cyclic Stock source instantiates prepared argument
and parameter metadata and the copy theorem with class/distinctness/slot/index
premises derived internally. Its actual synthetic jump copy swaps nonempty
home symbols and preserves every save cell; physical lowering succeeds. -/
theorem stock_prepared_cyclic_copy_arity_witness :
    ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx)
      (vb tb : VBlock) (a0 : AState),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true ∧
      rf = spillAllocAt prepared.code prepared.edges ∧ checkAllocAt prepared.code prepared.edges rf = .ok () ∧
      lowerRFunc prepared.code rf = .ok af ∧
      c.vc = prepared.code ∧ c.rf = rf ∧
      (∃ succs preds,prepared.code.cfg = .ok (succs,preds) ∧ c.succs = succs) ∧
      prepared.code.blocks[3]? = some vb ∧ prepared.code.blocks[1]? = some tb ∧
      rf.blocks[3]? = some ((spillArgMovesAt (spillHomesAt prepared.code prepared.edges)
        #[.vreg 195 .int,.vreg 194 .int] tb.params ++ [RItem.op 0 #[]]).toArray) ∧
      (∀ (b j : Nat) (row : PerEdgePrep.EdgeRow) (args : Array Reg),
        prepared.edges[b]? = some row → row[j]? = some args → ArgumentShape args) ∧
      (∀ (b : Nat) (vb : VBlock),prepared.code.blocks[b]? = some vb → ParameterShape vb.params) ∧
      (∀ ss ps,prepared.code.cfg = .ok (ss,ps) → EdgeArityAt prepared.code prepared.edges ss) ∧
      HomesSpec prepared.code prepared.edges ∧
      rf.spillSlots = (spillHomesAt prepared.code prepared.edges).size + maxArgsAt prepared.edges ∧
      a0.size = stateSizeAt prepared.code prepared.edges ∧
      Runs c vb 0 (spillArgMovesAt (spillHomesAt prepared.code prepared.edges)
        #[.vreg 195 .int,.vreg 194 .int] tb.params) a0 (fun k' a' =>
          k' = 0 ∧ a'.size = stateSizeAt prepared.code prepared.edges ∧
          a'.get (spillHomeAt (spillHomesAt prepared.code prepared.edges) 194 .int) = [.vreg 195] ∧
          a'.get (spillHomeAt (spillHomesAt prepared.code prepared.edges) 195 .int) = [.vreg 194] ∧
          ∀ r,a'.get (.save r) = a0.get (.save r)) := by
  obtain ⟨fixture⟩ := IndexedSpillFixture.cycle_fixture
  rcases fixture with ⟨result,prepared,rf,af,lowered,scope,dominated,prepare,fallback,accepted,physical,
    blockCount,edgeRow,params,codeSize,installedCopy,firstSymbol,secondSymbol⟩
  obtain ⟨p,raw,checked,prepAccepted,argumentShape,parameterShape⟩ := stock_prepare_copy_metadata lowered scope dominated.ssa
  have samePrepared := Except.ok.inj (prepare.symm.trans raw)
  subst p
  have header := accepted
  unfold checkAllocAt at header
  obtain ⟨⟨succs,preds⟩,cfg,_⟩ := Except.bind_ok header
  let c : CheckCtx := ⟨prepared.code,succs,rf,stateSizeAt prepared.code prepared.edges⟩
  let vb := prepared.code.blocks[3]!
  let tb := prepared.code.blocks[1]!
  have atSource : prepared.code.blocks[3]? = some vb := by
    have bound : 3 < prepared.code.blocks.size := by omega
    dsimp only [vb]
    rw [getElem!_pos prepared.code.blocks 3 bound]
    exact Array.getElem?_eq_getElem bound
  have atTarget : prepared.code.blocks[1]? = some tb := by
    have bound : 1 < prepared.code.blocks.size := by omega
    dsimp only [tb]
    rw [getElem!_pos prepared.code.blocks 1 bound]
    exact Array.getElem?_eq_getElem bound
  have slots : c.rf.spillSlots = (spillHomesAt prepared.code prepared.edges).size + maxArgsAt prepared.edges := by
    rw [show c.rf = rf from rfl,fallback]
    exact (spillAllocAt_storage _ _).1
  have stateSize : (initial prepared).size = stateSizeAt prepared.code prepared.edges := by
    simp only [initial,size_put,Array.size_replicate]
  obtain ⟨r,p2,rf2,af2,otherTarget,ss2,ps2,run2,_,_,raw2,_,_,_,cfg2,successors,rest⟩ :=
    SpillJumpWitness.stock_spill_jump_route_witness
  have sameResult := Except.ok.inj (lowered.symm.trans run2)
  subst r
  have sameOutput := Except.ok.inj (prepare.symm.trans raw2)
  subst p2
  have moves := stock_spillArgMovesAt_edge_runs (c := c) (b := 3) (j := 0) (target := 1) (execution := 3) lowered scope dominated.ssa prepare
    (by change rf = spillAllocAt prepared.code prepared.edges; exact fallback) cfg2 successors (by rfl) edgeRow (by rfl) atTarget atSource stateSize
  refine ⟨result,prepared,rf,af,c,vb,tb,initial prepared,lowered,scope,dominated,prepare,checked,prepAccepted,fallback,accepted,physical,
    rfl,rfl,⟨succs,preds,cfg,rfl⟩,atSource,atTarget,installedCopy,argumentShape,parameterShape,stock_prepare_edge_arity lowered scope dominated.ssa prepare,spillHomesAt_spec _ _,slots,stateSize,?_⟩
  apply moves.mono
  intro k' a' ⟨same,size,values,frame⟩
  have first := values 0 (.vreg 195 .int) (.vreg 194 .int) rfl (by rw [show tb.params = _ from params]; rfl)
  have second := values 1 (.vreg 194 .int) (.vreg 195 .int) rfl (by rw [show tb.params = _ from params]; rfl)
  refine ⟨same,size,first.trans secondSymbol,second.trans firstSymbol,?_⟩
  intro r
  exact frame (.save r) (fun _ eq => by cases eq) (fun _ _ eq => by cases eq) (fun _ _ eq => by cases eq)

/-- All four complete direct/indirect normal/handler Stock pipelines inhabit
prepared global arity and the actual selected result/payload/ordinary vector's
parameter count, retaining checked fallback and successful physical lowering. -/
theorem stock_prepared_try_arity_witness (indirect handler : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (tb : VBlock)
      (ss ps : Array (Array Nat)),
      Stock.lower (SpillEntryFixture.function indirect) = .ok result ∧
      LowerScope (SpillEntryFixture.function indirect) ∧ Dominated (SpillEntryFixture.function indirect) ∧
      ArityOk (SpillEntryFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ prepareCheckedAt result.code result.edgeArgs = .ok p ∧
      p.code.cfg = .ok (ss,ps) ∧ EdgeArityAt p.code p.edges ss ∧
      (∀ b,b < p.code.blocks.size → Prep.Reach ss b) ∧
      p.edges[0]? = some #[SpillEntryFixture.args indirect true,SpillEntryFixture.args indirect false] ∧
      p.code.blocks[SpillEntryFixture.target handler]? = some tb ∧
      (SpillEntryFixture.args indirect handler).size = tb.params.size ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af := by
  obtain ⟨fixture⟩ := SpillEntryFixture.try_fixture indirect
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,metadata⟩
  obtain ⟨count,atLast,normalParams,handlerParams,edgeRow,cfgOption,rest⟩ := metadata
  have cfg : p.code.cfg = .ok (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]) := by
    cases actual : p.code.cfg <;> simp_all [Except.toOption]
  let tb := p.code.blocks[SpillEntryFixture.target handler]!
  have atTarget : p.code.blocks[SpillEntryFixture.target handler]? = some tb := by
    have bound : SpillEntryFixture.target handler < p.code.blocks.size := by cases handler <;> simp [SpillEntryFixture.target] <;> omega
    dsimp only [tb]
    rw [getElem!_pos p.code.blocks _ bound]
    exact Array.getElem?_eq_getElem bound
  have allArity := stock_prepare_edge_arity run scope dominated.ssa raw _ _ cfg
  have selected : (#[2,1] : Array Nat)[SpillEntryFixture.index handler]? = some (SpillEntryFixture.target handler) := by cases handler <;> rfl
  have argsAt : (#[SpillEntryFixture.args indirect true,SpillEntryFixture.args indirect false] : Array (Array Reg))[SpillEntryFixture.index handler]? =
      some (SpillEntryFixture.args indirect handler) := by cases handler <;> rfl
  have exactCount := allArity 0 (SpillEntryFixture.index handler) (SpillEntryFixture.target handler) _ _ _ tb rfl selected edgeRow argsAt atTarget
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  exact ⟨result,p,rf,af,tb,_,_,run,scope,dominated,arity,raw,stock_prepareCheckedAt_complete run scope raw,cfg,allArity,
    PerEdgePrep.prepareAt_all_reachable raw nonempty labels cfg,edgeRow,atTarget,exactCount,fallback,accepted,physical⟩

end Backend.Stock.Proof.PreparedArityWitness
