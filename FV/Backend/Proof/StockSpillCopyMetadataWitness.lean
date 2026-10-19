import FV.Backend.Proof.PerEdgeSpillCycleFixture
import FV.Backend.Proof.StockSpillCopyMetadata
import FV.Backend.Proof.PerEdgeSpillEntryFixture

namespace Backend.Stock.Proof.SpillCopyMetadataWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgeSpill Backend.Proof.Spill
open Backend.Stock.Proof.IndexedSpillFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The complete checked cyclic Stock source instantiates prepared argument
and parameter metadata and the copy theorem with class/distinctness/slot/index
premises derived internally. Its actual synthetic jump copy swaps nonempty
home symbols and preserves every save cell; physical lowering succeeds. -/
theorem stock_spill_copy_metadata_witness :
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
  have sizes : (#[Reg.vreg 195 .int,Reg.vreg 194 .int] : Array Reg).size = tb.params.size := by rw [show tb.params = _ from params]; rfl
  have moves := stock_spillArgMovesAt_runs (c := c) (b := 3) (j := 0) (target := 1) (execution := 3) lowered scope dominated.ssa prepare
    (by change rf = spillAllocAt prepared.code prepared.edges; exact fallback) edgeRow (by rfl) atTarget atSource sizes stateSize
  refine ⟨result,prepared,rf,af,c,vb,tb,initial prepared,lowered,scope,dominated,prepare,checked,prepAccepted,fallback,accepted,physical,
    rfl,rfl,⟨succs,preds,cfg,rfl⟩,atSource,atTarget,installedCopy,argumentShape,parameterShape,spillHomesAt_spec _ _,slots,stateSize,?_⟩
  apply moves.mono
  intro k' a' ⟨same,size,values,frame⟩
  have first := values 0 (.vreg 195 .int) (.vreg 194 .int) rfl (by rw [show tb.params = _ from params]; rfl)
  have second := values 1 (.vreg 194 .int) (.vreg 195 .int) rfl (by rw [show tb.params = _ from params]; rfl)
  refine ⟨same,size,first.trans secondSymbol,second.trans firstSymbol,?_⟩
  intro r
  exact frame (.save r) (fun _ eq => by cases eq) (fun _ _ eq => by cases eq) (fun _ _ eq => by cases eq)

/-- Direct and indirect complete TryCall pipelines instantiate prepared copy
metadata for both real normal and handler rows carrying live results/payloads
and an ordinary argument, alongside actual checked fallback/physical lowering. -/
theorem stock_try_prepared_copy_metadata_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc),
      Stock.lower (SpillEntryFixture.function indirect) = .ok result ∧
      LowerScope (SpillEntryFixture.function indirect) ∧ Dominated (SpillEntryFixture.function indirect) ∧
      ArityOk (SpillEntryFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ prepareCheckedAt result.code result.edgeArgs = .ok p ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs p = true ∧
      (∀ (b j : Nat) (row : PerEdgePrep.EdgeRow) (args : Array Reg),
        p.edges[b]? = some row → row[j]? = some args → ArgumentShape args) ∧
      (∀ (b : Nat) (vb : VBlock),p.code.blocks[b]? = some vb → ParameterShape vb.params) ∧
      p.edges[0]? = some #[SpillEntryFixture.args indirect true,SpillEntryFixture.args indirect false] ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af := by
  obtain ⟨fixture⟩ := SpillEntryFixture.try_fixture indirect
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,metadata⟩
  obtain ⟨prepared,raw',checked,prepAccepted,args,params⟩ := stock_prepare_copy_metadata run scope dominated.ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst prepared
  have row := metadata.2.2.2.2.1
  exact ⟨result,p,rf,af,run,scope,dominated,arity,raw,checked,prepAccepted,args,params,row,fallback,accepted,physical⟩

end Backend.Stock.Proof.SpillCopyMetadataWitness
