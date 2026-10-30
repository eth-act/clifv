import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.StockCfgTotal
import FV.Backend.Proof.PerEdgeSpillCycleFixture

namespace Backend.Stock.Proof.IndexedSpillWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgeSpill Backend.Proof.Spill
open Backend.Stock.Proof.IndexedSpillFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A complete accepted cyclic Stock program executes raw preparation, the
actual checked indexed fallback and physical lowering. Its real synthetic-edge
copy swaps two live home contents and frames every save location; all four
universal home/storage/copy roots are instantiated on that actual allocation. -/
theorem stock_indexed_spill_cycle_witness :
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
  have prepFacts : prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
    obtain ⟨p,raw,checked,accepted⟩ := stock_prepare_total lowered scope
    have same := Except.ok.inj (prepare.symm.trans raw)
    subst p
    exact ⟨checked,accepted⟩
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
  have classes : ∀ (i : Nat) (a p : Reg),
      (#[Reg.vreg 195 .int,Reg.vreg 194 .int] : Array Reg)[i]? = some a → tb.params[i]? = some p →
      ∃ v w cl,a = .vreg v cl ∧ p = .vreg w cl := by
    intro i a p left right
    rw [show tb.params = _ from params] at right
    have bound : i < 2 := by have h := (Array.getElem?_eq_some_iff.mp left).1; exact h
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    all_goals cases left; cases right; exact ⟨_,_,.int,rfl,rfl⟩
  have distinct : (tb.params.toList.map Reg.homeNum).Nodup := by rw [show tb.params = _ from params]; decide +kernel
  have moves := spillArgMovesAt_runs (vc := prepared.code) (edges := prepared.edges) (c := c)
    (b := 3) (j := 0) (target := 1) slots edgeRow (by rfl) atTarget sizes classes distinct
    (vb := vb) (k := 0) (by change 0 ≠ (prepared.code.blocks[3]!).insts.size; rw [codeSize]; decide) stateSize
  refine ⟨result,prepared,rf,af,c,vb,tb,initial prepared,lowered,scope,dominated,prepare,prepFacts.1,prepFacts.2,fallback,accepted,physical,
    rfl,rfl,⟨succs,preds,cfg,rfl⟩,atSource,atTarget,installedCopy,spillHomesAt_spec _ _,slots,stateSize,?_⟩
  apply moves.mono
  intro k' a' ⟨same,size,values,frame⟩
  have first := values 0 (.vreg 195 .int) (.vreg 194 .int) rfl (by rw [show tb.params = _ from params]; rfl)
  have second := values 1 (.vreg 194 .int) (.vreg 195 .int) rfl (by rw [show tb.params = _ from params]; rfl)
  refine ⟨same,size,first.trans secondSymbol,second.trans firstSymbol,?_⟩
  intro r
  exact frame (.save r) (fun _ eq => by cases eq) (fun _ _ eq => by cases eq) (fun _ _ eq => by cases eq)

end Backend.Stock.Proof.IndexedSpillWitness
