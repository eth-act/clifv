import FV.Backend.Proof.StockPreparedSharedRun
import FV.Backend.Proof.PerEdgeSpillSharedFixture
import FV.Backend.Proof.SpillArity

namespace Backend.Stock.Proof.PreparedSharedRunWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.IndexedSpillFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
private def available (v : Nat) : Bool := v == 194 || v == 195

/-- A complete original-scope/dominated loop runs its real synthetic allocated
block with two live cyclic arguments. The real checker edge renames the copied
symbols, establishes both loop parameter homes and saved entry values, and
contains the shared target's canonical checker input. Checked allocation and
physical lowering remain successful. -/
theorem stock_prepared_shared_jump_block_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx)
      (succs preds : Array (Array Nat)) (vb tb : VBlock) (out e : AState),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧ ArityOk function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      c.vc = p.code ∧ c.rf = rf ∧ c.succs = succs ∧ p.code.cfg = .ok (succs,preds) ∧
      p.code.blocks[3]? = some vb ∧ p.code.blocks[1]? = some tb ∧
      vb.insts = #[.jump 1] ∧ tb.params = #[.vreg 194 .int,.vreg 195 .int] ∧
      p.edges[3]? = some #[#[.vreg 195 .int,.vreg 194 .int]] ∧ preds[1]? = some #[0,3] ∧
      GoodAt p.code p.edges available (bodyStateAt p.code p.edges available) ∧
      c.runBlock 3 (bodyStateAt p.code p.edges available) = .ok out ∧
      EdgeTransferAt c p.edges 3 1 0 #[.vreg 195 .int,.vreg 194 .int] tb out e ∧
      GoodAt p.code p.edges available e ∧
      (preEntryStateAt p.code p.edges succs preds (fun _ => available) (fun _ => available) 1).le e = true := by
  obtain ⟨result,p,rf,af,tb,succs,preds,run,scope,dominated,raw,fallback,accepted,physical,cfg,
    successor,predecessors,targetBlock,copies,installed⟩ := SpillJumpWitness.stock_spill_jump_route_witness
  obtain ⟨fixture⟩ := cycle_fixture
  have sameResult := Except.ok.inj (run.symm.trans fixture.lowered)
  have sameP := Except.ok.inj (raw.symm.trans (sameResult ▸ fixture.prepare))
  have edgeRow : p.edges[3]? = some #[#[Reg.vreg 195 .int,Reg.vreg 194 .int]] := sameP ▸ fixture.edgeRow
  have count : p.code.blocks.size = 4 := sameP ▸ fixture.blockCount
  have sameTarget : p.code.blocks[1]! = tb := by rw [getElem!_def,targetBlock]
  have params : tb.params = #[.vreg 194 .int,.vreg 195 .int] := by
    have params := sameP ▸ fixture.params
    rw [sameTarget] at params
    exact params
  let vb := p.code.blocks[3]!
  have block : p.code.blocks[3]? = some vb := by
    have bound : 3 < p.code.blocks.size := by omega
    dsimp only [vb]; rw [getElem!_pos p.code.blocks 3 bound]
    exact Array.getElem?_eq_getElem bound
  have layout := SharedJumpFixture.shared_jump_layout run raw
  have instructions : vb.insts = #[.jump 1] := layout.1
  let c : CheckCtx := ⟨p.code,succs,rf,stateSizeAt p.code p.edges⟩
  have availability : EntryAvailAt p.code vb 0 #[.vreg 195 .int,.vreg 194 .int] tb available available := by
    constructor
    · intro i ar found
      have bound : i < 2 := (Array.getElem?_eq_some_iff.mp found).1
      have choices : i = 0 ∨ i = 1 := by omega
      rcases choices with rfl | rfl <;> cases found <;> exact .inl (by rfl)
    · intro i ar found present
      have bound : i < 2 := (Array.getElem?_eq_some_iff.mp found).1
      have choices : i = 0 ∨ i = 1 := by omega
      rcases choices with rfl | rfl
      · cases found; exact layout.2.2
      · cases found; exact layout.2.1
    · intro p' member present
      rw [params] at member
      simp only [Array.toList, List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact layout.2.1
      · exact layout.2.2
    · intro v wanted outside
      simp only [available,Bool.or_eq_true,beq_iff_eq] at wanted
      rcases wanted with rfl | rfl
      all_goals exact False.elim (outside (by rw [params]; simp [Reg.homeNum]))
  have initialGood := bodyStateAt_good p.code p.edges available
  have shared : 1 < preds[1]!.size := by rw [getElem!_def,predecessors]; decide
  obtain ⟨vb',atActual,exactJump,single,zero⟩ := stock_prepare_shared_jump_cfg run scope raw cfg
    (j := 0) successor rfl shared
  rw [block] at atActual
  cases atActual
  have targetLabel : p.code.blocks[1]!.label = 1 := by
    rw [instructions] at exactJump
    have same : MInst.jump 1 = .jump p.code.blocks[1]!.label := Option.some.inj exactJump
    simpa only [MInst.jump.injEq] using same.symm
  have route := stock_spill_prepared_shared_jump_runs run scope dominated.ssa raw (c := c) rfl fallback cfg
    (post := fun _ => available) (body := fun _ => available)
    (by decide : (1 : Nat) ≠ 0) block targetBlock successor (j := 0) rfl
    (by rw [predecessors]; decide) edgeRow (by rfl) availability initialGood
  simp only [instructions,Array.size_singleton,Nat.reduceSub,targetLabel] at route
  have shape : spillInstAt (spillHomesAt p.code p.edges) 0 (.jump 1) = [.op 0 #[]] := by
    unfold spillInstAt
    rw [show (MInst.jump 1).operands = .ok #[] from rfl]
    simp [spillLocs,MInst.clobbers,MInst.isTerminator,MInst.isBranch,MInst.keptDefs]
  rw [shape] at route
  have whole : Spill.Runs c vb 0 (jumpCopies p.code p.edges succs preds 3 ++ [.op 0 #[]])
      (bodyStateAt p.code p.edges available) (fun k out => k = vb.insts.size ∧
        ∃ e,EdgeTransferAt c p.edges 3 1 0 #[.vreg 195 .int,.vreg 194 .int] tb out e ∧
          GoodAt p.code p.edges available e ∧
          (preEntryStateAt p.code p.edges succs preds (fun _ => available) (fun _ => available) 1).le e = true) := by
    exact route.mono (fun k out result => ⟨result.1.trans (by rw [instructions]; rfl),result.2⟩)
  obtain ⟨out,checked,e,transfer,good,least⟩ := whole.run
  have blockRun : c.runBlock 3 (bodyStateAt p.code p.edges available) = .ok out := by
    unfold CheckCtx.runBlock
    dsimp only [c]
    rw [block,installed]
    simpa only [List.toList_toArray] using checked
  exact ⟨result,p,rf,af,c,succs,preds,vb,tb,out,e,run,scope,dominated,arityOk_of (by decide +kernel),raw,fallback,accepted,physical,
    rfl,rfl,rfl,cfg,block,targetBlock,instructions,params,edgeRow,predecessors,initialGood,blockRun,transfer,good,least⟩

end Backend.Stock.Proof.PreparedSharedRunWitness
