import FV.Backend.Proof.PerEdgeSpillRoutes
import FV.Backend.Proof.PerEdgeSpillCycleFixture
namespace Backend.Stock.Proof.SpillJumpWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgeSpill Backend.Proof.Spill
open Backend.Stock.Proof.IndexedSpillFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private def view : Except String Bool := do
  let result ← Stock.lower function
  let p ← prepareAt result.code result.edgeArgs
  pure (decide (p.code.cfg.toOption = some (#[#[1],#[3,2],#[],#[1]],#[#[],#[0,3],#[1],#[1]])))
private theorem observed : view.toOption = some true := by decide +kernel
/-- A complete checked cyclic Stock source inhabits the shared-target jump
route: the real synthetic edge has one successor, the loop target has two
predecessors, and its actual block contains the two-live-home cyclic copy. -/
theorem stock_spill_jump_route_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (tb : VBlock)
      (succs preds : Array (Array Nat)),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧
      lowerRFunc p.code rf = .ok af ∧ p.code.cfg = .ok (succs,preds) ∧
      succs[3]? = some #[1] ∧ preds[1]? = some #[0,3] ∧
      p.code.blocks[1]? = some tb ∧
      jumpCopies p.code p.edges succs preds 3 =
        spillArgMovesAt (spillHomesAt p.code p.edges) #[.vreg 195 .int,.vreg 194 .int] tb.params ∧
      rf.blocks[3]? = some ((jumpCopies p.code p.edges succs preds 3 ++ [RItem.op 0 #[]]).toArray) := by
  obtain ⟨f⟩ := cycle_fixture
  rcases f with ⟨result,p,rf,af,lowered,scope,dominated,prepare,fallback,accepted,physical,
    count,edgeRow,params,codeSize,installedCopy,first,second⟩
  have cfg := observed
  unfold view at cfg
  rw [lowered] at cfg
  simp only [bind,Except.bind] at cfg
  rw [prepare] at cfg
  simp only [bind,Except.bind,pure,Except.pure,Except.toOption,Option.some.injEq,decide_eq_true_eq] at cfg
  have actualCfg : p.code.cfg = .ok (#[#[1],#[3,2],#[],#[1]],#[#[],#[0,3],#[1],#[1]]) := by
    cases actual : p.code.cfg <;> simp_all [Except.toOption]
  let succs : Array (Array Nat) := #[#[1],#[3,2],#[],#[1]]
  let preds : Array (Array Nat) := #[#[],#[0,3],#[1],#[1]]
  let tb := p.code.blocks[1]!
  have atTarget : p.code.blocks[1]? = some tb := by
    have bound : 1 < p.code.blocks.size := by omega
    dsimp only [tb]; rw [getElem!_pos p.code.blocks 1 bound]
    exact Array.getElem?_eq_getElem bound
  have route := spill_jump_route (vc := p.code) (edges := p.edges)
    (succs := succs) (preds := preds) (b := 3) (s := 1) (by rfl) (by decide +kernel)
    atTarget edgeRow (by rfl)
  exact ⟨result,p,rf,af,tb,succs,preds,lowered,scope,dominated,prepare,fallback,accepted,physical,actualCfg,
    rfl,rfl,atTarget,route,by rw [route]; exact installedCopy⟩

end Backend.Stock.Proof.SpillJumpWitness
