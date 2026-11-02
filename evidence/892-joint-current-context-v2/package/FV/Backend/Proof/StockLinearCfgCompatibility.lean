import FV.Backend.Proof.StockLinearCfgShape
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockOutgoingVectors
import FV.Backend.Proof.PerEdgeLegacyCompatible

namespace Backend.Stock.Proof.LinearCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Both actual single-successor rows retain the vectors consumed by the
existing compiler, checker, linker and generated-proof domain. -/
theorem legacy_compatible {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {entry middle target : Clif.Block} {first second : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (ret : target.term = .ret xs)
    (firstDestination : first.block = middle.id) (secondDestination : second.block = target.id)
    (entryMiddle : entry.id ≠ middle.id) (entryTarget : entry.id ≠ target.id)
    (middleTarget : middle.id ≠ target.id) : EdgeLegacyCompatible result.code result.edgeArgs := by
  have order : result.order = ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (block_order_three blocks firstJump secondJump ret
      firstDestination secondDestination entryMiddle entryTarget middleTarget))
  have source : f.blocks[0]? = some entry := by simp [blocks]
  have middleSource : f.blocks[1]? = some middle := by simp [blocks]
  have entryTag : result.order.nodes[0]? = some (.original 0) := by simp [order]
  have middleTag : result.order.nodes[1]? = some (.original 1) := by simp [order]
  have targetTag : result.order.nodes[2]? = some (.original 2) := by simp [order]
  obtain ⟨ev,ep,el,ea⟩ := stock_lower_original_jump_args run scope entryTag source firstJump
    (by simp [order] : result.order.successors[0]! = #[1]) middleTag
  obtain ⟨mv,mp,ml,ma⟩ := stock_lower_original_jump_args run scope middleTag middleSource secondJump
    (by simp [order] : result.order.successors[1]! = #[2]) targetTag
  have eVector := stock_lower_selected_outgoing run scope entryTag source
    (bc := first) (index := 0) (by simp [firstJump,dests]) (by simp [order]) middleTag
  have mVector := stock_lower_selected_outgoing run scope middleTag middleSource
    (bc := second) (index := 0) (by simp [secondJump,dests]) (by simp [order]) targetTag
  obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
  intro b index selected successor
  have onlyEdges : (b = 0 ∧ index = 0 ∧ selected = 1) ∨ (b = 1 ∧ index = 0 ∧ selected = 2) := by
    cases b with
    | zero =>
      cases index with
      | zero => exact Or.inl ⟨rfl,rfl,by simpa [succOf,cfg,order] using successor.symm⟩
      | succ index => simp [succOf,cfg,order] at successor
    | succ b =>
      cases b with
      | zero =>
        cases index with
        | zero => exact Or.inr ⟨rfl,rfl,by simpa [succOf,cfg,order] using successor.symm⟩
        | succ index => simp [succOf,cfg,order] at successor
      | succ b =>
        cases b with
        | zero => simp [succOf,cfg,order] at successor
        | succ b => simp [succOf,cfg,order] at successor
  rcases onlyEdges with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ⟨ev,ep,by simpa only [outgoingAt,ea] using eVector⟩
  · exact ⟨mv,mp,by simpa only [outgoingAt,ma] using mVector⟩

end Backend.Stock.Proof.LinearCfg
