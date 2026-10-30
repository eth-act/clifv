import FV.Backend.Proof.StockOutgoingVectors
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockTwoBlockShape
import FV.Backend.Proof.PerEdgeLegacyCompatible

namespace Backend.Stock.Proof.TwoBlock
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual argument collection/assembly makes this direct two-block class
compatible with existing consumers, including nonempty successor parameters.
No equality between independently chosen compiler cores is assumed. -/
theorem legacy_compatible {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {entry target : Clif.Block} {bc : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,target]) (jump : entry.term = .jump bc) (ret : target.term = .ret xs)
    (destination : bc.block = target.id) (different : entry.id ≠ target.id) :
    EdgeLegacyCompatible result.code result.edgeArgs := by
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (block_order blocks jump ret destination different))
  have source : f.blocks[0]? = some entry := by rw [blocks]; rfl
  have tag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
  have targetTag : result.order.nodes[1]? = some (.original 1) := by rw [order]; rfl
  have row : result.order.successors[0]! = #[1] := by rw [order]; rfl
  obtain ⟨vb,placed,label,args⟩ := stock_lower_original_jump_args run scope tag source jump row targetTag
  have vector := stock_lower_selected_outgoing run scope tag source
    (bc := bc) (index := 0) (by simp [jump,dests]) (by rw [order]; rfl) targetTag
  obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
  intro b index selected successor
  have onlyEdge : b = 0 ∧ index = 0 ∧ selected = 1 := by
    cases b with
    | zero =>
      cases index with
      | zero => simpa [succOf,cfg,order] using successor.symm
      | succ index => simp [succOf,cfg,order] at successor
    | succ b =>
      cases b with
      | zero => simp [succOf,cfg,order] at successor
      | succ b => simp [succOf,cfg,order] at successor
  obtain ⟨rfl,rfl,rfl⟩ := onlyEdge
  exact ⟨vb,placed,by simpa only [outgoingAt,args] using vector⟩

end Backend.Stock.Proof.TwoBlock
