import FV.Backend.Proof.RegallocSimulationBy
import FV.Backend.Proof.StockPerEdgeAllocatorWitness

/-! Non-vacuity of `IsSimulationBy`: the actual checked indexed allocation of a real Stock
conditional with two nonempty per-successor vectors gives a step-parametric simulation over its
per-successor code step, from the actual initial configurations. -/

namespace Backend.Proof

open Backend Backend.Stock

theorem simulationBy_per_edge_witness : ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc),
    prepareAt result.code result.edgeArgs = .ok prepared ∧
    prepared.edges[0]? = some #[#[Reg.vreg 192 .int],#[Reg.vreg 192 .int]] ∧
    checkAllocAt prepared.code prepared.edges rf = .ok () ∧
    ∀ {V W : Type} (sem : ISem V W) (keep : Reg → V → V) (m : Loc → V) (ρ : Nat → V) (w : W),
      ∃ R,IsSimulationBy prepared.code rf sem keep (VStepAt prepared.code prepared.edges sem) R ∧
        R (MConf.init rf m w) (VConf.init ρ w) := by
  obtain ⟨result,prepared,rf,af,_,_,_,prepare,vectors,_,_,checked,_,_,simulation⟩ :=
    Stock.Proof.PerEdgeAllocatorWitness.stock_per_edge_allocator_fallback_witness
  refine ⟨result,prepared,rf,prepare,vectors,checked,?_⟩
  intro V W sem keep m ρ w
  obtain ⟨R,simulates,initial,_⟩ := simulation sem keep m ρ w
  exact ⟨R,simulates.toBy,initial⟩

end Backend.Proof
