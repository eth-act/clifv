import FV.E2E.PerEdgeSimulationS
import FV.Backend.Proof.StockPerEdgeAllocatorWitness

/-! Non-vacuity of `PerEdge.isSimulationS_match`: the actual checked indexed allocation of a real
Stock conditional with two nonempty per-successor vectors gives a block- and op-pinning
simulation over its per-successor code step, from the actual initial configurations. -/

namespace Backend.Proof.PerEdge

open Backend Backend.Stock

theorem simulationS_per_edge_witness : ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc),
    prepareAt result.code result.edgeArgs = .ok prepared ∧
    prepared.edges[0]? = some #[#[Reg.vreg 192 .int],#[Reg.vreg 192 .int]] ∧
    checkAllocAt prepared.code prepared.edges rf = .ok () ∧
    ∀ {V W : Type} (sem : ISem V W) (keep : Reg → V → V) (m : Loc → V) (ρ : Nat → V) (w : W),
      ∃ R,IsSimulationSBy prepared.code rf keep (VStepAt prepared.code prepared.edges sem) sem R ∧
        R (MConf.init rf m w) (VConf.init ρ w) := by
  obtain ⟨result,prepared,rf,af,_,_,_,prepare,vectors,_,_,checked,_,_,_⟩ :=
    Stock.Proof.PerEdgeAllocatorWitness.stock_per_edge_allocator_fallback_witness
  refine ⟨result,prepared,rf,prepare,vectors,checked,?_⟩
  intro V W sem keep m ρ w
  obtain ⟨c,ins,hc⟩ := checked_of_checkAlloc checked
  obtain ⟨a0,hat,hle⟩ := hc.at
  obtain ⟨simulates,initial⟩ := isSimulationS_match sem keep hat m ρ w (Inv_mono hle Inv_entryState)
  exact ⟨_,simulates,initial⟩

end Backend.Proof.PerEdge
