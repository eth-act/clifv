import FV.E2E.RegLevelForward2By
import FV.E2E.PerEdgeSimulationSWitness

/-! Non-vacuity of `forward2By_perEdge`: the actual checked indexed allocation of a real Stock
conditional with two nonempty per-successor vectors gives, for any two semantics, the two
per-successor simulations its premises need; with the trivial joint realization the lemma applies
from the actual initial configurations. -/

namespace Backend.Proof.PerEdge

open Backend Backend.Stock

theorem forward2By_per_edge_witness : ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc),
    prepareAt result.code result.edgeArgs = .ok prepared ∧
    checkAllocAt prepared.code prepared.edges rf = .ok () ∧
    ∀ {V W : Type} (sem sem' : ISem V W) (keep : Reg → V → V) (m : Loc → V) (ρ : Nat → V) (w : W),
      ∃ R R',IsSimulationSBy prepared.code rf keep (VStepAt prepared.code prepared.edges sem) sem R ∧
        IsSimulationSBy prepared.code rf keep (VStepAt prepared.code prepared.edges sem') sem' R' ∧
        ∃ (n : Nat) (d d' : MConf V W),R d (VConf.init ρ w) ∧ R' d' (VConf.init ρ w) := by
  obtain ⟨result,prepared,rf,af,_,_,_,prepare,_,_,_,checked,_,_,_⟩ :=
    Stock.Proof.PerEdgeAllocatorWitness.stock_per_edge_allocator_fallback_witness
  refine ⟨result,prepared,rf,prepare,checked,?_⟩
  intro V W sem sem' keep m ρ w
  obtain ⟨c,ins,hc⟩ := checked_of_checkAlloc checked
  obtain ⟨a0,hat,hle⟩ := hc.at
  obtain ⟨simulates,initial⟩ := isSimulationS_match sem keep hat m ρ w (Inv_mono hle Inv_entryState)
  obtain ⟨simulates',initial'⟩ := isSimulationS_match sem' keep hat m ρ w (Inv_mono hle Inv_entryState)
  have realizes : RealizesJ prepared.code rf sem sem' keep (id : Unit → Unit) id (fun _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ => True) := by
    intro s c s' c' d d' _ hd hd' _
    exact ⟨0,d,d',hd,hd',trivial,fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨n,d,d',_,hr,hr',_,_⟩ := forward2By_perEdge (edges := prepared.edges) simulates simulates'
    (PI := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) realizes (Star.refl _) initial initial' trivial
    ⟨rfl,rfl⟩ (s := ()) (s' := ()) trivial
  exact ⟨_,_,simulates,simulates',n,d,d',hr,hr'⟩

end Backend.Proof.PerEdge
