import FV.Concurrency.FrameDisj
import FV.Concurrency.CallLoadWitness

/-!
# Witness: the compiled `atomic_load` nested in its compiled caller (#473, (iv))

The caller `RC` of `CallLoadData` with a callee budget of `0x100` bytes (`RCK`), and the
compiled `atomic_load` entered by its `bl ld` at `sBC` keeping the caller's frame and kept
addresses (`RLy`, `G = RCK.FK`):

* `wfRCK`, `nested_LC` (`Nested RCK RLy`), `wfRLy` (its `gfree` by `Nested.gfree`);
* `chain_LC`: the two live activations form a `Chain`, every code word outside the outer region;
* `frames_LC`, **`slots_LC`**: `Chain.frame_disj` and `Chain.slot_not_F` on it.
-/

namespace Concurrency.FrameDisj.Witness

open Arm Backend Backend.Proof E2E CallSeg.WitnessC RealizeCompiled.WitnessL
open ArmAllocThread.Witness (act)

/-- The caller with a callee budget of `0x100` bytes. -/
def RCK : RL := { RC with K := 0x100 }

theorem stackRCK : StackAvail 0x100 RCK.af RCK.s0 := by
  have hs := spC
  have hfs : (act vcpC rfC).af.frameSize = 160 := hs.2.2.2.2.2.2.2.1
  refine ⟨⟨?_, fun a ha => ?_⟩, ArmAllocThread.Witness.probeBelow_le_small
    (show (act vcpC rfC).af.frameSize + 16 < 4096 by omega)⟩
  · show (act vcpC rfC).af.frameSize + 16 + 0x100 ≤ (E2E.spv RC.s0).toNat
    rw [spv_RC, hfs]; decide
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RC ha
    show (act vcpC rfC).af.frameSize + 16 + 0x100 ≤
      (a - (E2E.spv RC.s0 - BitVec.ofNat 64 ((act vcpC rfC).af.frameSize + 16 + 0x100))).toNat
    rw [spv_RC, hfs]
    have hj' : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    rw [show RC.base = 0x30000#64 from rfl] at hd
    generalize j = J at hj' hd
    bv_omega

theorem wfRCK : RCK.Wf where
  check := wfRC.check
  alloc := wfRC.alloc
  emit := wfRC.emit
  layout := wfRC.layout
  lm := wfRC.lm
  fit := wfRC.fit
  stack := stackRCK
  psF := wfRC.psF
  prog0 := wfRC.prog0
  gfree := fun a hG ⟨h1, _⟩ => by
    have := gL_ge hG
    rw [show E2E.spv RCK.s0 = 0x7000#64 from spv_RC] at h1
    simp only [BitVec.toNat_ofNat] at h1
    omega

/-- The callee entered by the caller's `bl ld`, keeping the caller's frame and kept addresses. -/
noncomputable def RLy : RL := { RLx sBC with G := RCK.FK }

theorem strel_sBC : ∃ m, StRel RC sBC m w₀C := by
  obtain ⟨-, m, -, -, -, hS, -⟩ := Classical.choose_spec prefixC
  exact ⟨m, hS⟩

theorem spv_RLy : E2E.spv RLy.s0 = 0x6F50#64 := by
  obtain ⟨m, hS⟩ := strel_sBC
  exact spv_enterL hS

theorem stackRLy : StackAvail RLy.K RLy.af RLy.s0 := by
  obtain ⟨m, hS⟩ := strel_sBC
  exact stackX hS

theorem nested_LC : Nested RCK RLy where
  sp_le := by
    rw [spv_RLy]
    show 0x6F50 ≤ (E2E.spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af)).toNat
    rw [spv_RC, spC.2.1]; decide
  fits := by
    rw [spv_RLy]
    show (E2E.spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af)).toNat +
      (frameDrop (act vcpL rfL).af + 0) ≤ 0x6F50 + 0x100
    rw [spv_RC, spC.2.1, spC.2.2.1]; decide
  keep := rfl

theorem wfRLy : RLy.Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, h9⟩ := factsL
  have := wf_gen (H := (act vcpL rfL).H) allocL h1 h2 h3 h4 h5 h6 h9 stackRLy
    (enterL_program sBC) (nested_LC.gfree wfRCK stackRLy)
  exact this

/-- The live activations `[RLy, RCK]` form a chain whose code words avoid the outer region. -/
theorem chain_LC : Chain [RLy, RCK] ∧ (∀ R ∈ [RLy, RCK], R.Wf) ∧
    ∀ R ∈ [RLy, RCK], ∀ a, CodeAddr R.s0 a → ¬ Region ([RLy, RCK].getLast (by simp)) a := by
  refine ⟨⟨nested_LC, trivial⟩, fun R hR => ?_, fun R hR a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact wfRLy
    · exact wfRCK
  · show ¬ StackBelow (frameDrop RC.af + 0x100) (E2E.spv RC.s0) a
    rw [spv_RC, spC.2.1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    have hs := spC
    rcases hR with rfl | rfl
    · obtain ⟨j, hj, hd⟩ := codeAddr_words (enterL_program sBC) ha
      have hj' : j < 0x4000 := by have := hs.2.2.2.1; omega
      unfold StackBelow
      generalize j = J at hj' hd
      bv_omega
    · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RC ha
      have hj' : j < 0x4000 := by have := hs.2.2.2.2.1; omega
      rw [show RC.base = 0x30000#64 from rfl] at hd
      unfold StackBelow
      generalize j = J at hj' hd
      bv_omega

/-- The frames of the callee and of the caller are disjoint. -/
theorem frames_LC : ∀ a, Frame RLy a → ¬ Frame RCK a := fun a ha =>
  Chain.frame_disj chain_LC.1 chain_LC.2.1 0 1 (by simp) (by simp) (by omega) a ha

/-- **The CLIF slots of both live activations are in the callee's world.** -/
theorem slots_LC : ∀ C ∈ [RLy, RCK], ∀ a, slotArea C a → ¬ RLy.F a := fun _ hC _ hs =>
  Chain.slot_not_F chain_LC.1 chain_LC.2.1 chain_LC.2.2 hC hs

end Concurrency.FrameDisj.Witness
