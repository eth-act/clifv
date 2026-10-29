module

public import FV.Concurrency.CallEntryRel
public import FV.Concurrency.CallSegCallWitness
public import FV.Concurrency.CallEnterArmWitness

@[expose] public section

/-!
# Witnesses for `CallEntryRel` (#473)

On the link of the compiled caller and the compiled `atomic_load` (`LinkedMachine.Witness.link2`),
the caller with a callee budget of `0x100` bytes (`CallSegCall.Witness.RA2`) at its `bl ld`
(`sBF`), `atomic_load` entered with a budget of `0x10` bytes:

* `wf_ld`: the callee's activation is `Wf` (`act_wf`);
* `callee_relW_ld`: `callee_relW` from a CLIF memory with the slot-placement oracle at the
  caller's body `sp` (and no allocation): the callee's entry memory relation;
* `enterSlots_at_ld`: `enterSlots_at` for that memory.

`fL`'s slots are checked by `native_decide` (witness only).
-/

namespace Concurrency.CallEntryRel.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  AllocThread ArmAllocThread IselThread ThreadRefine E2E IselCall IselCallRet CallRetsEnd
  LinkedMachine LinkedMachine.Link LinkedMachine.Witness CallSeg.WitnessC CallEntry.Witness
  CallResumeL.Witness RealizeCompiled.WitnessL FrameDisj FrameDisj.Witness CallSegCall
  CallSegCall.Witness

/-- The callee's activation is well formed. -/
theorem wf_ld : (link2.act ldF (enter ldF sBF) 0x10 RA2.FK).Wf :=
  act_wf static_ld stack_ld (enter_program ldF sBF) gfree_ld

/-- The oracle's frames: every function as `atomic_load`. -/
def frL : String → Option (Nat × (Clif.SlotId → Nat)) :=
  fun _ => some (frameDrop ldF.af, slotOffs ldF.af fL)

/-- A CLIF memory with the oracle at the caller's body `sp`. -/
noncomputable def cmL : Clif.Mem := { place := some ⟨[spv sBF], frL, none⟩ }

theorem slots_fL : fL.slots = [] := by native_decide -- witness: native_decide

/-- **Non-vacuity of `enterSlots_at`.** -/
theorem enterSlots_at_ld : (Clif.enterSlots fL cmL).2.place =
    some ⟨(spv sBF - BitVec.ofNat 64 (frameDrop ldF.af)) :: [spv sBF], frL, none⟩ :=
  (enterSlots_at (f := fL) (mem := cmL) (sps := []) rfl rfl).2.2.2.2

/-- **Non-vacuity of `callee_relW`.** -/
theorem callee_relW_ld :
    RelW ⟨(link2.act ldF (enter ldF sBF) 0x10 RA2.FK).F, fun _ => none, ldF.af.slotBase, 0⟩ fL
      (spv (bodyOf ldF.af (enter ldF sBF))) (Clif.enterSlots fL cmL).1 (Clif.enterSlots fL cmL).2
      (bodyOf ldF.af (enter ldF sBF)) := by
  obtain ⟨m, hS⟩ := strel_sBF
  have hmr : MemRel RA2.F (fun _ => none) cmL sBF :=
    ⟨fun a b hv _ => by simp [cmL, Clif.Mem.valid] at hv,
      fun a n hv => by simp [cmL, Clif.Mem.valid] at hv, rfl⟩
  exact callee_relW wf_RA2 codeIn_RA2 CallSegCall.Witness.mem_ld wf_ld nested_ld hmr
    (fun _ _ => rfl) hS.err
    (sps := []) rfl rfl (by rw [slots_fL]; intro q hq; cases hq)

end Concurrency.CallEntryRel.Witness
