import FV.Backend.Proof.LowerOutcomes
namespace Backend.Proof.Driver
open Backend Backend.Proof
variable {ctx : Ctx}

/-- DFG consistency only depends on the frame's function, slots and registers. -/
theorem dfgCons_congr {fr fr' : Clif.Frame} (hf : fr'.func = fr.func) (hs : fr'.slots = fr.slots)
    (hr : fr'.regs = fr.regs) (h : DFGCons ctx fr) : DFGCons ctx fr' := by
  refine ⟨fun x j info cl v hd hi hc hp hv => ?_, fun x t v ht hv => h.2 x t v ht (hr ▸ hv)⟩
  obtain ⟨vals, hev, hlk⟩ := h.1 x j info cl v hd hi hc hp (hr ▸ hv)
  exact ⟨vals, fun cm => by rw [evalInst_congr hf hs cm cl (fun y _ => by rw [hr])]; exact hev cm,
    hlk⟩

theorem loadVal_congr {F : BitVec 64 → Prop} {s t : Arm.ArmState} (op : LoadOp) {a : BitVec 64}
    (h : ∀ x, ¬ F x → s.mem x = t.mem x) (hav : Avoids F op.bytes a) :
    loadVal op a s = loadVal op a t := by
  have hr : Arm.read_mem_bytes op.bytes a s = Arm.read_mem_bytes op.bytes a t :=
    read_mem_bytes_congr _ a (fun k hk => h _ (hav k hk))
  simp only [loadVal, hr]
end Backend.Proof.Driver
