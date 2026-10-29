module

public import FV.Backend.Proof.RegallocOperands

@[expose] public section

/-!
# A memory region overwritten by a prophecy (SEM1 step 2, `docs/plans/uninit.md` §5.4)

The prophecy call contract runs a callee canonically from the VCode world `w` with its stack
region (dead addresses below the caller's `sp`, inside the caller's mask `F`) holding the actual
machine bytes `P` there at the call. `overlay R P s`: `s` with the bytes `P` at the addresses `R`.

* `r_overlay`, `program_overlay`, `mem_overlay`, `mem_overlay_in`, `mem_overlay_out`: only the
  memory at `R` changes;
* `sameWorld_overlay`, `SameWorld.overlay`: with `R ⊆ F`, the overlay is the same world modulo
  `F` (as its source, and of two such worlds);
* `overlay_eq_self`: a state whose bytes at `R` are `P` is its own overlay (the actual run at the
  call, where `P` is by definition its memory there);
* `overlay_mem_eq`: two overlays agree on `R`.
-/

namespace Backend.Proof

open Classical in
/-- `s` with the bytes `P a` at the addresses `a` of `R`. -/
noncomputable def overlay (R : BitVec 64 → Prop) (P : BitVec 64 → BitVec 8) (s : Arm.ArmState) :
    Arm.ArmState :=
  { s with mem := fun a => if R a then P a else s.mem a }

section
variable {R : BitVec 64 → Prop} {P : BitVec 64 → BitVec 8}

theorem r_overlay (f : Arm.StateField) (s : Arm.ArmState) : Arm.r f (overlay R P s) = Arm.r f s := by
  cases f <;> unfold Arm.r <;> rfl

@[simp] theorem program_overlay (s : Arm.ArmState) : (overlay R P s).program = s.program := rfl

open Classical in
theorem mem_overlay (s : Arm.ArmState) (a : BitVec 64) :
    (overlay R P s).mem a = if R a then P a else s.mem a := rfl

theorem mem_overlay_in {s : Arm.ArmState} {a : BitVec 64} (h : R a) : (overlay R P s).mem a = P a := by
  rw [mem_overlay]; exact if_pos h

theorem mem_overlay_out {s : Arm.ArmState} {a : BitVec 64} (h : ¬ R a) :
    (overlay R P s).mem a = s.mem a := by
  rw [mem_overlay]; exact if_neg h

/-- **With `R ⊆ F` the overlay is the same world modulo `F`.** -/
theorem sameWorld_overlay {F : BitVec 64 → Prop} (hR : ∀ a, R a → F a) (s : Arm.ArmState) :
    SameWorld F s (overlay R P s) :=
  ⟨fun f _ => (r_overlay f s).symm, fun a ha => (mem_overlay_out fun h => ha (hR a h)).symm, rfl⟩

/-- Overlays of two worlds equal modulo `F ⊇ R` are equal modulo `F`. -/
theorem SameWorld.overlay {F : BitVec 64 → Prop} (hR : ∀ a, R a → F a) {s t : Arm.ArmState}
    (h : SameWorld F s t) : SameWorld F (Backend.Proof.overlay R P s) (Backend.Proof.overlay R P t) :=
  ⟨fun f hf => by rw [r_overlay, r_overlay]; exact h.1 f hf,
    fun a ha => by
      rw [mem_overlay_out fun h' => ha (hR a h'), mem_overlay_out fun h' => ha (hR a h')]
      exact h.2.1 a ha,
    h.2.2⟩

/-- Two overlays agree on `R`. -/
theorem overlay_mem_eq (s t : Arm.ArmState) {a : BitVec 64} (h : R a) :
    (overlay R P s).mem a = (overlay R P t).mem a := by
  rw [mem_overlay_in h, mem_overlay_in h]

open Classical in
/-- **A state holding `P` at `R` is its own overlay.** -/
theorem overlay_eq_self {s : Arm.ArmState} (h : ∀ a, R a → s.mem a = P a) : overlay R P s = s := by
  have e : (fun a => if R a then P a else s.mem a) = s.mem := by
    funext a
    by_cases ha : R a
    · simp only [ha, ↓reduceIte, h a ha]
    · simp only [ha, ↓reduceIte]
  show { s with mem := fun a => if R a then P a else s.mem a } = s
  rw [e]

end

end Backend.Proof
