import FV.E2E.LinkArm

/-!
# A world related to the CLIF memory after a call (SEM1 item (b), `docs/plans/uninit.md` §5.9)

The guarded call semantics (`ExtSem.guard`, `FV/E2E/ExtSemGuard.lean`) needs, at every VCode
call `(uses, w)` related to the CLIF memory `cm` of the invocation, *some* world related to the
CLIF memory `cm'` after it. `patchW cm' w` is `w` with the initialised bytes of `cm'`'s live
allocations written; it is related to `cm'` (`relW_patchW`) when `cm'` has no live allocation
`cm` lacks and the same symbols (a returning callee run keeps the allocations,
`runLoop_allocs`).
-/

namespace E2E

open Backend Backend.Proof

open Classical in
/-- **`w` with the initialised bytes of `cm`'s live allocations.** -/
noncomputable def patchW (cm : Clif.Mem) (w : Arm.ArmState) : Arm.ArmState :=
  setMem w fun a => match cm.bytes a.toNat with
    | some b => if cm.valid a.toNat 1 = true then b else w.mem a
    | none => w.mem a

theorem r_patchW (cm : Clif.Mem) (w : Arm.ArmState) (f : Arm.StateField) :
    Arm.r f (patchW cm w) = Arm.r f w := r_setMem f w _

@[simp] theorem program_patchW (cm : Clif.Mem) (w : Arm.ArmState) :
    (patchW cm w).program = w.program := rfl

theorem spv_patchW (cm : Clif.Mem) (w : Arm.ArmState) : spv (patchW cm w) = spv w := by
  simp only [spv, r_patchW]

/-- **The patched world is related to `cm'`**: `w` related to `cm`, `cm'`'s live allocations
are `cm`'s, and the symbols agree. -/
theorem relW_patchW {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {sl : List (Clif.SlotId × Nat)} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (h : RelW Γ f c sl cm w) (hv : ∀ a n, cm'.valid a n = true → cm.valid a n = true)
    (hsym : cm'.symbols = cm.symbols) : RelW Γ f c sl cm' (patchW cm' w) := by
  obtain ⟨⟨hmr, hsl, hout⟩, hsp, herr⟩ := h
  refine ⟨⟨⟨fun a b hva hb => ?_, fun a n hva => hmr.valid a n (hv a n hva),
    hsym.trans hmr.symbols⟩, ?_, ?_⟩, by rw [spv_patchW]; exact hsp, by rw [r_patchW]; exact herr⟩
  · have hlt : a < 2 ^ 64 := by
      have := (hmr.valid a 1 (hv a 1 hva)).1
      omega
    have e : (BitVec.ofNat 64 a).toNat = a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
    simp only [Arm.read_mem, Arm.read_store, patchW, mem_setMem, e, hb, hva, ↓reduceIte]
  · simp only [Rel.slotReg, spv_patchW]; exact hsl
  · obtain ⟨h1, h2, h3⟩ := hout
    refine ⟨h1, ?_, fun a n hva k hk j hj => ?_⟩
    · rw [spv_patchW]; exact h2
    · rw [spv_patchW]; exact h3 a n (hv a n hva) k hk j hj

end E2E
