module

public import FV.E2E.RelWPatch

@[expose] public section

/-!
# Witness for `relW_patchW`

A one-byte live allocation at `0x100`, uninitialised before the call and `7` after it: the
default world (related to the memory before) patched with the memory after is related to it
(`relW_patchW`) and holds `7` there.
-/

namespace E2E.RelWPatchWitness

open Backend Backend.Proof

def cm0 : Clif.Mem := { allocs := [{ base := 0x100, size := 1 }] }

def cm1 : Clif.Mem :=
  { allocs := [{ base := 0x100, size := 1 }], bytes := fun a => if a = 0x100 then some 7 else none }

def Γ0 : Rel := ⟨fun _ => False, fun _ => none, 0, 0⟩

/-- A world with no error. -/
def w1 : Arm.ArmState := Arm.w .ERR .None Arm.ArmState.default

theorem err_w1 : Arm.r .ERR w1 = .None := Arm.r_of_w_same

theorem relW_cm0 (f : Clif.Function) : RelW Γ0 f (spv w1) [] cm0 w1 := by
  refine ⟨⟨⟨fun a b _ hb => by simp [cm0] at hb, fun a n hv => ?_, rfl⟩,
    fun _ _ h => by simp at h, outRel_zero _ _ _⟩, rfl, err_w1⟩
  simp only [cm0, Clif.Mem.valid, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨by omega, fun _ _ h => h⟩

theorem patchW_applies (f : Clif.Function) :
    RelW Γ0 f (spv w1) [] cm1 (patchW cm1 w1) ∧ Arm.read_mem 0x100#64 (patchW cm1 w1) = 7 := by
  refine ⟨relW_patchW (relW_cm0 f) (fun a n h => h) rfl, ?_⟩
  simp [Arm.read_mem, Arm.read_store, patchW, cm1, Clif.Mem.valid, Clif.Alloc.contains]

end E2E.RelWPatchWitness
