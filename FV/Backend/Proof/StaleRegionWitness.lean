import FV.Backend.Proof.StaleRegion

/-!
# Witnesses for `overlay` (`FV/Backend/Proof/StaleRegion.lean`)

The 16 bytes below `0x8000` overwritten by the byte `0xAB`: the overlay reads `0xAB` at `0x7FF8`,
keeps `0x8000`, is the same world modulo those bytes, and is idempotent (`overlay_eq_self`).
-/

namespace Backend.Proof.StaleRegionWitness

open Backend.Proof

/-- The 16 bytes below `0x8000`. -/
def R16 (a : BitVec 64) : Prop := 0x7FF0 ≤ a.toNat ∧ a.toNat < 0x8000

def PAB : BitVec 64 → BitVec 8 := fun _ => 0xAB

theorem read_in (s : Arm.ArmState) : (overlay R16 PAB s).mem 0x7FF8 = 0xAB :=
  mem_overlay_in (by unfold R16; decide)

theorem read_out (s : Arm.ArmState) : (overlay R16 PAB s).mem 0x8000 = s.mem 0x8000 :=
  mem_overlay_out (by unfold R16; decide)

theorem same_world (s : Arm.ArmState) : SameWorld R16 s (overlay R16 PAB s) :=
  sameWorld_overlay (fun _ h => h) s

/-- Overlaying twice is overlaying once: the overlay holds `PAB` at `R16`. -/
theorem idem (s : Arm.ArmState) : overlay R16 PAB (overlay R16 PAB s) = overlay R16 PAB s :=
  overlay_eq_self fun _ h => mem_overlay_in h

end Backend.Proof.StaleRegionWitness
