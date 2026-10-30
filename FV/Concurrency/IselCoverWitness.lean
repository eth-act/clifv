import FV.Concurrency.IselCover
import FV.Concurrency.VCodeFrameWitness

/-!
# Non-vacuity of `IselCover` (T2h, #311)

* `runFoot_ldar0`: the run of the `ldar` of `VCodeThread.Witness` (8 bytes at `0x8000`, under
  `csem` without frame) steps with the precise footprint `cEvs` (`RunFoot`, the premise of
  `cover_of_not_runOut`);
* `addr_eq_cover8`: `addr_eq_of_cover` for the 8 bytes at `0x8000` covered by an event there;
* `cover_ldar`: `cover_of_not_runOut` for that run (without frame) and the byte `0x8000`: no
  footprint of the `ldar` avoids it (`not_runOut_ldar`: with the byte changed to `5`, the `ldar`
  loads `5` instead of `0`, `out_w0`, `out_wB`), so it lies in an event of the `ldar`.
-/

namespace Concurrency.IselCover.Witness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread VCodeThread.Witness
  VCodeAddr.Witness

theorem addr_eq_cover8 : (0x8000#64 : BitVec 64) = BitVec.ofNat 64 0x8000 :=
  addr_eq_of_cover (n := 8) (by decide) (by decide) (by decide) fun k hk =>
    ⟨k, hk, by apply BitVec.eq_of_toNat_eq; simp⟩

/-- No frame. -/
abbrev F0 : BitVec 64 → Prop := fun _ => False

/-- `w0` with the byte at `0x8000` set to `5`. -/
def wB : ArmState := setMem (write_store 0x8000#64 5#8 w0.mem) w0

def t0 : ArmState :=
  (execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0)).getD w0

def tB : ArmState :=
  (execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] wB)).getD wB

theorem exec_t0 : execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0) =
    some t0 := by
  have h : (execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0)).isSome := by
    decide +kernel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  rw [ht]; simp only [t0, ht, Option.getD_some]

theorem exec_tB : execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] wB) =
    some tB := by
  have h : (execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] wB)).isSome := by
    decide +kernel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  rw [ht]; simp only [tB, ht, Option.getD_some]

theorem prog_eq {t w : ArmState}
    (h : @BEq.beq (List (BitVec 64 × BitVec 32)) _ t.program w.program = true) :
    t.program = w.program :=
  @eq_of_beq (List (BitVec 64 × BitVec 32)) _ _ _ _ h

/-- The `ldar` loads `0` from `w0`. -/
theorem out_w0 : (csem F0 ctx0 X0 iLdar [ofX 0x8000#64] w0).map (·.1) = some [ofX 0#64] := by
  rw [csem_of_wf (by decide) (by decide +kernel) (by decide +kernel)
    (by unfold Arm.CheckSPAlignment; decide +kernel),
    straightSem_eq ops0_eq ic0_eq (fun _ _ _ _ h => h) exec_t0 (by decide +kernel)
      (prog_eq (by decide +kernel))]
  simp only [Option.map_some, Option.some.injEq]
  decide +kernel

/-- The `ldar` loads `5` from `wB`. -/
theorem out_wB : (csem F0 ctx0 X0 iLdar [ofX 0x8000#64] wB).map (·.1) = some [ofX 5#64] := by
  rw [csem_of_wf (by decide) (by decide +kernel) (by decide +kernel)
    (by unfold Arm.CheckSPAlignment; decide +kernel),
    straightSem_eq ops0_eq ic0_eq (fun _ _ _ _ h => h) exec_tB (by decide +kernel)
      (prog_eq (by decide +kernel))]
  simp only [Option.map_some, Option.some.injEq]
  decide +kernel

theorem ifoot_ldar0 : IFoot (csem F0 ctx0 X0) iLdar [ofX 0x8000#64] w0
    (cEvs F0 ctx0 iLdar [ofX 0x8000#64] w0) :=
  ifoot_csem X0_tls (by decide +kernel) (fun _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ => ⟨by decide +kernel, by unfold Arm.CheckSPAlignment; decide +kernel⟩)

theorem runFoot_ldar0 : RunFoot (csem F0 ctx0 X0) (cEvs F0 ctx0) [iLdar] ρ0 w0 := by
  intro ops hops
  rw [ops0_eq] at hops
  cases hops
  rw [show vuses ops0 ρ0 = [ofX 0x8000#64] from uses0]
  exact ⟨ifoot_ldar0, fun _ _ _ => trivial⟩

/-- No footprint of the `ldar` avoids the byte `0x8000`. -/
theorem not_runOut_ldar : ¬ IselFoot.RunOut (csem F0 ctx0 X0) 0x8000#64 [iLdar] ρ0 w0 := by
  intro h
  obtain ⟨evs, hif, hout, -⟩ := h ops0 ops0_eq
  rw [show vuses ops0 ρ0 = [ofX 0x8000#64] from uses0] at hif
  have e := hif.2 _ (IselFoot.sagrees_out 5#8 hout hif.1)
  have e2 := congrArg (Option.map (·.1)) e
  rw [show setMem (write_store 0x8000#64 5#8 w0.mem) w0 = wB from rfl, out_wB, Option.map_map]
    at e2
  have e3 : (csem F0 ctx0 X0 iLdar [ofX 0x8000#64] w0).map
      ((·.1) ∘ fun r => (r.1, setMem (applyW evs (write_store 0x8000#64 5#8 w0.mem)) r.2.1, r.2.2)) =
      (csem F0 ctx0 X0 iLdar [ofX 0x8000#64] w0).map (·.1) := rfl
  rw [e3, out_w0] at e2
  simp only [Option.some.injEq, List.cons.injEq, and_true] at e2
  exact absurd e2 (by decide +kernel)

/-- **Non-vacuity of `cover_of_not_runOut`**: the byte `0x8000` lies in an event of the `ldar`. -/
theorem cover_ldar : ∃ j ρj wj i ops, RunAt (csem F0 ctx0 X0) [iLdar] ρ0 w0 j ρj wj ∧
    [iLdar][j]? = some i ∧ i.operands = .ok ops ∧
    ∃ e ∈ cEvs F0 ctx0 i (vuses ops ρj) wj, ∃ k < e.n, e.addr + BitVec.ofNat 64 k = 0x8000#64 :=
  cover_of_not_runOut runFoot_ldar0 not_runOut_ldar

end Concurrency.IselCover.Witness
