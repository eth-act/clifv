module

public import FV.Concurrency.CallSeg
public import FV.Concurrency.ThreadLayerWitness
public import FV.Concurrency.CallThreadWitness

@[expose] public section

/-!
# Non-vacuity of `xClosed_mon` on an LL/SC loop (T2h, #311, calls)

* `ldxAcq_of_words`: `LdxAcq` at every state holding a program whose words pass the check
  `wordLdxB` (no load exclusive without acquire or with base `sp`);
* `xClosed_llsc`: on the `ldaxr; add; stlxr; cbnz` loop of `ArmThread.Witness` (machine `stepi`),
  the precise run from the open monitor through the `ldaxr` (reading `5`), the `add` and the
  successful `stlxr` (a `relXW` event) is exclusive-closed by `xClosed_mon0`.

Checks by `native_decide` / `decide +kernel` (witness only).
-/

namespace Concurrency.CallSeg.WitnessX

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise ArmAllocThread ThreadRefine

/-- A word that does not decode to a load exclusive without acquire or with base `sp`. -/
def wordLdxB (w : BitVec 32) : Bool :=
  match decode_raw_inst w with
  | some (.LDST (.Reg_exclusive i)) =>
    !(decide (i.ord ≠ 1#1) && decide (i.L = 1#1)) || (decide (i.o0 = 1#1) && decide (i.Rn ≠ 31#5))
  | _ => true

/-- **`LdxAcq` from the program's words.** -/
theorem ldxAcq_of_words {π : Arm.Program} (h : π.all (fun q => wordLdxB q.2) = true) :
    ∀ s, s.program = π → LdxAcq s := by
  intro s hs a rn sz hc
  unfold cls at hc
  cases hd : decodeAt s with
  | none => rw [hd] at hc; cases hc
  | some ai =>
    rw [hd] at hc
    have hw : ∃ w, fetch_inst (r .PC s) s = some w ∧ decode_raw_inst w = some ai := by
      unfold decodeAt at hd
      split at hd
      · exact ⟨_, by assumption, hd⟩
      · cases hd
    obtain ⟨w, hf, hdw⟩ := hw
    rw [fetch_inst_from_program, hs] at hf
    obtain ⟨a', hmem⟩ := CallThread.Witness.find?_mem hf
    have hok := List.all_eq_true.mp h _ hmem
    simp only [wordLdxB, hdw] at hok
    cases ai with
    | LDST i =>
      cases i with
      | Reg_exclusive i =>
        simp only at hc
        split at hc
        · split at hc <;> cases hc
        · rename_i hord
          split at hc
          · rename_i hL
            simp only [Cls.ldx.injEq] at hc
            obtain ⟨rfl, rfl, -⟩ := hc
            simp only [hord, hL, ne_eq, not_false_eq_true, decide_true, Bool.and_self,
              Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hok
            exact ⟨by simpa using hok.1, hok.2⟩
          · cases hc
      | _ => cases hc
    | BR i =>
      cases i <;> simp only at hc
      all_goals (try split at hc) <;> (try split at hc) <;> cases hc
    | _ => cases hc

open ArmThread.Witness in
theorem stepEvs_s1 : stepEvs s1 = [] := by
  simp only [stepEvs, decode_s1]; split <;> rfl

open ArmThread.Witness in
theorem stepEvs_s2 : stepEvs s2 = [evWrite] := by
  have herr : read_err s2 = .None := by decide +kernel
  unfold stepEvs
  rw [decode_s2]
  dsimp only
  rw [if_pos herr]
  show exclEvs iStlxr s2 = _
  unfold exclEvs
  rw [if_neg (by simp [iStlxr]), if_neg (by simp [iStlxr])]
  rfl

open ArmThread.Witness in
/-- **The LL/SC loop's precise run** through the `ldaxr`, the `add` and the successful `stlxr`. -/
theorem run_llsc : PRun Policy.arm stepi (fun _ _ => True) (st 0x1000#64 0#64, none)
    [⟨[evRead], false⟩, ⟨[], false⟩, ⟨[evWrite], false⟩] (stepi s2, none) :=
  .cons step_ldaxr (.inr ⟨ThreadLayerWitness.m5, (ThreadLayerWitness.stepEvs_setMem_ldaxr).1.symm⟩)
    trivial
    (.cons step_add (.inr ⟨s1.mem, by rw [setMem_self, stepEvs_s1]⟩) trivial
      (.cons retry_succ (.inr ⟨s2.mem, by rw [setMem_self, stepEvs_s2]⟩) trivial .nil))

open ArmThread.Witness in
/-- **Non-vacuity of `xClosed_mon0`**: the run of the LL/SC loop with a successful `stlxr` (a
`relXW` event) is exclusive-closed. -/
theorem xClosed_llsc :
    CallCompose.XClosed (evTr [⟨[evRead], false⟩, ⟨[], false⟩, ⟨[evWrite], false⟩]) ∧
    ∃ b y, evAt (evTr [⟨[evRead], false⟩, ⟨[], false⟩, ⟨[evWrite], false⟩]) b = some y ∧
      y.k = .relXW := by
  have hπ : (st 0x1000#64 0#64).program = prog := by
    simp only [st, w_program]; rfl
  refine ⟨xClosed_mon0 (π := prog) (fun s h => (stepi_program s).trans h)
    (fun s _ h => by rw [stepi_err h]; exact h) (ldxAcq_of_words (by native_decide)) hπ run_llsc,
    (2, 0), evWrite, rfl, rfl⟩

end Concurrency.CallSeg.WitnessX
