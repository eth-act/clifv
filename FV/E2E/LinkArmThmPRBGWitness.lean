module

public import FV.E2E.LinkArmIniOfWitness
public import FV.E2E.LinkArmProgramInitEX
public import FV.E2E.LinkArmIniOfCongr
public import FV.E2E.RegLevelCallStart
public import FV.E2E.RegLevelCorrectCWitness

@[expose] public section

/-!
# Witnesses: the per-state facts under the slot-byte oracle (SEM1 #537, executable level)

On the slotted system `Lsl = L0.std` (`LinkSlotSysWitness`: `f` calls `h`, `r` reads its slot):

* `thmPRBG_zero_Lsl`: `ThmPRBG` at depth `0` (no premise left);
* `thmPRBG_allC_Lsl`: `ThmPRBG` at every depth from `DetPRB`, `DetTabPRBE`, `DetTabPRBr`;
* `backend_correct_program_core_initEX_Lsl`, `backend_correct_program_initEX_L0`: the top-level
  statements with `Ok`, the budget, `BaseRetOk`, `RetCount`, `HooksKeep` discharged;
* `actualEntry_Lsl`, `ansDecode_Lsl`: the actual callee entry and the call decoding at `Lsl`;
* `iniOf_std_L0`: `iniOf_congr` for `L0.std` and `L0` (equal machines, `mach_std`);

and for `RegLevelCallStart`:

* `count_two`: two even states among the first `5` of the successor machine from `0`;
* `opCalls_le_one`, `countedRun0_any`: `RealizesCP0.countedRun` for the identity machine (every
  state counted, `opCalls` steps per segment: the first is the only one).
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`ThmPRBG` at depth `0` on the slotted system** (no premise left). -/
theorem thmPRBG_zero_Lsl : Lsl.ThmPRBG (fun M _ => Lsl.K M) 0 :=
  Lsl.thmPRBG_of Lsl_ok (Lsl.budget_K Lsl_ok) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun h => absurd h (Nat.lt_irrefl 0)) (retOkPRB_Lsl 0) (Lsl.stage2PRBZSE_zero Lsl_ok)
    (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0))

/-- **`ThmPRBG` at every depth on the slotted system** from the determinism premises. -/
theorem thmPRBG_allC_Lsl (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M)
    (hdtr : ∀ M, Lsl.DetTabPRBr (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBG (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBG_allC Lsl_ok (Lsl.budget_K Lsl_ok) needSlots baseRetOk_Lsl retCount_Lsl hdet hdt hdtr M

/-- **`backend_correct_program_core_initEX` on the slotted system** (`Ok`, budget, `BaseRetOk`,
`RetCount`, `HooksKeep` discharged; the determinism premises and the entry remain). -/
theorem backend_correct_program_core_initEX_Lsl
    (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M)
    (hdtr : ∀ M, Lsl.DetTabPRBr (fun M _ => Lsl.K M) M) :
    type_of% (@backend_correct_program_core_initEX Lsl Lsl_ok _ (fun M _ => Lsl.K M)
      (Lsl.budget_K Lsl_ok) baseRetOk_Lsl retCount_Lsl hdet hdt hdtr hooksKeep_Lsl) :=
  @backend_correct_program_core_initEX Lsl Lsl_ok _ (fun M _ => Lsl.K M) (Lsl.budget_K Lsl_ok)
    baseRetOk_Lsl retCount_Lsl hdet hdt hdtr hooksKeep_Lsl

/-- **`backend_correct_program_initEX` on the slotted system's base `L0`** (`Lsl = L0.std`). -/
theorem backend_correct_program_initEX_L0
    (hdet : ∀ M, L0.std.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, L0.std.DetTabPRBE (fun M _ => Lsl.K M) M)
    (hdtr : ∀ M, L0.std.DetTabPRBr (fun M _ => Lsl.K M) M) :
    type_of% (@backend_correct_program_initEX L0 L0_ok (fun M _ => Lsl.K M)
      (L0.budget_K L0_ok) baseRetOk_Lsl retCount_Lsl hdet hdt hdtr hooksKeep_L0) :=
  @backend_correct_program_initEX L0 L0_ok (fun M _ => Lsl.K M) (L0.budget_K L0_ok)
    baseRetOk_Lsl retCount_Lsl hdet hdt hdtr hooksKeep_L0

/-- `actualEntry` and `ansDecode` at the slotted system. -/
theorem actualEntry_Lsl {M : Nat} (hM : 0 < M) :
    type_of% (@LinkSys.actualEntry Lsl (fun M _ => Lsl.K M) Lsl_ok _ M hM) :=
  @LinkSys.actualEntry Lsl (fun M _ => Lsl.K M) Lsl_ok _ M hM

theorem ansDecode_Lsl : type_of% (@LinkSys.ansDecode Lsl (fun M _ => Lsl.K M) Lsl_ok) :=
  @LinkSys.ansDecode Lsl (fun M _ => Lsl.K M) Lsl_ok

/-- **The machine's own table of `L0.std` is `L0`'s** (`iniOf_congr`, equal machines). -/
theorem iniOf_std_L0 : L0.std.iniOf = L0.iniOf :=
  LinkSys.iniOf_congr rfl rfl rfl fun M g => L0.mach_std M g

end E2E.LinkSlotSysWitness

namespace Backend.Proof.RegLevelCallStartWitness

open Backend Backend.Proof E2E Backend.Proof.RegLevelCorrectCWitness

/-- Two even states (`0`, `2`) among the first `5` of the successor machine from `0`. -/
theorem count_two : 2 ≤ countIn (fun n : Nat => n % 2 = 0) Nat.succ 0 5 :=
  countIn_two_le (i := 2) rfl (by omega) (by omega) (by rw [iterN_succ_nat])

theorem opCalls_le_one {V W : Type} (vc : VCode) (c : MConf V W) : opCalls vc c ≤ 1 := by
  rcases Nat.lt_or_ge 0 (opCalls vc c) with h | h
  · obtain ⟨b, k, allocs, its, m, w, vb, i, rfl, hvb, hi, hc⟩ := opCalls_pos h
    simp [opCalls, hvb, hi, hc]
  · omega

/-- **`RealizesCP0.countedRun` for the identity machine** (every state counted, `opCalls` steps
per segment: at most one, the first). -/
theorem countedRun0_any (vc : VCode) (rf : RFunc) (sem : Nat → ISem CV Arm.ArmState) :
    Realizes vc rf (ISem.counted sem) ckeep (stepC (fun _ : Unit => True) id)
      (fun p c => True ∧ p.2 = c.world.2 ∧ ∃ i, p = iterN (stepC (fun _ : Unit => True) id) i ((), 0))
      (fun p => ∃ m, (fun (_ : Nat) (_ : Unit) => True) m p.1 ∧ (True → True)) :=
  RealizesCP0.countedRun (Q := fun _ _ => True) (T := fun _ _ => True) (P := fun _ _ => True)
    (fun _ _ c c' _ _ hs => ⟨opCalls vc c, c', hs, trivial, fun _ _ => trivial, countIn_true _ _ _,
      fun i hi _ => by have := opCalls_le_one vc c; omega⟩)
    fun _ => trivial

end Backend.Proof.RegLevelCallStartWitness
