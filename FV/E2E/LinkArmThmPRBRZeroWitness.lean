import FV.E2E.LinkArmRetOkPRB
import FV.E2E.LinkSlotSysWitness

/-!
# Witnesses for depth `0` of `ThmPRBRL` (`LinkArmStage2Zero`, `LinkArmCountZero`,
`LinkArmRetOkZero`), and `RetOkPRB` at every depth (`LinkArmRetOkPRB`)

On the slotted test system `LinkSlotSysWitness.Lsl` (`NeedSlots`; no base externs):

* `baseRetOk_Lsl` (vacuous: no base extern), `retCount_Lsl` (`retCountB`, `native_decide`);
* `stage2PRB_zero_Lsl`, `countPRB_zero_Lsl`, `retOkPRB_zero_Lsl`, and **`thmPRBRL_zero_Lsl`**:
  `ThmPRBRL` at depth `0` with the budget `K`;
* `retOkPRB_Lsl`: `retOkPRB_of` at every depth (program callees `h`, `r` return);
* `keeps_leave_h`: `returned_keeps_leave` (the core of `countPRB_zero`) on the slotted leaf `h`:
  its bare run on `41` from the placed entry returns `41` and gives back the popped entry's
  oracle, which is the caller's advanced by `1` (`initState_leave_nextAdv`). (`f`'s own run does
  not return at depth `0`: its callees' runs never do.)
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof E2E.LinkCheck

theorem baseRetOk_Lsl : Lsl.BaseRetOk := by
  intro n G hG
  simp [Lsl, L0, LinkSys.std, LinkSys.withCrun, LinkSys.ofInput, ofRes, closedBase,
    Clif.Env.empty] at hG

theorem retCountB_all : Lsl.P.funcs.all (Lsl.retCountB ·) = true := by native_decide

theorem retCount_Lsl : ∀ g ∈ Lsl.P.funcs, Lsl.RetCount g := fun g hg =>
  Lsl.retCountB_sound (List.all_eq_true.mp retCountB_all g hg)

theorem stage2PRB_zero_Lsl : Lsl.Stage2PRB (fun M _ => Lsl.K M) 0 := Lsl.stage2PRB_zero Lsl_ok

theorem countPRB_zero_Lsl : Lsl.CountPRB (fun M _ => Lsl.K M) 0 := Lsl.countPRB_zero Lsl_ok

theorem retOkPRB_zero_Lsl : Lsl.RetOkPRB (fun M _ => Lsl.K M) 0 :=
  Lsl.retOkPRB_zero baseRetOk_Lsl retCount_Lsl

/-- **`ThmPRBRL` at depth `0` on the slotted test system.** -/
theorem thmPRBRL_zero_Lsl : Lsl.ThmPRBRL (fun M _ => Lsl.K M) 0 :=
  Lsl.thmPRBRL_zero_of Lsl_ok (Lsl.budget_K Lsl_ok) baseRetOk_Lsl retCount_Lsl

theorem retOkPRB_Lsl (M : Nat) : Lsl.RetOkPRB (fun M _ => Lsl.K M) M :=
  Lsl.retOkPRB_of Lsl_ok needSlots baseRetOk_Lsl retCount_Lsl M

/-- `h`'s entry on `41` from `memS iniT`. -/
def csH : Clif.State := match Clif.initState Lsl.P "h" [⟨.i64, 41#64⟩] (memS iniT) with
  | .ok cs => cs
  | _ => default

def runH : Clif.Outcome := Clif.runLoop Clif.Env.empty Lsl.P.bare 50 csH

def checkH : Bool :=
  (match Clif.initState Lsl.P "h" [⟨.i64, 41#64⟩] (memS iniT) with
    | .ok _ => true
    | _ => false) &&
  (match runH with
    | .returned [v] _ => v.bits.toNat == 41
    | _ => false)

theorem checkH_true : checkH = true := by native_decide

theorem initH : Clif.initState Lsl.P "h" [⟨.i64, 41#64⟩] (memS iniT) = .ok csH := by
  have h := checkH_true
  simp only [checkH, Bool.and_eq_true] at h
  have h1 := h.1
  unfold csH
  split at h1 <;> rename_i hi
  · rw [hi]
  · cases h1

/-- **`returned_keeps_leave` on the slotted leaf `h`.** -/
theorem keeps_leave_h : ∃ v m, Clif.runLoop Clif.Env.empty Lsl.P.bare 50 csH = .returned [v] m ∧
    v.bits.toNat = 41 ∧ Clif.NextAdv csH.mem.leave m 0 ∧ Clif.NextAdv (memS iniT) csH.mem.leave 1 := by
  have h := checkH_true
  simp only [checkH, Bool.and_eq_true] at h
  have h2 := h.2
  unfold runH at h2
  split at h2
  · rename_i v m hr
    obtain ⟨hmem, hname⟩ := Clif.Program.func?_some func?_h
    have hpf : Lsl.P.func? fH.name = some fH := by rw [hname]; exact func?_h
    have hE := clifEntry_initState hpf (by rw [hname]; exact initH)
    have hI : Clif.LInv (Lsl.P.only fH) csH := runInv_entry (by simp [Clif.Program.only]) hE
    have hPf : ∀ f ∈ (Lsl.P.only fH).funcs, Clif.LinkFree f := fun f hf => by
      simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact Lsl_ok.free _ hmem
    have hl := Lsl.initState_leave_nextAdv func?_h initH placeAtB_memS
    have hs : fH.slots.isEmpty = false := by simpa using fH_slots
    rw [hs] at hl
    exact ⟨v, m, hr, by simpa using h2,
      returned_keeps_leave hPf LinkPlaceBWitness.keeps_empty hI hE.callers hr, hl⟩
  · cases h2

end E2E.LinkSlotSysWitness
