module

public import FV.E2E.LinkArmTableECall
public import FV.E2E.LinkSlotSysWitness

@[expose] public section

/-!
# Witnesses for the prefix-closed machine table (`FV/E2E/LinkArmTableE.lean`, #700)

On the slotted system `LinkSlotSysWitness.Lsl`:

* `tabE_zero_Lsl`: the empty prefix has the prefix-closed table;
* `tableOfE_of_Lsl`: every `TableOf` of `Lsl` is a `TableOfE`;
* **`tableOfE_err_Lsl`**: a machine entry with an error has the prefix-closed table of every
  oracle, at every depth (`tableOfE_of_err`), for each of `Lsl`'s functions;
* `tabUpToE_of_Lsl`: the empty-prefix `TabUpTo` converts (`tabUpToE_of`);
* `callsTo_err_zero_Lsl`: at depth `0` a program call of `Lsl` always ends in an error
  (`callsTo_ret`: no `M'` with `0 = M' + 1`); `callsTo_ret_Lsl`: the instance at depth `M`;
* `tabUpToE_count_zero_Lsl`: two prefix-closed tables of the empty prefix agree;
  `tabUpToE_call_at_Lsl`: the instance of `tabUpToE_call_at`.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

theorem tabUpToE_count_zero_Lsl (M : Nat) (g : Clif.Function) (s : Arm.ArmState)
    (ini : Clif.SlotInit) {e : Nat} (h : Lsl.TabUpToE M g s ini.bytes ini.next 0 e) : e = 0 :=
  Lsl.tabUpToE_count (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) h (Lsl.tabUpToE_zero M g s ini.bytes ini.next)

theorem tabUpToE_call_at_Lsl :
    type_of% (@LinkSys.tabUpToE_call_at Lsl) :=
  @LinkSys.tabUpToE_call_at Lsl

theorem callsTo_err_zero_Lsl {g h : Clif.Function} {t : Arm.ArmState} (hc : Lsl.CallsTo g t h)
    (hpb : progBase t = (Lsl.A g).base) : Arm.r .ERR (Lsl.mach 0 g t) ≠ .None := fun herr => by
  obtain ⟨M', hM, -⟩ := Lsl.callsTo_ret hc hpb herr
  exact absurd hM (Nat.succ_ne_zero M').symm

theorem callsTo_ret_Lsl {M : Nat} {g h : Clif.Function} {t : Arm.ArmState}
    (hc : Lsl.CallsTo g t h) (hpb : progBase t = (Lsl.A g).base)
    (herr : Arm.r .ERR (Lsl.mach M g t) = .None) :
    ∃ M', M = M' + 1 ∧ ∃ N', RetOf (Lsl.A h) t (runX (Lsl.mach M' h) N' (enterAt (Lsl.A h) t)) ∧
      ∀ N'' < N', ¬ RetOf (Lsl.A h) t (runX (Lsl.mach M' h) N'' (enterAt (Lsl.A h) t)) :=
  Lsl.callsTo_ret hc hpb herr

theorem tabE_zero_Lsl (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (ini : Clif.SlotInit) :
    Lsl.TabUpToE M g s ini.bytes ini.next 0 0 :=
  Lsl.tabUpToE_zero M g s ini.bytes ini.next

theorem tableOfE_of_Lsl {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {ini : Clif.SlotInit}
    (h : Lsl.TableOf M g s ini) : Lsl.TableOfE M g s ini :=
  Lsl.tableOfE_of h

/-- The default state with an error. -/
def sErr : Arm.ArmState := Arm.w .ERR (.Other "x") Arm.ArmState.default

theorem sErr_err : Arm.r .ERR sErr ≠ .None := by
  simp [sErr, Arm.r_of_w_same]

/-- **An erroring entry of `r` has the prefix-closed table of `iniT` at every depth.** -/
theorem tableOfE_err_Lsl (M : Nat) : Lsl.TableOfE M fR sErr iniT :=
  Lsl.tableOfE_of_err sErr_err iniT

theorem tabUpToE_of_Lsl (M : Nat) (g : Clif.Function) (s : Arm.ArmState) :
    Lsl.TabUpToE M g s iniT.bytes iniT.next 0 0 :=
  Lsl.tabUpToE_of M g s iniT.bytes iniT.next 0 0 (Lsl.tabUpTo_zero M g s iniT.bytes iniT.next)

end E2E.LinkSlotSysWitness
