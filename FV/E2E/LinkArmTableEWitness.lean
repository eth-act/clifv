import FV.E2E.LinkArmTableE
import FV.E2E.LinkSlotSysWitness

/-!
# Witnesses for the prefix-closed machine table (`FV/E2E/LinkArmTableE.lean`, #700)

On the slotted system `LinkSlotSysWitness.Lsl`:

* `tabE_zero_Lsl`: the empty prefix has the prefix-closed table;
* `tableOfE_of_Lsl`: every `TableOf` of `Lsl` is a `TableOfE`;
* **`tableOfE_err_Lsl`**: a machine entry with an error has the prefix-closed table of every
  oracle, at every depth (`tableOfE_of_err`), for each of `Lsl`'s functions;
* `tabUpToE_of_Lsl`: the empty-prefix `TabUpTo` converts (`tabUpToE_of`).
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

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
