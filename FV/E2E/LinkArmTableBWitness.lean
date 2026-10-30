import FV.E2E.LinkArmTableB
import FV.E2E.LinkArmProphDetWitness

/-!
# Witnesses for the slot-byte statement layer (`FV/E2E/LinkArmTableB.lean`)

On `LinkArmProphDetWitness.Lu` (a program with a call): the empty prefix has a table at every
depth, and a shorter prefix of a table has one (`tabUpTo_zero`, `tabUpTo_mono`); the
`WorldEntryB → WorldEntry` reduction applies without slotted callees.
-/

namespace E2E.LinkArmTableBWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem tab_Lu (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (ini : Clif.SlotInit) :
    Lu.TabUpTo M g s ini.bytes ini.next 0 0 :=
  Lu.tabUpTo_zero M g s ini.bytes ini.next

theorem tab_mono_Lu (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (ini : Clif.SlotInit) :
    ∃ e, Lu.TabUpTo M g s ini.bytes ini.next 0 e :=
  Lu.tabUpTo_mono (tab_Lu M g s ini) (Nat.le_refl 0)

theorem worldEntryB_Lu {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {vals : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} {ini : Clif.SlotInit}
    (h : Lu.WorldEntryB (fun M _ => Lu.K M) M g F vals cs w₀ ini) (hN : ¬ Lu.NeedSlots) :
    Lu.WorldEntry (fun M _ => Lu.K M) M g F vals cs w₀ :=
  h.toWorldEntry Lu hN

end E2E.LinkArmTableBWitness
