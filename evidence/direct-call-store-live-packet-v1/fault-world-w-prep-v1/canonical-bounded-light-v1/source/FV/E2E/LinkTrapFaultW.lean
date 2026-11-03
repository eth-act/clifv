import FV.E2E.LinkTrapCall
import FV.E2E.MemTrapStatement
import FV.E2E.LinkGoodBoundedW

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Fault-aware linked observations retain each activation's complete pre-fault W trace.
The access case does not assert that the optimistic model machine stops. -/
inductive LinkSys.TrapInFW (L : LinkSys) (mp : ArmFault.MemMap) :
    Nat → Clif.Function → Arm.ArmState → Clif.TrapCode → Prop
  | site {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {c : Clif.TrapCode} {n : Nat} :
      L.Stop M g s n →
      TrapAt (L.A g).fb (L.A g).base c (runX (L.mach M g) n s) →
      L.RunGoodLBW n M g s → L.TrapInFW mp M g s c
  | access {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {c : Clif.TrapCode} {n : Nat} :
      TrapAtF mp (L.A g).fb (L.A g).base c (runX (L.mach M g) n s) →
      L.RunGoodLBW n M g s → L.TrapInFW mp M g s c
  | base {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {c : Clif.TrapCode} {n : Nat} :
      L.Stop M g s n → L.BaseTrapCall g c (runX (L.mach M g) n s) →
      L.RunGoodLBW n M g s → L.TrapInFW mp M g s c
  | prog {M : Nat} {g h : Clif.Function} {s : Arm.ArmState} {c : Clif.TrapCode} {n : Nat} :
      L.Stop (M + 1) g s n → L.ProgCallAt g h (runX (L.mach (M + 1) g) n s) →
      L.ProgCallOk g h (runX (L.mach (M + 1) g) n s) →
      RaOk (L.A h) (Arm.r .PC (runX (L.mach (M + 1) g) n s)) →
      L.RunGoodLBW n (M + 1) g s →
      L.TrapInFW mp M h (enterAt (L.A h) (runX (L.mach (M + 1) g) n s)) c →
      L.TrapInFW mp (M + 1) g s c

namespace LinkSys
variable (L : LinkSys)

/-- A source premise remains separate from the old explicit-only TrapsD contract. -/
def ThmTFW (mp : ArmFault.MemMap)
    (D : Nat → Clif.Function → Clif.State → Prop)
    (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (tc : Clif.TrapCode),
    L.WorldEntry κ M g F vals cs w₀ → D M g cs →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .trapped tc →
    ∀ G ra s, L.MachEntry κ M g F G ra s w₀ → L.TrapInFW mp M g s tc

end LinkSys
end E2E
