import FV.E2E.DeadCleanupBinaryInitRU
import FV.E2E.LinkArmDetInduction

/-!
# `InitOkRU` from the scope conditions and three checks on the compiled code (SEM1 #537, #713)

**`InitOkRU.of_checks`**: the determinism fields of `InitOkRU` (`det`, `detTab`, `detTabR`, about
the linked system with its default callee runs `L.std`) follow from the determinism induction
(`LinkArmDetInduction.lean`: `detPRBRU_allK`, `detTabPRBE_allK`, `detTabPRBr_allK`) under
`NeedSlots`, given `L.Ok`, the budget, the scope conditions (`BaseRetOk`, `RetCount`,
`HooksKeep`), non-interference `NeedNI` with the trusted base-hook fact `BaseNIX` (of `L.std`,
whose machine entries the induction runs over), and the
decidable checks on every function's compiled code: `FnAsm.x30Free`, `VCode.retsLow`,
`FnAsm.blrLow`. No determinism premise is left.
-/

namespace E2E.DeadCleanupBinary
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck

/-- **`InitOkRU` from the scope conditions and the code checks** (module doc). -/
theorem InitOkRU.of_checks {L : LinkSys} {κ : Nat → Clif.Function → Nat} (hL : L.Ok)
    (hκ : L.Budget κ) (hNI : L.NeedSlots → L.NeedNI) (hNX : L.std.BaseNIX)
    (hB : L.NeedSlots → L.BaseRetOk) (hC : L.NeedSlots → ∀ g ∈ L.P.funcs, L.RetCount g)
    (hK : L.NeedSlots → L.HooksKeep)
    (hx30 : ∀ g ∈ L.P.funcs, ∀ lm, labelOffsets (L.A g).fa.lines = .ok lm →
      (L.A g).fa.x30Free lm = true)
    (hrl : ∀ g ∈ L.P.funcs, (L.A g).vc.retsLow = true)
    (hblr : ∀ g ∈ L.P.funcs, (L.A g).fa.blrLow = true) : InitOkRU L κ := by
  have hLs : L.std.Ok := hL.withCrun _
  haveI : L.std.CrunOk := L.crunOk_std hL
  refine ⟨hB, hC, fun hN M => ?_, fun hN M => ?_, fun hN M => ?_, hK⟩ <;>
  · have hKs : L.std.HooksKeep := ⟨(hK hN).err, (hK hN).tlsErr, (hK hN).prog, (hK hN).tlsProg⟩
    first
    | exact L.std.detPRBRU_allK hLs hκ hKs hN (hNI hN) hNX (hB hN) (hC hN) hx30 hrl hblr M
    | exact L.std.detTabPRBE_allK hLs hκ hKs hN (hNI hN) hNX (hB hN) (hC hN) hx30 hrl hblr M
    | exact L.std.detTabPRBr_allK hLs hκ hKs hN (hNI hN) hNX (hB hN) (hC hN) hx30 hrl hblr M

end E2E.DeadCleanupBinary
