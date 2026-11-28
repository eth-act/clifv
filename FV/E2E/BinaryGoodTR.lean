import FV.E2E.BinaryGoodT
import FV.E2E.LinkGoodTR
import FV.E2E.StackBoundTR

/-!
# `BinaryGoodT` for `LinkSys.OkTR` and `okBTSR` (#753, stage R4)

The declarations of `BinaryGoodT` on the paths from the typed Stock binary theorems to
`LinkSys.OkT`/`okBTS`, for the link contract with the register-guarded calls `LinkSys.OkTR` and
the checks `okBTSR` (suffix `R`).
-/
namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- `backend_correct_program_stack` with `RunGoodL` for a returning or trapping outcome. -/
theorem backend_correct_program_stackXTR (L : LinkSys) (hL : L.OkTR) {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ) {f : Clif.Function} (b : Nat) (hb : ∀ M, κ M f = b)
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s)
    (hroom : frameDrop (L.A f).af + b ≤ (spv s).toNat)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + b) (spv s) a)
    (hF : L.F = frameWG b (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s) := by
  have hd := L.frameDrop_eqTR hL hf
  have hres : StackAvail b (L.A f).af s := by
    refine ⟨?_, by rw [← hb M]; exact hκ.2 M f hf⟩
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budgetXTR L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav
    hrel hpl htr
namespace StackBound
open LinkCheck

end StackBound
namespace Binary
open LinkCheck

end Binary
end E2E
