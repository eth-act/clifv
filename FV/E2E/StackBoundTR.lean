import FV.E2E.StackBoundT
import FV.E2E.LinkArmTR

/-!
# `StackBoundT` for `LinkSys.OkTR` and `okBTSR` (#753, stage R4)

The declarations of `StackBoundT` on the paths from the typed Stock binary theorems to
`LinkSys.OkT`/`okBTS`, for the link contract with the register-guarded calls `LinkSys.OkTR` and
the checks `okBTSR` (suffix `R`).
-/
namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_program` with a fixed stack bound for the entry**: with a budget `κ`
(`LinkSys.Budget`) that is `b` at the entry function `f` at every depth, every run of every fuel
`M` refines, provided the entry `sp` has `frameDrop f + b` bytes below it (without wrapping)
holding no code of the program, and the addresses outside the world are that stack and the code
(`hF`). -/
theorem backend_correct_program_stackTR (L : LinkSys) (hL : L.OkTR) {κ : Nat → Clif.Function → Nat}
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
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  have hd := L.frameDrop_eqTR hL hf
  have hres : StackAvail b (L.A f).af s := by
    refine ⟨?_, by rw [← hb M]; exact hκ.2 M f hf⟩
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budgetTR L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel
    hpl htr
namespace LinkSys
end LinkSys
namespace StackBound
open LinkCheck

section
variable {fd : Array Nat} {succ : Array (List Nat)} {b₀ : Array (Option Nat)}
end

end StackBound
end E2E
