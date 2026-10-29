module

public import FV.E2E.LinkArmUProg
public import FV.E2E.LinkArmUIndNI

@[expose] public section

/-!
# The whole-program theorem with unwinding, with non-interference (S10f, #233)

`backend_correct_program_budgetU'`/`_peakU'`: `backend_correct_program_budgetU`/`_peakU`
(`FV/E2E/LinkArmUProg.lean`) without `¬ NeedNI`: program callees may have an outgoing-argument
area or a slot region; the base raises' non-interference (`LinkSysU.OkUNI`) is a premise
(vacuous without `NeedNI`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The whole-program theorem with unwinding for the runs of at most `M + 1` steps**
(`backend_correct_program_budget`'s counterpart): for a function `f` of a linked program with
unwinding whose premises hold (`Ok`, `OkU`, the base raises' non-interference `OkUNI`) and a stack
budget `κ`, the linked machine with
unwinding of depth `M` refines `f`'s whole-program run with unwinding of at most `M + 1` steps
(`ArmRefinesU`: a return is an ABI return with the results, a trap the trap site, an exception
leaving `f` an ABI return to the caller with the exception object in x0). -/
theorem backend_correct_program_budgetU' (L : LinkSysU) (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s
      (Clif.runLoopX L.envX L.P (M + 1) cs.toX) := by
  haveI := L.crunOkX_std hL fun g hg hn => hU.indScopeX g hg hn
  exact backend_correct_program_budgetU_of L hL hU hf M
    (L.stdX.thmUN hL (hU.withCrunX _) ⟨hNI.baseRaiseNI⟩ hκ M) hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr

/-- **The whole-program theorem with unwinding for the run's peak call depth**
(`backend_correct_program_peak`'s counterpart): the linked machine with
unwinding of depth `d`, the peak call depth of the whole-program run with unwinding
(`Clif.DepthLeX`), refines that run of fuel `F + 1`. -/
theorem backend_correct_program_peakU' (L : LinkSysU) (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLeX L.envX L.P d cs.toX)
    (htr : TrapsExplicitX ((L.peakX F).envRX d f) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU d f) s
      (Clif.runLoopX L.envX L.P (F + 1) cs.toX) := by
  haveI := L.crunOkX_peak hL (fun g hg hn => hU.indScopeX g hg hn) F
  exact backend_correct_program_peakU_of L hL hU hf F d
    ((L.peakX F).thmUN hL (hU.withCrunX _) ⟨hNI.baseRaiseNI⟩ hκ d) hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl hd htr

end E2E
