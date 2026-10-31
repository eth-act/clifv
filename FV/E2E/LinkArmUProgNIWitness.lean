import FV.E2E.LinkArmUProgNI
import FV.E2E.NonVacuityLink

/-!
# Non-vacuity of the whole-program theorem with unwinding and non-interference (S10f, #233)

`E2E.LinkWitness.L` (`FV/E2E/NonVacuityLink.lean`: 18 compiled functions with slots, an
outgoing-argument area, indirect calls, a `try_call`; its linking needs non-interference and slot
placement: `NeedNI`, `NeedSlots`) lifted to a linked program with unwinding whose base callees do
not raise (`Ub`, `XRb` none; the base with unwinding `Clif.Env.empty.toX`): every premise of
`backend_correct_program_budgetU'`/`_peakU'` but the entry state's holds — `Ok` (`L_ok`), `OkU`
(the per-function unwinding checks `uChkN`, decided by `native_decide`), `OkUNI` (vacuous: no base
callee raises) — and the linking needs non-interference (`needNI`).
-/

namespace E2E.LinkArmUProgNIWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables LinkWitness

/-- `LinkWitness.L` with base callees that do not raise. -/
def LUN (F : BitVec 64 → Prop) : LinkSysU :=
  { L F with Ub := Unw.UnwHooks.none, envX := (L F).base.toX, XRb := XRaise.none }

/-- The per-function unwinding checks of the 18 functions. -/
def uChkN : Bool :=
  P.funcs.all fun g => let a := A g
    lowerCheckU g a.vc && (callSites a.af a.fa).toBool && (unwindRows a.af a.fa).toBool &&
      padsNonzeroB a.af a.fa && lastCallsOk a.af a.fa && savedCheck a.vcp a.rf

theorem uChkN_true : uChkN = true := by native_decide

theorem ok_of_toBool {ε α : Type} {x : Except ε α} (h : x.toBool = true) : ∃ a, x = .ok a := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl⟩

theorem ufacts {F : BitVec 64 → Prop} {g : Clif.Function} (hg : g ∈ (LUN F).P.funcs) :
    lowerCheckU g ((LUN F).A g).vc = true ∧
    (∃ lsda, callSites ((LUN F).A g).af ((LUN F).A g).fa = .ok lsda) ∧
    (∃ rows, unwindRows ((LUN F).A g).af ((LUN F).A g).fa = .ok rows) ∧
    padsNonzeroB ((LUN F).A g).af ((LUN F).A g).fa = true ∧
    lastCallsOk ((LUN F).A g).af ((LUN F).A g).fa = true ∧
    savedCheck ((LUN F).A g).vcp ((LUN F).A g).rf = true := by
  have h := uChkN_true
  simp only [uChkN, List.all_eq_true] at h
  have hc := h g hg
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, ok_of_toBool h2, ok_of_toBool h3, h4, h5, h6⟩

/-- **`LinkSys.Ok` holds** (`LinkWitness.L_ok`). -/
theorem LUN_ok (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) : (LUN F).Ok := L_ok F hF

/-- **`LinkSysU.OkU` holds**: the per-function unwinding checks; no base callee raises. -/
theorem LUN_okU (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) : (LUN F).OkU where
  envX := Clif.Env.toX_toEnv _
  lowerU g hg := (ufacts hg).1
  sites g hg := (ufacts hg).2.1
  rows g hg := (ufacts hg).2.2.1
  pads g hg := (ufacts hg).2.2.2.1
  last g hg := (ufacts hg).2.2.2.2.1
  saved g hg := (ufacts hg).2.2.2.2.2
  indScopeX g hg hn := ((LUN_ok F hF).indScope g hg hn).toX
  baseXR g _ F' slotOff out c := by
    intro ext _ G sl cm w d uses args vals e m hG _ _ _ hu
    exact absurd hu (Clif.Env.toX_noUnwind _ _ _ hG vals cm e m)
  baseXRI g _ F' slotOff out c := by
    intro sig _ n G sl cm w u args vals e m hG _ _ _ _ hu
    exact absurd hu (Clif.Env.toX_noUnwind (L F).base n G hG vals cm e m)
  baseExcl _ _ _ _ _ := rfl
  baseRaiseExt _ _ _ _ _ _ h := by cases h
  baseUnw g _ info _ _ i _ F' K G s0 Pc := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    cases h
  baseNoRaise := by intros; rfl
  baseKeepsPlaceU _ n G hG vals m e m' hu :=
    absurd hu (Clif.Env.toX_noUnwind _ _ _ hG vals m e m')
  baseKeepsAllocsU _ n G hG := by
    simp [LUN, L, Clif.Env.toX, Clif.Env.empty] at hG

/-- **The base raises' non-interference holds** (vacuously: no base callee raises). -/
theorem LUN_okUNI (F : BitVec 64 → Prop) : (LUN F).OkUNI where
  baseRaiseNI := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx
    cases hx

/-- **The linking needs non-interference** (`LinkWitness.backend_correct_program_witness`: the
callee `u` has an outgoing-argument area, `t` a stack slot). -/
theorem needNI : (LUN F0).NeedNI := by
  have h := backend_correct_program_witness
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **`backend_correct_program_budgetU'` applies** to this system (with `NeedNI`): every premise
but the entry state's holds, so for every entry state of `f` the linked machine with unwinding
refines `f`'s whole-program run with unwinding. -/
theorem budgetU'_applies (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) :
    (LUN F).Ok ∧ (LUN F).OkU ∧ (LUN F).OkUNI ∧ (LUN F).Budget (fun M _ => (LUN F).K M) ∧
    fF ∈ (LUN F).P.funcs ∧
    ∀ (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
      AbiEntry ((LUN F).A fF).fb ((LUN F).A fF).base ra s →
      StackAvail ((LUN F).K M) ((LUN F).A fF).af s →
      (LUN F).F = frameWG ((LUN F).K M)
        (RAFrame.compute ((LUN F).A fF).vcp ((LUN F).A fF).rf).intBase
        (RAFrame.compute ((LUN F).A fF).vcp ((LUN F).A fF).rf).size ((LUN F).A fF).af
        (LUN F).Img s →
      (∀ a, (LUN F).Img a → ¬ StackBelow (frameDrop ((LUN F).A fF).af + (LUN F).K M) (spv s) a) →
      (∀ a, (LUN F).Img a → s.mem a = (LUN F).imgMem a) →
      BodyEntry ((LUN F).A fF).af s w₀ → ArgsIn fF.sig args s → ClifEntry fF args cs →
      StackArgsAvoid (LUN F).Img fF.sig args s →
      Rel.holds ⟨(LUN F).F, (LUN F).syms, ((LUN F).A fF).af.slotBase,
        (RAFrame.compute ((LUN F).A fF).vcp ((LUN F).A fF).rf).intBase⟩ fF cs.frame.slots
        cs.mem w₀ →
      ((LUN F).NeedSlots → (LUN F).PlaceAt cs.mem (spv w₀)) →
      TrapsExplicitX ((LUN F).stdX.envRX M fF) (LUN F).P.bare cs →
      ArmRefinesU ((LUN F).A fF).fb ((LUN F).A fF).base ra ((LUN F).machU M fF) s
        (Clif.runLoopX (LUN F).envX (LUN F).P (M + 1) cs.toX) := by
  have hL := LUN_ok F hF
  have hU := LUN_okU F hF
  have hκ : (LUN F).Budget (fun M _ => (LUN F).K M) := (LUN F).toLinkSys.budget_K hL
  have hfF : fF ∈ (LUN F).P.funcs := by simp [LUN, L, P]
  refine ⟨hL, hU, LUN_okUNI F, hκ, hfF, fun M ra s w₀ args cs hent hres hFe hgfree himg hbe
    hargs hcs hsav hrel hpl htr => ?_⟩
  exact backend_correct_program_budgetU' (LUN F) hL hU (LUN_okUNI F) hκ hfF M hent hres hFe
    hgfree himg hbe hargs hcs hsav hrel hpl htr

end E2E.LinkArmUProgNIWitness
